import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { spawnSync } from 'node:child_process';

// Local preflight for the maintained sources, not Palomar's full verifier.
// In a Git checkout, inspect every tracked Lean file, including unused files.
// This unversioned development workspace also has ignored local toolchains;
// the fallback scope is explicitly the maintained source directories below.
const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
let failures = 0;
function fail(message) { process.stderr.write(`error: ${message}\n`); failures++; }
function read(relative) { return fs.readFileSync(path.join(root, relative), 'utf8'); }
function lines(text) { return text.split('\n').length - Number(text.endsWith('\n')); }
function walk(relative) {
  return fs.readdirSync(path.join(root, relative), { withFileTypes: true }).flatMap(entry => {
    const name = path.join(relative, entry.name);
    if (entry.isSymbolicLink()) return entry.name.endsWith('.lean') ? [name] : [];
    return entry.isDirectory() ? walk(name) : entry.name.endsWith('.lean') ? [name] : [];
  });
}
const git = spawnSync('git', ['rev-parse', '--show-toplevel'], { cwd: root, encoding: 'utf8' });
let sourceFiles;
if (git.status === 0 && path.resolve(git.stdout.trim()) === root) {
  const listing = spawnSync('git', ['ls-files', '-z', '--', '*.lean'], { cwd: root, encoding: 'utf8' });
  if (listing.status !== 0) throw new Error('Cannot list tracked Lean sources');
  sourceFiles = listing.stdout.split('\0').filter(Boolean);
  process.stdout.write('Source scope: all Git-tracked Lean files.\n');
  if (!sourceFiles.includes('Challenge.lean') || !sourceFiles.includes('Solution.lean'))
    fail('Challenge.lean and Solution.lean must be tracked in the submission commit');
} else {
  sourceFiles = [...fs.readdirSync(root).filter(name => name.endsWith('.lean')),
    ...walk('PerfectPowers'), ...walk('scripts')];
  process.stdout.write('Source scope: maintained workspace files; tmp, output, and .lake are not submission sources.\n');
}
let largest = { name: '', lines: 0 };
for (const name of sourceFiles) {
  if (fs.lstatSync(path.join(root, name)).isSymbolicLink()) { fail(`${name}: symbolic link`); continue; }
  const text = read(name);
  // This project's convention is stricter than Palomar: module is first.
  if (!/^module(?:\r?\n|$)/.test(text)) fail(`${name}: module must be the first line`);
  const count = lines(text);
  if (count > 10000) fail(`${name}: ${count} physical lines exceeds 10000`);
  if (count > largest.lines) largest = { name, lines: count };
}
const challenge = read('Challenge.lean');
const challengeBytes = Buffer.byteLength(challenge, 'utf8');
if (lines(challenge) > 1000 || challengeBytes > 100 * 1024) fail('Challenge exceeds a hard size limit');
if (lines(challenge) > 300 || challengeBytes > 32 * 1024)
  process.stderr.write('warning: Challenge exceeds Palomar\'s preferred review size\n');
const imports = [...challenge.matchAll(/^(?:public )?import (\S+)/gm)].map(match => match[1]);
if (imports.some(name => !name.startsWith('Mathlib.'))) fail('Challenge directly imports a non-Mathlib module');
const solution = read('Solution.lean');
if (/^(?:public )?import Challenge(?:\s|$)/m.test(solution)) fail('Solution must not import Challenge');
if (/^\s*(sorry|admit)\s*$/m.test(solution)) fail('Solution contains a proof placeholder');
const config = JSON.parse(read('comparator.json'));
const required = ['challenge_module', 'solution_module', 'theorem_names', 'permitted_axioms'];
const allowed = new Set([...required, 'definition_names', 'enable_nanoda']);
for (const field of required) if (!(field in config)) fail(`Comparator is missing ${field}`);
for (const field of Object.keys(config)) if (!allowed.has(field)) fail(`Unsupported Comparator field ${field}`);
const moduleName = /^[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*$/;
for (const key of ['challenge_module', 'solution_module'])
  if (typeof config[key] !== 'string' || !moduleName.test(config[key])) fail(`Invalid ${key}`);
if (config.challenge_module === config.solution_module) fail('Challenge and Solution must be distinct modules');
if (!Array.isArray(config.theorem_names) || !config.theorem_names.length ||
    config.theorem_names.some(name => typeof name !== 'string' || !moduleName.test(name)))
  fail('Comparator must name the compared theorems');
if (!Array.isArray(config.permitted_axioms) ||
    config.permitted_axioms.some(name => !['propext', 'Quot.sound', 'Classical.choice'].includes(name)))
  fail('Comparator permits a nonstandard axiom');
if (config.definition_names?.length) fail('This specification must not have definition holes');
const toolchain = read('lean-toolchain').trim();
const mathlibToolchainPath = path.join(root, '.lake/packages/mathlib/lean-toolchain');
if (fs.existsSync(mathlibToolchainPath) && fs.readFileSync(mathlibToolchainPath, 'utf8').trim() !== toolchain)
  fail('Project and pinned Mathlib toolchains differ');
if (!fs.existsSync(path.join(root, 'lake-manifest.json'))) fail('Missing Lake manifest');
process.stdout.write(`${sourceFiles.length} Lean files; largest: ${largest.name} (${largest.lines} lines).\n`);
process.stdout.write(`Challenge: ${lines(challenge)} lines, ${challengeBytes} bytes; ${imports.length} Mathlib imports.\n`);
process.stdout.write(`Comparator: ${config.theorem_names?.length ?? 0} theorem targets; no definition holes.\n`);
process.stdout.write(failures ? `${failures} preflight failure(s).\n` : 'Source and Comparator preflight passed.\n');
process.exitCode = failures ? 1 : 0;
