"""Behavioral regressions for fail-closed source and endpoint verification."""
import importlib.util
import subprocess
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]


class VerificationGuards(unittest.TestCase):
    def test_source_policy_rejects_unused_holes_and_missing_module(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            subprocess.run(['git', 'init', '-q', directory], check=True)
            (root / 'Challenge.lean').write_text('module\nexample : True := by sorry\n')
            source = root / 'Unused.lean'
            source.write_text('module\n/- sorry /- axiom -/ native_decide -/\nexample : True := by trivial\n')
            command = ['python3', str(ROOT / 'scripts/check-source-policy.py')]
            self.assertEqual(subprocess.run(command, cwd=root, capture_output=True).returncode, 0)
            for text in ['module\nexample : True := by sorry\n',
                         'example : True := by trivial\n',
                         'module\naxiom hidden : True\n',
                         'module\nexample : True := by native_decide\n',
                         'module\n' + '\n' * 10000]:
                source.write_text(text)
                self.assertNotEqual(subprocess.run(command, cwd=root, capture_output=True).returncode, 0)

    def test_challenge_has_stricter_size_limits(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            subprocess.run(['git', 'init', '-q', directory], check=True)
            challenge = root / 'Challenge.lean'
            command = ['python3', str(ROOT / 'scripts/check-source-policy.py')]
            for text in ['module\nexample : True := by sorry\n' + '\n' * 999,
                         'module\n/- ' + 'x' * (100 * 1024) + ' -/\nexample : True := by sorry\n']:
                challenge.write_text(text)
                self.assertNotEqual(subprocess.run(command, cwd=root, capture_output=True).returncode, 0)

    def test_axiom_allowlist_and_complete_endpoint_coverage(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            endpoints, log = root / 'endpoints.txt', root / 'axioms.log'
            endpoints.write_text('A.theorem\nB.theorem\n')
            command = ['python3', str(ROOT / 'scripts/check-axiom-closure.py'), '--endpoints', str(endpoints), str(log)]
            valid = "'A.theorem' depends on axioms: [propext, Classical.choice, Quot.sound]\n'B.theorem' does not depend on any axioms\n"
            log.write_text(valid)
            self.assertEqual(subprocess.run(command, capture_output=True).returncode, 0)
            for text in ['', valid.splitlines()[0], valid.replace('Quot.sound', 'Hidden.axiom'),
                         valid.replace('B.theorem', 'C.theorem'), valid + 'X.lean:2: error: failed\n']:
                log.write_text(text)
                self.assertNotEqual(subprocess.run(command, capture_output=True).returncode, 0)

    def test_pin_guard_rejects_legacy_and_orphan_dependencies(self):
        import json
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'lean-toolchain').write_text('leanprover/lean4:test\n')
            mathlib = {'url': 'https://example.invalid/mathlib', 'revision': 'a' * 40}
            pins = {'lean_toolchain': 'leanprover/lean4:test', 'packages': {'mathlib': mathlib}}
            (root / 'dependency-pins.json').write_text(json.dumps(pins))
            lakefile = '[[require]]\nname = "mathlib"\ngit = "https://example.invalid/mathlib"\nrev = "' + 'a' * 40 + '"\n'
            (root / 'lakefile.toml').write_text(lakefile)
            package = {'name': 'mathlib', 'url': mathlib['url'], 'rev': mathlib['revision'], 'inputRev': mathlib['revision'], 'type': 'git'}
            (root / 'lake-manifest.json').write_text(json.dumps({'packages': [package]}))
            checkout = root / '.lake/packages/mathlib'
            checkout.mkdir(parents=True)
            (checkout / 'lake-manifest.json').write_text('{"packages": []}')
            command = ['python3', str(ROOT / 'scripts/check-pins.py')]
            self.assertEqual(subprocess.run(command, cwd=root, capture_output=True).returncode, 0)
            orphan = dict(package, name='stafford38Formal')
            (root / 'lake-manifest.json').write_text(json.dumps({'packages': [package, orphan]}))
            self.assertNotEqual(subprocess.run(command, cwd=root, capture_output=True).returncode, 0)
            pins['packages']['stafford38Formal'] = mathlib
            (root / 'dependency-pins.json').write_text(json.dumps(pins))
            (root / 'lakefile.toml').write_text(lakefile + lakefile.replace('name = "mathlib"', 'name = "stafford38Formal"'))
            self.assertNotEqual(subprocess.run(command, cwd=root, capture_output=True).returncode, 0)

    def test_release_evidence_rejects_source_drift_and_commit_mismatch(self):
        import hashlib
        import json
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            subprocess.run(['git', 'init', '-q', directory], check=True)
            names = ['Proof.lean', 'scripts/verify.sh', 'tests/Oracle.lean', '.github/workflows/verify.yml',
                     'lean-toolchain', 'lakefile.toml', 'lake-manifest.json', 'dependency-pins.json',
                     'comparator.json', 'LICENSE', 'NOTICE']
            for name in names:
                path = root / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text('original source\n')
            subprocess.run(['git', '-C', directory, 'add', '--', *names], check=True)
            evidence = root / 'evidence'
            evidence.mkdir()
            subprocess.run(['git', '-C', directory, '-c', 'user.name=Verifier', '-c', 'user.email=verifier@example.invalid',
                            '-c', 'commit.gpgsign=false', '-c', 'core.hooksPath=/dev/null', 'commit', '-qm', 'Checked fixture source'], check=True)
            revision = subprocess.check_output(['git', '-C', directory, 'rev-parse', 'HEAD'], text=True).strip()
            inventory = {'schema': 'symplectic-stafford-source-inventory/v1', 'source_commit': revision,
                         'files': {name: hashlib.sha256((root / name).read_bytes()).hexdigest() for name in names}}
            (evidence / 'source-inventory.json').write_text(json.dumps(inventory))
            phases = {}
            for phase in ['phase_i', 'phase_ii', 'palomar']:
                phases[phase] = {'status': 'verified', 'evidence': f'evidence/{phase}.json', 'required_checks': ['lean-build']}
                record = {'phase': phase, 'result': 'pass', 'source_commit': revision, 'checks': {'lean-build': 'pass'}}
                (evidence / f'{phase}.json').write_text(json.dumps(record))
            manifest = {'target': 'SS-all-original-affine', 'verification_source_commit': revision,
                        'phases': phases, 'publication': {'enabled': True, 'required_phases': list(phases)}}
            (root / 'release-gates.yaml').write_text(json.dumps(manifest))
            command = ['bash', str(ROOT / 'scripts/check-release-readiness.sh')]
            self.assertEqual(subprocess.run(command, cwd=root, capture_output=True).returncode, 0)
            (root / 'Proof.lean').write_text('changed source\n')
            result = subprocess.run(command, cwd=root, capture_output=True, text=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('source drift in Proof.lean', result.stdout)
            original_digest = inventory['files']['Proof.lean']
            inventory['files']['Proof.lean'] = hashlib.sha256((root / 'Proof.lean').read_bytes()).hexdigest()
            (evidence / 'source-inventory.json').write_text(json.dumps(inventory))
            result = subprocess.run(command, cwd=root, capture_output=True, text=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('digest differs from source_commit for Proof.lean', result.stdout)
            inventory['files']['Proof.lean'] = original_digest
            (evidence / 'source-inventory.json').write_text(json.dumps(inventory))
            (root / 'Proof.lean').write_text('original source\n')
            record['phase'], record['source_commit'] = 'phase_ii', 'b' * 40
            (evidence / 'phase_ii.json').write_text(json.dumps(record))
            result = subprocess.run(command, cwd=root, capture_output=True, text=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('phase_ii: evidence source_commit differs', result.stdout)

    def test_resource_guard_handles_dynamic_inodes_and_finite_exhaustion(self):
        import os
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'sitecustomize.py').write_text(
                'import os, shutil\n'
                'from types import SimpleNamespace\n'
                'from unittest.mock import patch\n'
                'patch("os.statvfs", return_value=SimpleNamespace(\n'
                '    f_files=int(os.environ["TEST_TOTAL_INODES"]),\n'
                '    f_favail=int(os.environ["TEST_FREE_INODES"]))).start()\n'
                'patch("shutil.disk_usage", return_value=SimpleNamespace(\n'
                '    free=int(os.environ["TEST_FREE_BYTES"]))).start()\n')
            for total, free, size, accepted in [
                (0, 0, 2**31, True),
                (20000, 10000, 2**31, True),
                (20000, 9999, 2**31, False),
                (20000, 0, 2**31, False),
                (0, 0, 2**30 - 1, False),
            ]:
                with self.subTest(total=total, free=free, size=size):
                    env = dict(os.environ, PYTHONPATH=directory,
                               TEST_TOTAL_INODES=str(total), TEST_FREE_INODES=str(free),
                               TEST_FREE_BYTES=str(size), MIN_FREE_BYTES=str(2**30),
                               MIN_FREE_INODES='10000')
                    result = subprocess.run(['bash', str(ROOT / 'scripts/check-resources.sh')],
                                            cwd=root, env=env, capture_output=True, text=True)
                    self.assertEqual(result.returncode == 0, accepted,
                                     result.stdout + result.stderr)

    def test_map_fingerprint_rejects_changed_source(self):
        spec = importlib.util.spec_from_file_location('paper_map_guard', ROOT / 'scripts/check-paper-lean-map.py')
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        import hashlib
        record = {'path': 'proof.lean', 'sha256': hashlib.sha256(b'original').hexdigest()}
        module.verify_hash(b'original', record)
        with self.assertRaises(SystemExit):
            module.verify_hash(b'changed', record)
        for path in ['../proof.lean', '/proof.lean', 'dir/../../proof.lean']:
            with self.assertRaises(SystemExit):
                module.safe_path(path)


if __name__ == '__main__':
    unittest.main()
