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
