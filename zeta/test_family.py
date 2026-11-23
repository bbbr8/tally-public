import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


ROOT = Path(__file__).resolve().parent
LANGUAGES = ('zeta', 'euler', 'gauss', 'riemann', 'mertens', 'hardy', 'siegel')


def run_cli(name, *args, cwd=ROOT):
    script = ROOT / name / f'{name}.py'
    return subprocess.run(
        [sys.executable, '-X', 'utf8', str(script), *map(str, args)],
        cwd=cwd, text=True, encoding='utf-8', capture_output=True, timeout=30,
    )


class FamilyTests(unittest.TestCase):
    def test_source_with_utf8_signature(self):
        with tempfile.TemporaryDirectory() as directory:
            for name in LANGUAGES:
                with self.subTest(name=name):
                    source = Path(directory) / f'example.{name}'
                    source.write_text('expect 2 + 3 == 5\n', encoding='utf-8-sig')
                    check = run_cli(name, 'check', source)
                    self.assertEqual(check.returncode, 0, check.stderr)
                    run = run_cli(name, 'run', source, '--json')
                    self.assertEqual(run.returncode, 0, run.stderr)
                    self.assertEqual(json.loads(run.stdout)['expects'], [1, 1])

    def test_dialect_check_reports_usage_and_syntax_errors(self):
        missing = run_cli('riemann', 'check')
        self.assertEqual(missing.returncode, 2)
        self.assertIn('usage: riemann check FILE', missing.stderr)
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / 'broken.riemann'
            source.write_text('let answer = )', encoding='utf-8')
            check = run_cli('riemann', 'check', source, '--json')
            self.assertEqual(check.returncode, 1)
            self.assertFalse(json.loads(check.stdout)['ok'])

    def test_renamed_launchers_run_namesake_examples(self):
        for name in LANGUAGES:
            with self.subTest(name=name):
                help_result = run_cli(name, '--help')
                self.assertEqual(help_result.returncode, 0, help_result.stderr)
                self.assertIn('Zeta language family', help_result.stdout)
                description = run_cli(name, 'describe', '--json')
                self.assertEqual(description.returncode, 0, description.stderr)
                metadata = json.loads(description.stdout)
                self.assertEqual(metadata['language'], name.title())
                self.assertEqual(metadata['family'], 'Zeta language family')

                example = ROOT / name / 'examples' / f'namesake.{name}'
                result = run_cli(name, 'run', example, '--json')
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                packet = json.loads(result.stdout)
                self.assertTrue(packet['ok'])
                passed, total = packet['expects']
                self.assertGreater(total, 0)
                self.assertEqual(passed, total)

    def test_parent_bridges_work_from_another_directory(self):
        with tempfile.TemporaryDirectory(prefix='zeta example ') as directory:
            example = Path(directory) / 'bridge.gauss'
            example.write_text(
                'expect parent_describe("Euler").language == "Euler"\n'
                'expect parent_example("Euler").ok\n'
                'expect parent_run("Euler", "expect len(primes_to(10)) == 4").ok\n',
                encoding='utf-8',
            )
            result = run_cli('gauss', 'run', example, '--json', cwd=directory)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(json.loads(result.stdout)['expects'], [3, 3])
