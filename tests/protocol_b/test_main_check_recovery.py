"""Include the recovery suite in the ordinary offline gate CI run."""
from pathlib import Path
import sys
import unittest

HERE = Path(__file__).parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT/'.github/protocol_b_main'))
sys.path.insert(0, str(HERE/'main_checks'))


def load_tests(loader, tests, pattern):
    return unittest.TestLoader().discover(str(HERE/'main_checks'), pattern='test_*.py',
                                        top_level_dir=str(HERE/'main_checks'))
