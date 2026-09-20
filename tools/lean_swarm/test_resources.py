"""Pure tests for the process-shared resource semaphore."""
import threading
import time
import unittest
from tempfile import TemporaryDirectory

from resources import slot


class ResourceSlotTests(unittest.TestCase):
    def test_global_limit_is_respected_by_independent_threads(self):
        with TemporaryDirectory() as directory:
            active = peak = 0
            lock = threading.Lock()
            failures = []

            def worker():
                nonlocal active, peak
                try:
                    with slot(directory, 'compiler', 2, timeout=3):
                        with lock:
                            active += 1
                            peak = max(peak, active)
                        time.sleep(.04)
                        with lock:
                            active -= 1
                except Exception as exc:
                    failures.append(exc)

            threads = [threading.Thread(target=worker) for _ in range(8)]
            for thread in threads:
                thread.start()
            for thread in threads:
                thread.join()
            self.assertEqual(failures, [])
            self.assertLessEqual(peak, 2)
            self.assertEqual(active, 0)

    def test_timeout_and_validation_are_fail_closed(self):
        with TemporaryDirectory() as directory:
            entered = threading.Event()
            release = threading.Event()

            def holder():
                with slot(directory, 'verifier', 1):
                    entered.set()
                    release.wait(2)

            thread = threading.Thread(target=holder)
            thread.start()
            self.assertTrue(entered.wait(1))
            with self.assertRaises(TimeoutError):
                with slot(directory, 'verifier', 1, timeout=.03):
                    pass
            release.set()
            thread.join()
            for resource, limit in [('../compiler', 1), ('compiler/', 1), ('compiler', 0),
                                    ('compiler', -1), ('compiler', 1.5)]:
                with self.subTest(resource=resource, limit=limit), self.assertRaises(ValueError):
                    with slot(directory, resource, limit):
                        pass


if __name__ == '__main__':
    unittest.main()
