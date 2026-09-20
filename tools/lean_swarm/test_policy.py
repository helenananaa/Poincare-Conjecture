"""Unit tests for the model and reasoning policy contract."""

from __future__ import annotations

import unittest

from policy import ALLOWED_EFFORTS, LUNA_MODEL, parse_limit, resolve_effort


class PolicyTests(unittest.TestCase):
    def test_exports_and_limit_sentinels(self) -> None:
        self.assertEqual(LUNA_MODEL, "gpt-5.6-luna")
        self.assertEqual(ALLOWED_EFFORTS, {"high", "xhigh", "max"})
        for value in (None, 0, "0", "none", "unlimited", "NONE"):
            self.assertEqual(parse_limit(value), 0)
        self.assertEqual(parse_limit(" 12 "), 12)
        self.assertEqual(parse_limit(2**63 - 1), 2**63 - 1)

    def test_limit_rejects_bool_negative_and_unsafe_values(self) -> None:
        for value in (True, False, -1, 2**63, 1.5, ""):
            with self.subTest(value=value), self.assertRaises(ValueError):
                parse_limit(value)

    def test_explicit_effort_wins(self) -> None:
        for effort in sorted(ALLOWED_EFFORTS):
            self.assertEqual(resolve_effort({"reasoning_effort": effort, "difficulty": "foundation"}), effort)

    def test_difficulty_defaults(self) -> None:
        self.assertEqual(resolve_effort({"difficulty": "integration"}), "high")
        self.assertEqual(resolve_effort({"difficulty": "proof"}), "xhigh")
        self.assertEqual(resolve_effort({"difficulty": "foundation"}), "max")

    def test_config_default_and_exact_model(self) -> None:
        self.assertEqual(resolve_effort({}, {"luna_reasoning_effort": "max", "luna_model": LUNA_MODEL}), "max")
        self.assertEqual(resolve_effort({}, {}), "high")
        with self.assertRaises(ValueError):
            resolve_effort({}, {"luna_model": "gpt-5.5"})

    def test_invalid_explicit_effort_fails_closed(self) -> None:
        for effort in ("low", "medium", "", None, True, 1):
            with self.subTest(effort=effort), self.assertRaises(ValueError):
                resolve_effort({"reasoning_effort": effort})

    def test_invalid_config_effort_does_not_lower_request(self) -> None:
        with self.assertRaises(ValueError):
            resolve_effort({}, {"luna_reasoning_effort": "low"})
        with self.assertRaises(ValueError):
            resolve_effort({"reasoning_effort": "invalid"}, {"luna_reasoning_effort": "high"})

    def test_grok_shape_is_still_resolvable_for_historical_cards(self) -> None:
        self.assertIn(resolve_effort({"model": "grok"}), ALLOWED_EFFORTS)


if __name__ == "__main__":
    unittest.main()
