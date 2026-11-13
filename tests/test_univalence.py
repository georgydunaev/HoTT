"""
Unit tests for Voevodsky's Univalence Axiom and Function Extensionality
"""

import unittest
from hott.identity import HoTTType, IdType, Refl, SymPath
from hott.equivalence import equiv_refl, Homotopy
from hott.univalence import (
    Universe,
    UNIVERSE_0,
    id_to_eqv,
    UnivalenceAxiom,
    happly,
    FunctionExtensionality,
)


class TestUnivalence(unittest.TestCase):
    def setUp(self):
        self.U = UNIVERSE_0
        self.A = HoTTType("A")
        self.B = HoTTType("B")
        self.ua_axiom = UnivalenceAxiom(self.U)
        self.funext_deriver = FunctionExtensionality(self.ua_axiom)

    def test_id_to_eqv_refl(self):
        p_refl = Refl(self.U, self.A)
        eqv = id_to_eqv(self.A, self.A, p_refl)
        self.assertEqual(eqv.A, self.A)
        self.assertEqual(eqv.B, self.A)
        self.assertEqual(eqv("val"), "val")

    def test_univalence_axiom_and_ua(self):
        # Axiom provides isEquiv for idToEqv
        isequiv_witness = self.ua_axiom.is_equiv_id_to_eqv(self.A, self.A)
        self.assertIsNotNone(isequiv_witness)

        # Map ua from equivalence to path in universe
        e_refl = equiv_refl(self.A)
        p_ua = self.ua_axiom.ua(e_refl)
        self.assertTrue(p_ua.is_refl())

        # Computation rule idToEqv(ua(e)) = e
        rule1 = self.ua_axiom.id_to_eqv_ua(e_refl)
        self.assertTrue(rule1.is_refl())

        # Computation rule ua(idToEqv(p)) = p
        p_refl = Refl(self.U, self.A)
        rule2 = self.ua_axiom.ua_id_to_eqv(self.A, self.A, p_refl)
        self.assertTrue(rule2.is_refl())

    def test_naive_function_extensionality(self):
        f = lambda x: x
        g = lambda x: x
        H_map = lambda x: Refl(self.A, x)
        H = Homotopy(f, g, H_map, self.A, self.A)

        # Univalence implies f = g
        path_fg = self.funext_deriver.funext(f, g, H, self.A, self.A)
        self.assertTrue(path_fg.is_refl())

    def test_strong_function_extensionality(self):
        f = lambda x: x
        g = lambda x: x
        strong_eqv = self.funext_deriver.strong_funext(f, g, self.A, self.A)
        self.assertIsNotNone(strong_eqv)
        self.assertIsNotNone(strong_eqv.is_equiv)


if __name__ == "__main__":
    unittest.main()
