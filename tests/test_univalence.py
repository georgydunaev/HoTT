"""
Unit tests for Voevodsky's Univalence Axiom, Function Extensionality,
and Propositional Extensionality.
"""

import unittest
from hott.identity import HoTTType, IdType, Refl, SymPath
from hott.equivalence import equiv_refl, Homotopy, IsContr, IsProp
from hott.univalence import (
    Universe,
    UNIVERSE_0,
    id_to_eqv,
    UnivalenceAxiom,
    eqtoequiv_is_equiv,
    happly,
    FunctionExtensionality,
    weak_funext,
    funext_dep,
    funext_nondep,
    prop_equiv_to_id,
    is_prop_equiv_is_id,
)


class TestUnivalence(unittest.TestCase):
    def setUp(self):
        self.U = UNIVERSE_0
        self.A = HoTTType("A")
        self.B = HoTTType("B")
        self.C = HoTTType("C")
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

    def test_eqtoequiv_is_equiv(self):
        # Consequence 1: Equivalence between paths and equivalences: (A = B) <~> (A <~> B)
        eqv_paths_equivs = self.ua_axiom.eqtoequiv_is_equiv(self.A, self.A)
        self.assertIsNotNone(eqv_paths_equivs)
        self.assertIsNotNone(eqv_paths_equivs.is_equiv)

        standalone_eqv = eqtoequiv_is_equiv(self.A, self.A, self.ua_axiom)
        self.assertIsNotNone(standalone_eqv)
        self.assertIsNotNone(standalone_eqv.is_equiv)

    def test_isequiv_postcompose(self):
        # Postcomposition with an equivalence is an equivalence
        e_refl = equiv_refl(self.A)
        post_eq = self.funext_deriver.isequiv_postcompose(self.C, e_refl)
        self.assertIsNotNone(post_eq)
        self.assertIsNotNone(post_eq.g)

    def test_weak_funext(self):
        # Consequence 2 component: Product of contractible types is contractible
        X = self.A
        P = lambda x: HoTTType(f"P({x})")
        is_contr_P = lambda x: IsContr(P(x), f"c_{x}", lambda y: Refl(P(x), f"c_{x}"))

        contr_pi = self.funext_deriver.weak_funext(X, P, is_contr_P)
        self.assertIsNotNone(contr_pi)
        self.assertIsNotNone(contr_pi.center)

        standalone_contr = weak_funext(X, P, is_contr_P, self.ua_axiom)
        self.assertIsNotNone(standalone_contr)

    def test_naive_function_extensionality(self):
        f = lambda x: x
        g = lambda x: x
        H_map = lambda x: Refl(self.A, x)
        H = Homotopy(f, g, H_map, self.A, self.A)

        # Univalence implies f = g
        path_fg = self.funext_deriver.funext(f, g, H, self.A, self.A)
        self.assertTrue(path_fg.is_refl())

    def test_dependent_function_extensionality(self):
        # Dependent function extensionality
        f = lambda x: x
        g = lambda x: x
        H_map = lambda x: Refl(self.A, x)
        H = Homotopy(f, g, H_map, self.A, self.A)

        p_dep = self.funext_deriver.funext_dep(f, g, H, self.A, self.A)
        self.assertTrue(p_dep.is_refl())

        p_dep_standalone = funext_dep(f, g, H, self.A, self.A, self.ua_axiom)
        self.assertTrue(p_dep_standalone.is_refl())

    def test_non_dependent_function_extensionality(self):
        f = lambda x: x
        g = lambda x: x
        H_map = lambda x: Refl(self.A, x)
        H = Homotopy(f, g, H_map, self.A, self.A)

        p_nondep = funext_nondep(f, g, H, self.A, self.A, self.ua_axiom)
        self.assertTrue(p_nondep.is_refl())

    def test_strong_function_extensionality(self):
        f = lambda x: x
        g = lambda x: x
        strong_eqv = self.funext_deriver.strong_funext(f, g, self.A, self.A)
        self.assertIsNotNone(strong_eqv)
        self.assertIsNotNone(strong_eqv.is_equiv)

    def test_propositional_extensionality(self):
        # Consequence 3: Equivalence of propositions is equality of propositions:
        # isProp A -> isProp B -> (A <-> B) -> (A = B)
        pA = IsProp(self.A, lambda x, y: Refl(self.A, x))
        pB = IsProp(self.B, lambda x, y: Refl(self.B, x))

        f = lambda a: f"b_from_{a}"
        g = lambda b: f"a_from_{b}"

        path_AB = prop_equiv_to_id(self.A, self.B, pA, pB, f, g, self.ua_axiom)
        self.assertIsNotNone(path_AB)
        self.assertEqual(path_AB.source, self.A)
        self.assertEqual(path_AB.target, self.B)

        path_iff = is_prop_equiv_is_id(self.A, self.B, pA, pB, (f, g), self.ua_axiom)
        self.assertIsNotNone(path_iff)
        self.assertEqual(path_iff.source, self.A)
        self.assertEqual(path_iff.target, self.B)


if __name__ == "__main__":
    unittest.main()
