"""
Unit tests for Higher Inductive Types (HITs):
Interval, Circle, Suspension, and Torus.
"""

import unittest
from hott.identity import Refl, SymPath, concat, inverse
from hott.hit import (
    CellComplex,
    ProdType,
    ProdPair,
    ProdPath,
    pair_path,
    INTERVAL,
    IntervalPoint,
    IntervalSeg,
    INTERVAL_ZERO,
    INTERVAL_ONE,
    SEG,
    interval_rec,
    interval_rec_beta_seg,
    interval_is_contr,
    funext_from_interval,
    interval_cell_complex,
    S1,
    CircleBase,
    CircleLoop,
    BASE,
    LOOP,
    circle_rec,
    loop_power,
    circle_winding,
    circle_cell_complex,
    SuspensionType,
    SuspPoint,
    SuspMerid,
    susp_rec,
    BOOL_TYPE,
    BOOL_TRUE,
    BOOL_FALSE,
    SUSP_BOOL,
    susp_bool_to_s1,
    s1_to_susp_bool,
    susp_bool_equiv_s1,
    susp_bool_cell_complex,
    T2,
    TorusBase,
    TorusLoopP,
    TorusLoopQ,
    TorusSurf,
    TORUS_B,
    TORUS_P,
    TORUS_Q,
    TORUS_SURF,
    torus_rec,
    PROD_S1_S1,
    torus_to_prod,
    prod_to_torus,
    torus_equiv_circle_prod,
    torus_cell_complex,
)


class TestHigherInductiveTypes(unittest.TestCase):
    def test_interval_contractibility_and_funext(self):
        # 1. Endpoints and path constructor
        self.assertEqual(SEG.source, INTERVAL_ZERO)
        self.assertEqual(SEG.target, INTERVAL_ONE)
        self.assertEqual(SEG.A, INTERVAL)

        # 2. Recursor computation rules
        target_z = "PointA"
        target_o = "PointB"
        dummy_path = SymPath("s", INTERVAL, target_z, target_o)
        f_rec = interval_rec(INTERVAL, target_z, target_o, dummy_path)

        self.assertEqual(f_rec(INTERVAL_ZERO), target_z)
        self.assertEqual(f_rec(INTERVAL_ONE), target_o)
        beta_p = interval_rec_beta_seg(INTERVAL, target_z, target_o, dummy_path)
        self.assertEqual(beta_p, dummy_path)

        # 3. Contractibility witness
        contr_witness = interval_is_contr()
        self.assertEqual(contr_witness.A, INTERVAL)
        self.assertEqual(contr_witness.center, INTERVAL_ZERO)

        # Contraction on zero is refl_zero, on one is seg
        path_at_zero = contr_witness.contraction(INTERVAL_ZERO)
        path_at_one = contr_witness.contraction(INTERVAL_ONE)
        self.assertTrue(path_at_zero.is_refl())
        self.assertEqual(path_at_one, SEG)

        # 4. Function Extensionality from Interval
        def f(x):
            return x

        def g(x):
            return x

        def p_homotopy(x):
            return Refl("T", x)

        p_ext = funext_from_interval("T", lambda _: "T", f, g, p_homotopy)
        self.assertEqual(p_ext.source, f)
        self.assertEqual(p_ext.target, g)

    def test_circle_and_fundamental_group_winding(self):
        # 1. Base point and loop
        self.assertEqual(BASE.type, S1)
        self.assertEqual(LOOP.source, BASE)
        self.assertEqual(LOOP.target, BASE)

        # 2. Circle recursor
        target_val = 42
        loop_id = Refl("Nat", target_val)
        rec_fn = circle_rec("Nat", target_val, loop_id)
        self.assertEqual(rec_fn(BASE), target_val)

        # 3. Winding number of powers of loop
        self.assertEqual(circle_winding(Refl(S1, BASE)), 0)
        self.assertEqual(circle_winding(LOOP), 1)
        self.assertEqual(circle_winding(inverse(LOOP)), -1)

        p3 = loop_power(3)
        self.assertEqual(circle_winding(p3), 3)

        p_minus2 = loop_power(-2)
        self.assertEqual(circle_winding(p_minus2), -2)

        # Cancellation test: loop^2 . loop^-2 has winding 0
        p_cancel = concat(loop_power(2), loop_power(-2))
        self.assertEqual(circle_winding(p_cancel), 0)

        # Composition test: loop^3 . loop^4 has winding 7
        p_sum = concat(loop_power(3), loop_power(4))
        self.assertEqual(circle_winding(p_sum), 7)

    def test_suspension_equivalence(self):
        # 1. Poles and meridians
        north_pt = SuspPoint(SUSP_BOOL, "north")
        south_pt = SuspPoint(SUSP_BOOL, "south")
        merid_t = SuspMerid(SUSP_BOOL, BOOL_TRUE)
        merid_f = SuspMerid(SUSP_BOOL, BOOL_FALSE)

        self.assertEqual(merid_t.source, north_pt)
        self.assertEqual(merid_t.target, south_pt)
        self.assertEqual(merid_f.source, north_pt)
        self.assertEqual(merid_f.target, south_pt)

        # 2. Suspension recursor
        rec_s = susp_rec(
            BOOL_TYPE,
            "Target",
            "N_val",
            "S_val",
            lambda b: SymPath(f"m_{b}", "Target", "N_val", "S_val"),
        )
        self.assertEqual(rec_s(north_pt), "N_val")
        self.assertEqual(rec_s(south_pt), "S_val")

        # 3. Susp(Bool) to S1 equivalence
        equiv_witness = susp_bool_equiv_s1()
        self.assertEqual(equiv_witness.A, SUSP_BOOL)
        self.assertEqual(equiv_witness.B, S1)

        # Map north and south to circle base
        self.assertEqual(equiv_witness(north_pt), BASE)
        self.assertEqual(equiv_witness(south_pt), BASE)

        # Inverse maps circle base to north pole
        inv_fn = equiv_witness.inv
        self.assertEqual(inv_fn(BASE), north_pt)

        # Section and retraction homotopies
        sect_north = equiv_witness.is_equiv.eta(north_pt)
        self.assertTrue(sect_north.is_refl())

        sect_south = equiv_witness.is_equiv.eta(south_pt)
        self.assertEqual(sect_south, merid_f)

        retr_base = equiv_witness.is_equiv.eps(BASE)
        self.assertTrue(retr_base.is_refl())

    def test_torus_and_surface_commutativity(self):
        # 1. Torus constructors
        self.assertEqual(TORUS_B.type, T2)
        self.assertEqual(TORUS_P.source, TORUS_B)
        self.assertEqual(TORUS_P.target, TORUS_B)
        self.assertEqual(TORUS_Q.source, TORUS_B)
        self.assertEqual(TORUS_Q.target, TORUS_B)

        # 2. Torus 2-cell surf : p . q = q . p
        pq = concat(TORUS_P, TORUS_Q)
        qp = concat(TORUS_Q, TORUS_P)
        self.assertEqual(TORUS_SURF.source, pq)
        self.assertEqual(TORUS_SURF.target, qp)

        # 3. Torus recursor
        torus_fn = torus_rec("Tgt", "y0", Refl("Tgt", "y0"), Refl("Tgt", "y0"), Refl("Tgt", "y0"))
        self.assertEqual(torus_fn(TORUS_B), "y0")

        # 4. Product S1 * S1 and pair_path
        pair_loop_refl = pair_path(PROD_S1_S1, LOOP, Refl(S1, BASE))
        pair_refl_loop = pair_path(PROD_S1_S1, Refl(S1, BASE), LOOP)

        self.assertEqual(pair_loop_refl.source, ProdPair(BASE, BASE, PROD_S1_S1))
        self.assertEqual(pair_loop_refl.target, ProdPair(BASE, BASE, PROD_S1_S1))

        # 5. Torus to S1 * S1 equivalence
        torus_eqv = torus_equiv_circle_prod()
        self.assertEqual(torus_eqv.A, T2)
        self.assertEqual(torus_eqv.B, PROD_S1_S1)

        prod_pt = torus_to_prod(TORUS_B)
        self.assertEqual(prod_pt, ProdPair(BASE, BASE, PROD_S1_S1))

        torus_pt = prod_to_torus(prod_pt)
        self.assertEqual(torus_pt, TORUS_B)

        self.assertTrue(torus_eqv.is_equiv.eta(TORUS_B).is_refl())
        self.assertTrue(torus_eqv.is_equiv.eps(prod_pt).is_refl())

    def test_topological_cell_complexes(self):
        # 1. Interval complex
        ic = interval_cell_complex()
        self.assertEqual(ic.v_count, 2)
        self.assertEqual(ic.e_count, 1)
        self.assertEqual(ic.f_count, 0)
        self.assertEqual(ic.euler_characteristic(), 1)
        self.assertTrue(ic.is_contractible_cell_complex())
        self.assertEqual(ic.boundary_1("seg"), ("zero", "one"))

        # 2. Circle S1 complex
        cc = circle_cell_complex()
        self.assertEqual(cc.v_count, 1)
        self.assertEqual(cc.e_count, 1)
        self.assertEqual(cc.f_count, 0)
        self.assertEqual(cc.euler_characteristic(), 0)
        self.assertFalse(cc.is_contractible_cell_complex())
        self.assertEqual(cc.boundary_1("loop"), ("base", "base"))

        # 3. Susp(Bool) complex
        sc = susp_bool_cell_complex()
        self.assertEqual(sc.v_count, 2)
        self.assertEqual(sc.e_count, 2)
        self.assertEqual(sc.f_count, 0)
        self.assertEqual(sc.euler_characteristic(), 0)
        self.assertEqual(sc.boundary_1("merid_true"), ("north", "south"))
        self.assertEqual(sc.boundary_1("merid_false"), ("north", "south"))

        # 4. Torus T2 complex
        tc = torus_cell_complex()
        self.assertEqual(tc.v_count, 1)
        self.assertEqual(tc.e_count, 2)
        self.assertEqual(tc.f_count, 1)
        self.assertEqual(tc.euler_characteristic(), 0)  # 1 - 2 + 1 = 0
        self.assertEqual(tc.boundary_1("p"), ("b", "b"))
        self.assertEqual(tc.boundary_1("q"), ("b", "b"))


if __name__ == "__main__":
    unittest.main()
