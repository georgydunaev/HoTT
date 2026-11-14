"""
Unit tests for Homotopy Type Theory: Blakers-Massey Connectivity Theorem
and Freudenthal Suspension Theorem.
"""

import unittest
from hott.identity import HoTTType, Refl, SymPath, ConcatPath, InversePath
from hott.truncation import TruncIndex, MINUS_TWO, MINUS_ONE, ZERO, ONE
from hott.connectivity import (
    ConnectivityLevel,
    ConnectedType,
    ConnectedMap,
    fiber_connectivity_validator,
    LoopSpace,
    SuspensionFunctor,
    FreudenthalMap,
    BlakersMasseySquare,
    freudenthal_stable_range,
    stable_homotopy_group_sphere,
)


class TestConnectivity(unittest.TestCase):
    def test_connectivity_level_arithmetic(self):
        c_m2 = ConnectivityLevel(-2)
        self.assertTrue(c_m2.is_contractible())
        self.assertFalse(c_m2.is_inhabited())
        self.assertFalse(c_m2.is_path_connected())
        self.assertFalse(c_m2.is_simply_connected())

        c_0 = ConnectivityLevel(0)
        self.assertFalse(c_0.is_contractible())
        self.assertTrue(c_0.is_inhabited())
        self.assertTrue(c_0.is_path_connected())
        self.assertFalse(c_0.is_simply_connected())

        c_1 = ConnectivityLevel(1)
        self.assertTrue(c_1.is_simply_connected())

        # Successor and Predecessor
        self.assertEqual(c_0.succ().level, 1)
        self.assertEqual(c_0.pred().level, -1)
        self.assertEqual(c_m2.pred().level, -2)

        # Addition and Doubling
        c_2 = ConnectivityLevel(2)
        c_3 = ConnectivityLevel(3)
        self.assertEqual(c_2.add(c_3).level, 5)
        self.assertEqual(c_2.double().level, 4)
        self.assertEqual(c_m2.add(c_m2).level, -2)
        self.assertEqual(c_m2.double().level, -2)

        # Comparisons and conversions
        self.assertEqual(int(c_2), 2)
        self.assertTrue(c_0 < c_1)
        self.assertTrue(c_1 <= c_2)
        self.assertEqual(c_1, ConnectivityLevel(1))
        self.assertEqual(c_1, 1)
        self.assertIn("ConnectivityLevel(2)", repr(c_2))

        # TruncIndex conversion
        ti = c_2.to_trunc_index()
        self.assertIsInstance(ti, TruncIndex)
        self.assertEqual(ti.level, 2)

        # ValueError on level < -2
        with self.assertRaises(ValueError):
            ConnectivityLevel(-3)

    def test_connected_type_operations(self):
        # Type A: 1-connected
        A = ConnectedType("X", 1, basepoint="x0")
        self.assertEqual(A.name, "X")
        self.assertEqual(A.connectivity, 1)
        self.assertTrue(A.is_connected(0))
        self.assertTrue(A.is_connected(1))
        self.assertFalse(A.is_connected(2))
        self.assertTrue(A.is_inhabited())
        self.assertTrue(A.is_path_connected())
        self.assertTrue(A.is_simply_connected())

        # Truncation contractibility witness
        contr = A.truncation_contr()
        self.assertEqual(contr.center, "x0")
        p = contr.contraction("x0")
        self.assertTrue(p.is_refl())

        # Suspension: (n + 1)-connected
        susp_A = A.suspension()
        self.assertEqual(susp_A.connectivity, 2)
        self.assertEqual(susp_A.basepoint, "north_X")

        # Loop space: (n - 1)-connected
        loop_A = A.loop_space()
        self.assertEqual(loop_A.connectivity, 0)
        self.assertIsInstance(loop_A.basepoint, Refl)

        # Bounded at -2
        c_bot = ConnectedType("Bot", -2)
        loop_bot = c_bot.loop_space()
        self.assertEqual(loop_bot.connectivity, -2)

    def test_connected_map_and_fibers(self):
        A = ConnectedType("A", 1, basepoint="a0")
        B = ConnectedType("B", 1, basepoint="b0")

        f_map = ConnectedMap(
            name="f",
            dom=A,
            codom=B,
            connectivity=1,
            f=lambda x: f"f({x})",
        )
        self.assertTrue(f_map.is_connected(0))
        self.assertTrue(f_map.is_connected(1))
        self.assertFalse(f_map.is_connected(2))
        self.assertEqual(f_map("a0"), "f(a0)")

        # Homotopy fiber
        fib = f_map.fiber("b0")
        self.assertEqual(fib.connectivity, 1)
        self.assertIn("fib_f(b0)", fib.name)

        # Fiber connectivity validation
        self.assertTrue(f_map.validate_fiber_connectivity(["b0", "b1", "b2"]))
        self.assertTrue(fiber_connectivity_validator(f_map, ["b0", "b1"]))

    def test_loop_space_and_iterated(self):
        X = ConnectedType("X", 3, basepoint="pt")
        omega = LoopSpace(X)
        self.assertEqual(omega.connectivity, 2)
        self.assertEqual(omega.basepoint, "pt")
        self.assertIsInstance(omega.loop_base, Refl)

        # Iterated loop spaces
        omega_0 = omega.iterated(0)
        self.assertEqual(omega_0, omega)

        omega_2 = omega.iterated(2)
        self.assertEqual(omega_2.connectivity, 0)

        with self.assertRaises(ValueError):
            omega.iterated(-1)

        ct = omega.to_connected_type()
        self.assertEqual(ct.connectivity, 2)

    def test_suspension_functor(self):
        A = ConnectedType("S1", 0, basepoint="base")
        susp = SuspensionFunctor(A)
        self.assertEqual(susp.connectivity, 1)
        self.assertEqual(susp.north, "north_S1")
        self.assertEqual(susp.south, "south_S1")

        # Meridian path
        m = susp.merid("base")
        self.assertIsInstance(m, SymPath)
        self.assertEqual(m.source, "north_S1")
        self.assertEqual(m.target, "south_S1")

        ct = susp.to_connected_type()
        self.assertEqual(ct.connectivity, 1)

    def test_freudenthal_suspension_map(self):
        A = ConnectedType("S2", 1, basepoint="s0")
        sigma = FreudenthalMap(A)
        # S2 is 1-connected, sigma is 2*1 = 2-connected
        self.assertEqual(sigma.connectivity, 2)

        # Freudenthal map application: merid(a) . (merid(a0))^{-1}
        p = sigma.apply("s1")
        self.assertIsInstance(p, ConcatPath)
        self.assertIsInstance(p.p, SymPath)
        self.assertIsInstance(p.q, InversePath)

        # Basepoint preservation
        p_base = sigma.basepoint_preservation()
        self.assertIsInstance(p_base, ConcatPath)

        # Freudenthal stability range
        self.assertTrue(sigma.is_in_stable_range(0))
        self.assertTrue(sigma.is_in_stable_range(1))
        self.assertFalse(sigma.is_in_stable_range(2))
        self.assertEqual(sigma.stable_range(), (0, 1))

        conn_map = sigma.to_connected_map()
        self.assertEqual(conn_map.connectivity, 2)

    def test_blakers_massey_homotopy_excision(self):
        C = ConnectedType("C", 1)
        A = ConnectedType("A", 2)
        B = ConnectedType("B", 2)

        f = ConnectedMap("f", C, A, connectivity=2)
        g = ConnectedMap("g", C, B, connectivity=3)

        bm_square = BlakersMasseySquare(f, g)
        # Comparison map connectivity: n + m = 2 + 3 = 5
        self.assertEqual(bm_square.comparison_map_connectivity(), 5)
        self.assertTrue(bm_square.is_cartesian_up_to(5))
        self.assertFalse(bm_square.is_cartesian_up_to(6))

        # Comparison map
        kappa = bm_square.comparison_map()
        self.assertEqual(kappa.connectivity, 5)
        val = kappa("c0")
        self.assertEqual(val, ("f(c0)", "g(c0)", "glue(c0)"))

        # Suspension specialization recovers Freudenthal map
        sigma = bm_square.suspension_specialization()
        self.assertIsInstance(sigma, FreudenthalMap)
        self.assertEqual(sigma.connectivity, 2)

        # Domain mismatch raises ValueError
        C_alt = ConnectedType("C_alt", 1)
        g_bad = ConnectedMap("g_bad", C_alt, B, connectivity=3)
        with self.assertRaises(ValueError):
            BlakersMasseySquare(f, g_bad)

    def test_stable_homotopy_groups_of_spheres(self):
        # Range validation
        self.assertEqual(freudenthal_stable_range(1), (0, 0))
        self.assertEqual(freudenthal_stable_range(2), (0, 2))
        self.assertEqual(freudenthal_stable_range(3), (0, 4))
        self.assertEqual(freudenthal_stable_range(4), (0, 6))

        with self.assertRaises(ValueError):
            freudenthal_stable_range(0)

        # Lower homotopy groups vanish: pi_k(S^n) = 0 for k < n
        info_lower = stable_homotopy_group_sphere(1, 2)
        self.assertEqual(info_lower["group"], "0")
        self.assertEqual(info_lower["order"], 1)

        # Homotopy group on sphere itself: pi_n(S^n) = Z
        info_diag = stable_homotopy_group_sphere(2, 2)
        self.assertEqual(info_diag["group"], "Z")
        self.assertEqual(info_diag["order"], "infinity")

        # Stable 1-stem: pi_3(S^2) = Z (Hopf fibration), pi_{n+1}(S^n) = Z_2 for n >= 3
        info_s2_3 = stable_homotopy_group_sphere(3, 2)
        self.assertEqual(info_s2_3["group"], "Z")
        info_s3_4 = stable_homotopy_group_sphere(4, 3)
        self.assertEqual(info_s3_4["group"], "Z_2")
        self.assertEqual(info_s3_4["order"], 2)

        # Stable 2-stem: pi_4(S^2) = Z_2, pi_5(S^3) = Z_2
        info_s2_4 = stable_homotopy_group_sphere(4, 2)
        self.assertEqual(info_s2_4["group"], "Z_2")
        info_s3_5 = stable_homotopy_group_sphere(5, 3)
        self.assertEqual(info_s3_5["group"], "Z_2")

        # Stable 3-stem: pi_6(S^3) = Z_12, pi_7(S^4) = Z_24 + Z_2, pi_8(S^5) = Z_24
        info_s3_6 = stable_homotopy_group_sphere(6, 3)
        self.assertEqual(info_s3_6["group"], "Z_12")
        self.assertEqual(info_s3_6["order"], 12)

        info_s4_7 = stable_homotopy_group_sphere(7, 4)
        self.assertEqual(info_s4_7["group"], "Z_24 + Z_2")
        self.assertEqual(info_s4_7["order"], 48)

        info_s5_8 = stable_homotopy_group_sphere(8, 5)
        self.assertEqual(info_s5_8["group"], "Z_24")
        self.assertEqual(info_s5_8["order"], 24)

        # Parameter error checks
        with self.assertRaises(ValueError):
            stable_homotopy_group_sphere(1, 0)
        with self.assertRaises(ValueError):
            stable_homotopy_group_sphere(-1, 2)


if __name__ == "__main__":
    unittest.main()
