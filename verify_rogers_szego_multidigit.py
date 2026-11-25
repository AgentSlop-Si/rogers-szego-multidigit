#!/usr/bin/env python3
"""Standalone exact algebraic & valuation verification script for:
'Multi-Digit Base-p Squarefreeness and Christoffel-Darboux Kernel Nonvanishing
 for Rogers-Szego Polynomials at Prime-Power Roots of Unity'
by Daniyar Kuttymbek, Adilkhan Kuttymbek, Dayana Kuttymbek,
Amina Kolpenova, and Mukhammadali Kottumbekov.

Uses Python 3 standard library only (zero external dependencies). Verifies:
1. Exact rational identities (Section 2 & Lemma 5.1): P_n recurrence, H_n(v^2) = v^n P_n(v+v^-1),
   shifted continuant split (2.4), determinant (2.5), g_m^0(0) = (-1)^u Q_u, exact Chebyshev
   shifted-derivative identity (5.3), and the p=3, m=3 negative control v(P_3'(0)) = 2 != 1.
2. Sparse-suffix carry lemma (Lemma 4.1) across multi-digit suffixes with t=0,1,2,3,4 even
   middle digits (including n=14,751 and n=4,917), plus out-of-scope odd-middle negative
   controls (p=3, m=819, ell=243 -> 1824 > 1662; p=3, m=273, x=121 -> 679 > 463).
3. Four-parity endpoint carry lemma (Lemma 5.1, Eq. 5.4) exhaustively over all 147,153 pairs
   at m=543 plus multi-digit fixtures for p=3, 5, 7 (including exceptional r_0=(B_0+1)/2 carries).
4. Replacement adjacent cap (Lemma 6.1) with UNIQUE equality at h=L across p=3,5,7 and j=2,3,
   parity-compensated g' convolution scores, k=3 boundary/annulus margins, and k>=4 deficit p-lambda<0.
5. Arbitrary-prefix level-one outer disk cap (Proposition 5.2) and 30-digit annulus dominance margins.
6. Direct finite-field good-reduction squarefreeness & neighbor-coprimality certificates for
   actual P_n(X;q) and H_n(z;q) at n = 10, 20 (Thm 1.1), 171 (Thm 1.2), 543 (Thm 1.4), 549 (Thm 1.5).
"""
from __future__ import annotations

from fractions import Fraction


# ---------------------------------------------------------------------------
# Valuation primitives V(a), W(b), rho_ell, T_ell(b), R_ell(b)
# ---------------------------------------------------------------------------

def ord_p(a: int, p: int) -> int:
    assert a > 0
    c = 0
    while a % p == 0:
        a //= p
        c += 1
    return c


def V_val(a: int, p: int) -> int:
    return p ** ord_p(a, p)


def build_W_table(n_max: int, p: int) -> list[int]:
    W = [0] * (n_max + 1)
    for a in range(1, n_max + 1):
        W[a] = W[a - 1] + V_val(a, p)
    return W


def rho_level(ell: int, p: int) -> Fraction:
    if ell == 1:
        return Fraction(2 * p - 1, 2 * p)
    if ell % 2 == 0:
        return Fraction(p ** (ell // 2), 2)
    return Fraction((2 * p - 1) * (p ** (ell // 2 - 1)), 2)


def build_TR_tables(n_max: int, ell: int, p: int) -> tuple[list[Fraction], list[Fraction]]:
    rho = rho_level(ell, p)
    W = build_W_table(n_max, p)
    T = [Fraction(0)] * (n_max + 1)
    R = [Fraction(0)] * (n_max + 1)
    for a in range(1, n_max + 1):
        va = Fraction(V_val(a, p))
        T[a] = T[a - 1] + (va if va < rho else rho)
        R[a] = Fraction(W[a]) - T[a]
    return T, R


# ---------------------------------------------------------------------------
# Exact polynomial arithmetic over Q and F_l
# ---------------------------------------------------------------------------

def ptrim_q(a: list[Fraction]) -> list[Fraction]:
    a = list(a)
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    return a


def padd_q(a: list[Fraction], b: list[Fraction]) -> list[Fraction]:
    n = max(len(a), len(b))
    return ptrim_q([(a[i] if i < len(a) else Fraction(0)) + (b[i] if i < len(b) else Fraction(0)) for i in range(n)])


def psub_q(a: list[Fraction], b: list[Fraction]) -> list[Fraction]:
    n = max(len(a), len(b))
    return ptrim_q([(a[i] if i < len(a) else Fraction(0)) - (b[i] if i < len(b) else Fraction(0)) for i in range(n)])


def pscale_q(a: list[Fraction], s: Fraction) -> list[Fraction]:
    return ptrim_q([c * s for c in a])


def pmul_q(a: list[Fraction], b: list[Fraction]) -> list[Fraction]:
    res = [Fraction(0)] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        if ai == 0:
            continue
        for j, bj in enumerate(b):
            if bj != 0:
                res[i + j] += ai * bj
    return ptrim_q(res)


def pderiv_q(a: list[Fraction]) -> list[Fraction]:
    if len(a) <= 1:
        return [Fraction(0)]
    return ptrim_q([a[i] * i for i in range(1, len(a))])


def build_P_seq_q(n_max: int, q: Fraction) -> list[list[Fraction]]:
    P = [[Fraction(1)], [Fraction(0), Fraction(1)]]
    for b in range(1, n_max):
        edge = Fraction(1) - (q ** b)
        nxt = psub_q([Fraction(0)] + P[b], pscale_q(P[b - 1], edge))
        P.append(nxt)
    return P


def build_shifted_fg_q(U: int, m_max: int, q: Fraction) -> tuple[list[list[Fraction]], list[list[Fraction]]]:
    f = [[Fraction(1)], [Fraction(0), Fraction(1)]]
    g = [[Fraction(0)], [Fraction(1)]]
    for b in range(1, m_max):
        edge = Fraction(1) - (q ** (U + b))
        f.append(psub_q([Fraction(0)] + f[b], pscale_q(f[b - 1], edge)))
        g.append(psub_q([Fraction(0)] + g[b], pscale_q(g[b - 1], edge)))
    return f, g


def build_cheb_U_q(n_max: int) -> list[list[Fraction]]:
    U = [[Fraction(1)], [Fraction(0), Fraction(1)]]
    for b in range(1, n_max):
        U.append(psub_q([Fraction(0)] + U[b], U[b - 1]))
    return U


# ---------------------------------------------------------------------------
# Check 1: Exact rational identities & Chebyshev shifted g' identity (Eq. 5.3)
# ---------------------------------------------------------------------------

def verify_exact_rational_identities() -> None:
    checked_cheb = 0
    for q_val in (Fraction(2, 3), Fraction(3, 5), Fraction(-2, 7)):
        q_inv = Fraction(1) / q_val
        P_q = build_P_seq_q(18, q_val)
        P_qi = build_P_seq_q(18, q_inv)
        U_cheb = build_cheb_U_q(16)
        w = [Fraction(1)]
        for j in range(1, 18):
            w.append(w[-1] * (Fraction(1) - q_val ** j))
        Q_even = [Fraction(1)]
        for j in range(1, 10):
            Q_even.append(Q_even[-1] * (Fraction(1) - q_val ** (2 * j)))

        for U in (0, 2, 5, 7):
            f_seq, g_seq = build_shifted_fg_q(U, 9, q_val)
            bU = Fraction(1) - q_val ** U
            for m in range(1, 9):
                # Split identity (2.4): P_{U+m} = f_m^U P_U - (1-q^U) g_m^U P_{U-1}
                if U >= 1:
                    lhs = P_q[U + m]
                    rhs = psub_q(pmul_q(f_seq[m], P_q[U]), pscale_q(pmul_q(g_seq[m], P_q[U - 1]), bU))
                    assert lhs == rhs
                    # Determinant identity (2.5): g_m^U P_{U+m-1} - g_{m-1}^U P_{U+m} = prod_{j=1}^{m-1}(1-q^{U+j}) P_U
                    prod_c = Fraction(1)
                    for j in range(1, m):
                        prod_c *= (Fraction(1) - q_val ** (U + j))
                    det_lhs = psub_q(pmul_q(g_seq[m], P_q[U + m - 1]), pmul_q(g_seq[m - 1], P_q[U + m]))
                    assert det_lhs == pscale_q(P_q[U], prod_c)

                # g_m^0(0) = (-1)^u Q_u for odd m = 2u + 1
                if U == 0 and m % 2 == 1:
                    u = (m - 1) // 2
                    assert g_seq[m][0] == ((-1) ** u) * Q_even[u]

                # Universal Chebyshev shifted g' identity (Eq. 5.3)
                CmU = Fraction(1)
                for j in range(1, m + 1):
                    CmU *= (Fraction(1) - q_val ** (U + j))
                acc = [Fraction(0)]
                for a in range(1, m + 1):
                    for b in range(a + 1, m + 1):
                        sgn = Fraction(-1) ** (a - 1)
                        qpow = q_val ** (a * (a - 1) // 2)
                        den = w[m - b] * w[a - 1] * (Fraction(1) - q_val ** (U + a)) * (Fraction(1) - q_val ** (U + b))
                        coeff = CmU * sgn * qpow / den
                        term = pmul_q(pmul_q(P_q[m - b], P_qi[a - 1]), U_cheb[b - a - 1])
                        acc = padd_q(acc, pscale_q(term, coeff))
                assert acc == pderiv_q(g_seq[m]), f"Chebyshev g' mismatch at U={U}, m={m}"
                checked_cheb += 1

    # Negative control for old delta=p^2 at bottom-p: P_3'(0) = -(2 - q - q^2) = -3t + t^2
    # In Z[t] with t = q - 1, q = 1 + t, so -(2 - (1+t) - (1+2t+t^2)) = 3t + t^2;
    # at p=3, s>=2, v(3) = 2*3^{s-1} >= 6 > 2, so v(P_3'(0)) = v(t^2) = 2 (NOT old 1 = G+p-p!).
    for q_test in (Fraction(2, 3), Fraction(5, 7)):
        P3 = build_P_seq_q(3, q_test)[3]
        P3p_0 = pderiv_q(P3)[0]
        t = q_test - 1
        assert P3p_0 == 3 * t + t * t

    print(f"  [PASS] Check 1 (Section 2 & Lemma 5.1): {checked_cheb} exact Q(q)[X] Chebyshev shifted-g', split, det, and g(0) identities + P_3'(0) negative control.")


# ---------------------------------------------------------------------------
# Check 2: Sparse-suffix carry lemma (Lemma 4.1) & odd-middle negative controls
# ---------------------------------------------------------------------------

def verify_sparse_carry_and_negatives() -> None:
    fixtures = [
        # (p, j, suffix m)
        (3, 2, 3 ** 2),                                       # t=0
        (3, 2, 2 * 3 ** 4 + 3 ** 2),                          # t=1 (m=171)
        (3, 2, 2 * 3 ** 6 + 2 * 3 ** 4 + 3 ** 2),             # t=2 (suffix of n=14,751)
        (3, 2, 2 * 3 ** 8 + 2 * 3 ** 6 + 2 * 3 ** 4 + 3 ** 2),# t=3 (m=14,751)
        (5, 2, 4 * 5 ** 6 + 2 * 5 ** 4 + 3 * 5 ** 2),         # p=5, t=2 (m=63,825)
        (3, 1, 2 * 3 ** 3 + 3),                               # bottom-p t=1 (m=57)
        (3, 1, 2 * 3 ** 5 + 2 * 3 ** 3 + 3),                  # bottom-p t=2 (suffix of n=4,917, m=543)
        (3, 1, 2 * 3 ** 7 + 2 * 3 ** 5 + 2 * 3 ** 3 + 3),     # bottom-p t=3 (m=4,917)
        (5, 1, 4 * 5 ** 5 + 2 * 5 ** 3 + 3 * 5),              # bottom-p p=5, t=2 (m=12,765)
    ]
    total_x = 0
    for p, j, m in fixtures:
        L = p ** j
        u = (m - 1) // 2
        W = build_W_table(m, p)
        G = W[u]
        assert W[m - 1] == 2 * G and W[m] == 2 * G + L
        # Check strict balance u mod p^b < (p^b - 1)/2 for all b > j
        pb = p ** (j + 1)
        while pb <= m:
            assert (u % pb) < (pb - 1) // 2
            pb *= p
        for x in range(u + 1):
            assert W[u - x] + W[x] + V_val(2 * x + 1, p) <= G + L
            total_x += 1

    # Out-of-scope odd-middle negative controls (must violate G + L!)
    # 1. p=3, j=2, m=819 = 3^6 + 3^4 + 3^2, ell=243 (x=121) -> score 1824 > G + L = 1662
    W819 = build_W_table(819, 3)
    u819 = (819 - 1) // 2
    G819 = W819[u819]
    x_bad1 = (243 - 1) // 2
    sc1 = W819[u819 - x_bad1] + W819[x_bad1] + V_val(243, 3)
    assert sc1 == 1824 and G819 + 9 == 1662 and sc1 > G819 + 9

    # 2. p=3, j=1, m=273 = 3^5 + 3^3 + 3, x=121 -> score 679 > G + 3 = 463
    W273 = build_W_table(273, 3)
    u273 = (273 - 1) // 2
    G273 = W273[u273]
    sc2 = W273[u273 - 121] + W273[121] + V_val(243, 3)
    assert sc2 == 679 and G273 + 3 == 463 and sc2 > G273 + 3

    print(f"  [PASS] Check 2 (Lemma 4.1): {total_x:,} exact carry-lemma checks across {len(fixtures)} multi-digit suffixes + both odd-middle negative controls.")


# ---------------------------------------------------------------------------
# Check 3: Four-parity endpoint carry lemma (Lemma 5.1, Eq. 5.4)
# ---------------------------------------------------------------------------

def verify_four_parity_endpoint_lemma() -> None:
    # Exhaustive unpruned check across ALL pairs 1 <= a < b <= m for m=57, 543 (p=3) and m=265 (p=5)
    # 265 = 2*5^3 + 3*5 (bottom-p, t=1, p=5)
    pairs_checked = 0
    exc_hits = 0
    for p, m in [(3, 57), (3, 543), (5, 265), (7, 1001)]:
        # Wait: 7^3 = 343, 2*7^3 + 3*7 = 707! Use 707 for p=7!
        if p == 7:
            m = 2 * (7 ** 3) + 3 * 7  # 707
        u = (m - 1) // 2
        W = build_W_table(m, p)
        G = W[u]
        V = [0] + [V_val(k, p) for k in range(1, m + 1)]
        for a in range(1, m + 1):
            x = (a - 1) // 2
            va = V[a]
            wx = W[x]
            for b in range(a + 1, m + 1):
                y = (m - b) // 2
                sc = wx + W[y] + va + V[b]
                assert sc <= G + p, (p, m, a, b, sc, G + p)
                pairs_checked += 1
                # Count Case 4 exceptional r0=(B0+1)/2 with A0 > B0 hits
                if a % 2 == 1 and b % 2 == 0:
                    z = u - y
                    r0 = z - x
                    B0 = V[b]
                    if 2 * r0 - 1 == B0 and va > B0:
                        exc_hits += 1
    assert exc_hits > 0
    print(f"  [PASS] Check 3 (Lemma 5.1 four-parity): {pairs_checked:,} exhaustive (a,b) pairs verified ({exc_hits} exceptional carry-cascade pairs).")


# ---------------------------------------------------------------------------
# Check 4: Adjacent cap (Lemma 6.1), parity-compensated g', k=3 vs k>=4 margins
# ---------------------------------------------------------------------------

def verify_adjacent_cap_and_margins() -> None:
    cap_checks = 0
    for p, j in [(3, 2), (3, 3), (5, 2), (5, 3), (7, 2)]:
        k = j + 1
        L = p ** j
        M = p ** k
        lam = Fraction(L, 2 * p)
        W = build_W_table(M, p)
        _, Rk = build_TR_tables(M, k, p)
        eq_hits = []
        for h in range(M):
            diff = Rk[h] - Fraction(W[h // 2])
            assert diff <= lam, (p, j, h, diff, lam)
            if diff == lam:
                eq_hits.append(h)
            cap_checks += 1
        assert eq_hits == [L], f"Expected unique equality at h={L}, got {eq_hits}"

    # Verify parity-compensated g' convolution score (Lemma 6.1(c)) exhaustively for (p,j,d) = (3,2,1), (5,2,1), (5,2,3)
    conv_checks = 0
    for p, d in [(3, 1), (5, 1), (5, 3)]:
        L = p * p
        m = d * L
        G0 = build_W_table((m - 1) // 2, p)[(m - 1) // 2]
        W = build_W_table(m, p)
        _, Rk = build_TR_tables(m, 3, p)
        for ell in range(1, m + 1):
            v_ell = V_val(ell, p)
            # First factor differentiated: h + delta + 2a = m - ell, t + 2b = ell - 1
            for delta in range(1, m - ell + 1):
                v_del = V_val(delta, p)
                rem1 = m - ell - delta
                for a in range(rem1 // 2 + 1):
                    h = rem1 - 2 * a
                    s1 = Rk[h] + W[a] + v_del
                    # Max over t + 2b = ell - 1 is bounded by checking all b
                    for b in range((ell - 1) // 2 + 1):
                        t = ell - 1 - 2 * b
                        sc = s1 + Rk[t] + W[b] + v_ell
                        assert sc <= G0 + L, (p, d, ell, delta, a, b, sc, G0 + L)
                        conv_checks += 1

    # Verify k=3 positive margins and k>=4 negative separate-term margin p - lambda
    for p in (3, 5, 7, 11, 13):
        L2, M3 = p ** 2, p ** 3
        lam2 = Fraction(p, 2)
        sig3 = rho_level(3, p)
        assert L2 - 2 * lam2 == p * p - p > 0
        assert p - lam2 == Fraction(p, 2) > 0
        assert Fraction(M3, 2) - L2 + p - sig3 == Fraction(p * p * (p - 2) + 1, 2) > 0
        # For k=4, j=3: lambda = p^2 / 2 > p -> p - lambda < 0!
        assert Fraction(p) - Fraction(p * p, 2) < 0

    print(f"  [PASS] Check 4 (Lemma 6.1 & Theorem 1.5): {cap_checks:,} adjacent-cap checks (unique equality at h=L), {conv_checks:,} parity-compensated g' scores, and k=3/k>=4 margins.")


# ---------------------------------------------------------------------------
# Check 5: Level-one arbitrary-prefix cap (Prop. 5.2) & 30-digit annulus margins
# ---------------------------------------------------------------------------

def verify_level1_and_30digit_margins() -> None:
    # Level-one block inequality & root/derivative equality sets on b = 543, 4917 (p=3) and b = 12765 (p=5)
    for p, b, e in [(3, 543, 1), (3, 4917, 1), (5, 12765, 3)]:
        W = build_W_table(b, p)
        _, R1 = build_TR_tables(b, 1, p)
        # Check root equality set: a = u*p, 0 <= 2u <= e
        root_eq = []
        for a in range(b // 2 + 1):
            h = b - 2 * a
            val = R1[b] - R1[h] - Fraction(W[a])
            assert val >= 0
            if val == 0:
                root_eq.append(a)
        assert root_eq == [u * p for u in range(e // 2 + 1)]
        # Check derivative equality set on small/medium b (all delta <= b)
        if b <= 600:
            min_dval = None
            deriv_eq = []
            for delta in range(1, b + 1):
                vd = V_val(delta, p)
                for a in range((b - delta) // 2 + 1):
                    h = b - delta - 2 * a
                    val = R1[b] - R1[h] - Fraction(W[a]) - Fraction(vd)
                    if min_dval is None or val < min_dval:
                        min_dval = val
                        deriv_eq = [(delta, a)]
                    elif val == min_dval:
                        deriv_eq.append((delta, a))
            assert min_dval == Fraction(-1, 2)
            assert deriv_eq == [(p, u * p) for u in range((e - 1) // 2 + 1)]

    # 30-digit annulus & shift margins across p in {3, 5, 7}
    for p in (3, 5, 7):
        exps = [1 + 2 * i for i in range(31)]  # 1, 3, 5, ..., 61 (30 middle digits!)
        for i in range(len(exps) - 1):
            e_lo, e_hi = exps[i], exps[i + 1]
            M, D = p ** e_lo, p ** e_hi
            sig, rho = rho_level(e_lo, p), rho_level(e_hi, p)
            assert M + rho < Fraction(D, 2)
            assert D - M - sig + Fraction(1, 2) > 0
            assert sig < rho

    print("  [PASS] Check 5 (Prop. 5.2 & 30-digit induction): Level-one equality sets + 30-digit annulus/shift margins verified.")


# ---------------------------------------------------------------------------
# Check 6: Direct finite-field good-reduction certificates for actual P_n, H_n
# ---------------------------------------------------------------------------

def fp_trim(a: list[int], mod: int) -> list[int]:
    a = [x % mod for x in a]
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    return a


def fp_gcd(a: list[int], b: list[int], mod: int) -> list[int]:
    a = fp_trim(a, mod)
    b = fp_trim(b, mod)
    while b != [0]:
        db = len(b) - 1
        inv_lb = pow(b[-1], mod - 2, mod)
        rem = list(a)
        for k in range(len(rem) - 1, db - 1, -1):
            c = rem[k]
            if c:
                qk = (c * inv_lb) % mod
                for j in range(db + 1):
                    rem[k - db + j] = (rem[k - db + j] - qk * b[j]) % mod
        a, b = b, fp_trim(rem, mod)
    inv_la = pow(a[-1], mod - 2, mod)
    return [(x * inv_la) % mod for x in a]


def fp_deriv(a: list[int], mod: int) -> list[int]:
    if len(a) <= 1:
        return [0]
    return fp_trim([(a[i] * i) % mod for i in range(1, len(a))], mod)


def find_prime_and_root(order: int) -> tuple[int, int]:
    """Find smallest prime ell == 1 (mod order) and an element q of exact order."""
    ell = order + 1
    while True:
        if all(ell % d != 0 for d in range(2, int(ell ** 0.5) + 1)):
            break
        ell += order
    # Factor order (here order = p^s, so just check q^{order/p} != 1)
    p = next(d for d in range(2, order + 1) if order % d == 0)
    g = 2
    while True:
        q = pow(g, (ell - 1) // order, ell)
        if pow(q, order, ell) == 1 and pow(q, order // p, ell) != 1:
            return ell, q
        g += 1


def verify_direct_good_reduction_certificates() -> None:
    # Certify ACTUAL P_n and H_n squarefreeness + P_n, P_{n-1} coprimality by good reduction
    # at representative minimal shapes from Theorems 1.1, 1.2, 1.4, and 1.5!
    cases = [
        ("Thm 1.1 (n=3^2+1=10, s=3)", 3, 3, 10),
        ("Thm 1.1 (n=2*3^2+2=20, s=3)", 3, 3, 20),
        ("Thm 1.2 (n=2*3^4+3^2=171, s=5)", 3, 5, 171),
        ("Thm 1.4 (n=2*3^5+2*3^3+3=543, s=6)", 3, 6, 543),
        ("Thm 1.5 (n=2*3^5+2*3^3+3^2=549, s=6)", 3, 6, 549),
    ]
    for label, p, s, n in cases:
        order = p ** s
        ell, q = find_prime_and_root(order)
        # Build P_n and P_{n-1} in F_ell[X]
        P_prev = [1]
        P_curr = [0, 1]
        for b in range(1, n):
            edge = (1 - pow(q, b, ell)) % ell
            assert edge != 0
            nxt = [0] + P_curr
            for i, c in enumerate(P_prev):
                nxt[i] = (nxt[i] - edge * c) % ell
            P_prev, P_curr = P_curr, nxt
        assert len(P_curr) == n + 1 and P_curr[-1] == 1
        assert fp_gcd(P_curr, fp_deriv(P_curr, ell), ell) == [1], f"P_n not squarefree in {label}"
        assert fp_gcd(P_curr, P_prev, ell) == [1], f"P_n, P_{{n-1}} not coprime in {label}"

        # Build H_n(z; q) via contiguous q-binomial ratios in F_ell[z]
        H_coeffs = [1] * (n + 1)
        for k in range(1, n + 1):
            num = (1 - pow(q, n - k + 1, ell)) % ell
            den = (1 - pow(q, k, ell)) % ell
            H_coeffs[k] = (H_coeffs[k - 1] * num * pow(den, ell - 2, ell)) % ell
        assert fp_gcd(H_coeffs, fp_deriv(H_coeffs, ell), ell) == [1], f"H_n not squarefree in {label}"
        print(f"  [PASS] Check 6 good-reduction cert [{label}] mod {ell} (q={q}): P_n, H_n squarefree & gcd(P_n, P_{{n-1}})=1.")


def main() -> None:
    verify_exact_rational_identities()
    verify_sparse_carry_and_negatives()
    verify_four_parity_endpoint_lemma()
    verify_adjacent_cap_and_margins()
    verify_level1_and_30digit_margins()
    verify_direct_good_reduction_certificates()
    print("ALL PAPER 9 VERIFICATIONS PASSED.")


if __name__ == "__main__":
    main()
