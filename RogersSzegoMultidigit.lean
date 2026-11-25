/-
  RogersSzegoMultidigit.lean

  Zero-dependency Lean 4 formal verification companion to:
  "Multi-Digit Base-p Squarefreeness and Christoffel-Darboux Kernel Nonvanishing
   for Rogers-Szego Polynomials at Prime-Power Roots of Unity"
  by Daniyar Kuttymbek, Adilkhan Kuttymbek, Dayana Kuttymbek,
  Amina Kolpenova, and Mukhammadali Kottumbekov.

  Uses Lean 4 core (`Init`) only — no Mathlib or external dependencies required.
  Zero `sorry`, zero custom `axiom`, zero `native_decide`.
  Verify with: `lean RogersSzegoMultidigit.lean`

  Contents:
    Part 1: Symbolic universal theorems (zero `sorry`):
      - Eq. (2.8): Geometric legality bound n < 3 * p^r <= p^(r+1) <= p^s for all odd p >= 3
        and arbitrary-length separated base-p digit sums.
      - Theorems 1.2-1.4: Annulus dominance inequality M + rho < D/2 (scaled: 2M + 2rho < D)
        for all p >= 3 whenever M * p^2 <= D and rho * p < D.
      - Theorems 1.3-1.4: Boundary-gap positivity for both j >= 2 and bottom-p (j = 1).
      - Theorem 1.5 & Remark 6.2: Exact adjacent k=3, j=2 boundary and annulus gap positivity
        for ALL odd p >= 3, plus symbolic proof of the exact k >= 4 separate-margin deficit
        lambda > p for all j >= 3.
      - Eq. (5.2): Bottom-p high-order carry bracket negativity (p + p^b < b(p-1)p^(b-1) + p + 1)
        for all p >= 3 and b >= 2.
      - Section 1 / Eq. (1.2): Abstract consecutive-neighbor coprimality propagation for
        three-term recurrences P_0 = 1, P_1 = X, P_{b+1} = X P_b - c_b P_{b-1} with c_b != 0.
    Part 2: Pure-kernel exact finite verifications (`decide` / `decide +kernel`, zero `native_decide`):
      - Lemma 4.1: Exhaustive sparse-suffix carry inequality W(u-x) + W(x) + V(2x+1) <= G + L
        at p=3 for multi-digit j=2 (m=171) and bottom-p j=1 (m=57).
      - Lemma 6.1: Exhaustive replacement adjacent cap R_k(h) - W(h/2) <= L/(2p) with UNIQUE
        equality at h = L for (p,j) = (3,2) and (5,2).
      - Lemma 5.1: Exhaustive four-parity endpoint carry inequality W(x)+W(y)+V(a)+V(b) <= G+p
        over all 1,596 pairs 1 <= a < b <= 57 at p=3, m=57.
      - Negative controls: odd-middle m=273, x=121 (679 > 463) and m=819, ell=243 (1824 > 1662).
      - Direct F_109[X] good-reduction certificate at n = 2*3^2 + 2 = 20 (p=3, r=2, s=3):
        exact gcd(P_20, P_20') = 1, gcd(P_20, P_19) = 1, and gcd(H_20, H_20') = 1.
-/

namespace RogersSzegoMultidigit

/-! ## Part 1: Symbolic Universal Theorems -/

/-- Auxiliary geometric tail bound: any separated sum of digits `≤ p - 1`
    below `p^k` plus `c * p^k` (`c < p`) is strictly less than `p^(k + 1)`. -/
theorem separated_tail_lt_pow {p : Nat} :
    ∀ (k : Nat) (tail : Nat), tail < p ^ k →
      ∀ (c : Nat), c < p → c * p ^ k + tail < p ^ (k + 1) := by
  intro k tail htail c hc
  have h1 : (c + 1) * p ^ k ≤ p * p ^ k := Nat.mul_le_mul_right (p ^ k) (by omega)
  have h2 : c * p ^ k + p ^ k = (c + 1) * p ^ k := by
    rw [Nat.add_mul, Nat.one_mul]
  have h3 : p ^ (k + 1) = p * p ^ k := by
    rw [Nat.pow_succ, Nat.mul_comm]
  omega

/-- Eq. (2.8) (Legality bound): for `p ≥ 3`, `r < s`, and any `n < 3 * p^r`,
    we have `n < p^s` (ensuring every recurrence edge `1 - q^a` below `n` is nonzero). -/
theorem legal_degree_bound {p r s n : Nat} (hp : 3 ≤ p) (hrs : r < s) (hn : n < 3 * p ^ r) :
    n < p ^ s := by
  have h1 : 3 * p ^ r ≤ p * p ^ r := Nat.mul_le_mul_right (p ^ r) hp
  have h2 : p * p ^ r = p ^ (r + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
  have h3 : p ^ (r + 1) ≤ p ^ s := Nat.pow_le_pow_right (by omega) hrs
  omega

/-- Theorems 1.2-1.4 (Annulus dominance `M + rho < D/2`, scaled by 2):
    if `p ≥ 3`, `p^2 * M ≤ D`, and `p * rho < D` (so `2 * p * rho ≤ 2 * D - 1`),
    then `2 * M + 2 * rho < D`. -/
theorem annulus_dominance_margin {p D M twoRho : Nat}
    (hp : 3 ≤ p) (hM : p * p * M ≤ D) (hR : p * twoRho < 2 * D) :
    2 * M + twoRho < D := by
  have h9M : 9 * M ≤ p * p * M := Nat.mul_le_mul_right M (Nat.mul_le_mul hp hp)
  have h3R : 3 * twoRho ≤ p * twoRho := Nat.mul_le_mul_right twoRho hp
  omega

/-- Theorem 1.3 (Boundary gap positivity for `j ≥ 2`):
    if `p ≥ 3`, `p^2 ≤ L`, `p^2 * L ≤ D`, and `L ≤ delta`, then all boundary gaps
    `2*delta - L`, `delta - L + 1`, `delta - L + p`, and `D/2 - L + 1` are strictly positive. -/
theorem boundary_gaps_jge2 {p L D delta : Nat}
    (hp : 3 ≤ p) (hL : p * p ≤ L) (hD : p * p * L ≤ D) (hdel : L ≤ delta) :
    0 < 2 * delta - L ∧ 0 < delta - L + 1 ∧ 0 < delta - L + p ∧ 0 < D / 2 - L + 1 := by
  have h9L : 9 * L ≤ D := Nat.le_trans (Nat.mul_le_mul_right L (Nat.mul_le_mul hp hp)) hD
  have hLpos : 9 ≤ L := Nat.le_trans (Nat.mul_le_mul hp hp) hL
  refine ⟨by omega, by omega, by omega, by omega⟩

/-- Theorem 1.4 (Bottom-`p` boundary gap positivity):
    for odd `p ≥ 3`, `h = (p - 1) / 2`, and `p ≤ delta`, all three gaps
    `2*delta - p - h`, `delta - h`, `delta - h` are at least `h + 1 > 0`. -/
theorem boundary_gaps_bottom_p {p delta : Nat}
    (hp : 3 ≤ p) (hodd : p % 2 = 1) (hdel : p ≤ delta) :
    let h := (p - 1) / 2
    h + 1 ≤ 2 * delta - p - h ∧ h + 1 ≤ delta - h ∧ 0 < h + 1 := by
  dsimp only
  omega

/-- Theorem 1.5 (Adjacent `k = 3, j = 2` exact boundary and annulus gap positivity for ALL odd `p ≥ 3`):
    with `L = p^2`, `M = p^3`, `2*lambda = p`, `2*sigma = 2*p - 1`:
    (1) `L - 2*lambda = p^2 - p > 0`,
    (2) `2*p - 2*lambda = p > 0`,
    (3) `M - 2*L + 2*p - (2*p - 1) = p^3 - 2*p^2 + 1 = p^2*(p - 2) + 1 > 0`. -/
theorem adjacent_k3_gaps_positive {p : Nat} (hp : 3 ≤ p) :
    let L := p * p
    let M := p * p * p
    (0 < L - p) ∧
    (0 < 2 * p - p) ∧
    (M + 2 * p > 2 * L + (2 * p - 1)) := by
  dsimp only
  have hp2 : 3 * p ≤ p * p := Nat.mul_le_mul_right p hp
  have hp3 : 3 * (p * p) ≤ p * p * p := by
    have h := Nat.mul_le_mul_left (p * p) hp
    have hc : p * p * 3 = 3 * (p * p) := Nat.mul_comm _ _
    omega
  refine ⟨by omega, by omega, by omega⟩

/-- Remark 6.2 (Exact `k ≥ 4` separate-term deficit):
    for every `p ≥ 3` and `j ≥ 3`, `2 * lambda = p^(j - 1) ≥ p^2 > 2 * p`,
    so the separate boundary margin `p - lambda` is strictly negative for all `k ≥ 4`. -/
theorem adjacent_kge4_separate_deficit {p j : Nat} (hp : 3 ≤ p) (hj : 3 ≤ j) :
    2 * p < p ^ (j - 1) := by
  have h1 : p ^ 2 ≤ p ^ (j - 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have h2 : p ^ 2 = p * p := by rw [Nat.pow_succ, Nat.pow_one]
  have h3 : 3 * p ≤ p * p := Nat.mul_le_mul_right p hp
  omega

/-- Eq. (5.2) (Bottom-`p` high-order carry bracket negativity):
    for every `p ≥ 3` and `b ≥ 2`, `p + p^b < b * (p - 1) * p^(b - 1) + p + 1`
    (in fact `p + p^b ≤ b * (p - 1) * p^(b - 1)` already!). -/
theorem bottom_p_high_order_carry_neg {p b : Nat} (hp : 3 ≤ p) (hb : 2 ≤ b) :
    p + p ^ b ≤ b * (p - 1) * p ^ (b - 1) := by
  have hpow : p ^ b = p * p ^ (b - 1) := by
    have hsub : b = (b - 1) + 1 := by omega
    conv => lhs; rw [hsub]
    rw [Nat.pow_succ, Nat.mul_comm]
  have hpm1 : p ≤ p ^ (b - 1) := by
    have h1 : p ^ 1 ≤ p ^ (b - 1) := Nat.pow_le_pow_right (by omega) (by omega)
    simpa using h1
  have hcoef : p + 1 ≤ b * (p - 1) := by
    have h2 : 2 * (p - 1) ≤ b * (p - 1) := Nat.mul_le_mul_right (p - 1) hb
    omega
  have hmul : (p + 1) * p ^ (b - 1) ≤ b * (p - 1) * p ^ (b - 1) :=
    Nat.mul_le_mul_right (p ^ (b - 1)) hcoef
  rw [Nat.add_mul, Nat.one_mul] at hmul
  omega

/-- Section 1 / Eq. (1.2) (Abstract consecutive-neighbor coprimality propagation):
    For any field-like zero/nonzero predicate on a sequence `val : Nat → Int` with `val 0 = 1`
    and recurrence `val (k + 1) = X * val k - c k * val (k - 1)` where `c k ≠ 0` for `1 ≤ k < n`,
    if `val n = 0` and `val (n - 1) = 0`, we reach a contradiction (so `P_n` and `P_{n-1}` share no root). -/
theorem consecutive_coprimality_propagation
    (val c : Nat → Int) (X : Int)
    (h0 : val 0 = 1)
    (hrec : ∀ k, 1 ≤ k → val (k + 1) = X * val k - c k * val (k - 1))
    (hc : ∀ k, 1 ≤ k → c k ≠ 0) :
    ∀ n, 1 ≤ n → ¬ (val n = 0 ∧ val (n - 1) = 0) := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ m ih =>
    intro hm ⟨h1, h2⟩
    cases m with
    | zero =>
      simp only [Nat.succ_sub_one] at h2
      rw [h0] at h2
      omega
    | succ m' =>
      have hrec_m := hrec (m' + 1) (by omega)
      simp only [Nat.succ_sub_one] at h2 hrec_m
      rw [h1, h2] at hrec_m
      have hprod : c (m' + 1) * val m' = 0 := by omega
      have hcm := hc (m' + 1) (by omega)
      have hvm : val m' = 0 := by
        cases Int.mul_eq_zero.mp hprod with
        | inl hcz => exact absurd hcz hcm
        | inr hvz => exact hvz
      exact ih (by omega) ⟨h2, hvm⟩

/-! ## Part 2: Pure-Kernel Exact Finite Verifications (`decide +kernel`) -/

/-- Exact `p`-adic part `V_p(a) = p^(ord_p(a))` computed with structural fuel. -/
def vPartFuel (p : Nat) : Nat → Nat → Nat
  | 0, _ => 1
  | f + 1, a => if a > 0 && a % p == 0 then p * vPartFuel p f (a / p) else 1

def vPart (p a : Nat) : Nat := vPartFuel p 12 a

/-- Build array of `W_p(0), W_p(1), ..., W_p(n)` as a `List Nat` (using Array for O(1) lookup). -/
def buildWArray (p n : Nat) : Array Nat :=
  (List.range n).foldl (fun arr idx =>
    let a := idx + 1
    let prev := arr.getD idx 0
    arr.push (prev + vPart p a)) #[0]

/-- Lemma 4.1 (Sparse-suffix carry inequality) verified exhaustively in Lean's kernel for:
    (1) `p = 3, j = 2, m = 2*3^4 + 3^2 = 171` (all `86` values `0 ≤ x ≤ 85`),
    (2) `p = 3, j = 1, m = 2*3^3 + 3 = 57` (all `29` values `0 ≤ x ≤ 28`). -/
def checkSparseCarry (p j m : Nat) : Bool :=
  let L := p ^ j
  let u := (m - 1) / 2
  let W := buildWArray p m
  let G := W.getD u 0
  (W.getD (m - 1) 0 == 2 * G) &&
  (W.getD m 0 == 2 * G + L) &&
  (List.range (u + 1)).all fun x =>
    W.getD (u - x) 0 + W.getD x 0 + vPart p (2 * x + 1) ≤ G + L

theorem sparse_carry_lemma_multi_digit_p3 :
    checkSparseCarry 3 2 171 = true ∧
    checkSparseCarry 3 1 57 = true := by
  decide +kernel

/-- Lemma 6.1 (Replacement adjacent cap `2 * (R_k(h) - W(h/2)) ≤ L / p` with UNIQUE equality at `h = L`,
    scaled by 2 to pure integer arithmetic for `k = 3, j = 2`, where `2 * rho_3 = 2*p - 1`). -/
def checkAdjacentCapK3 (p : Nat) : Bool :=
  let L := p * p
  let M := p * p * p
  let twoRho := 2 * p - 1
  let W := buildWArray p M
  -- Build array of 2 * T_3(h)
  let twoT := (List.range M).foldl (fun arr idx =>
    let a := idx + 1
    let prev := arr.getD idx 0
    let twoV := 2 * vPart p a
    arr.push (prev + min twoV twoRho)) #[0]
  -- Check 2 * R_3(h) <= 2 * W(h/2) + p (since 2 * lambda = L / p = p), equality uniquely at h = L
  (List.range M).all fun h =>
    let twoR := 2 * W.getD h 0 - twoT.getD h 0
    let rhs := 2 * W.getD (h / 2) 0 + p
    if h == L then twoR == rhs else twoR < rhs

theorem adjacent_cap_unique_equality_p3_p5 :
    checkAdjacentCapK3 3 = true ∧
    checkAdjacentCapK3 5 = true := by
  decide +kernel

/-- Lemma 5.1 (Four-parity endpoint carry inequality `W(x) + W(y) + V(a) + V(b) ≤ G + p`)
    verified exhaustively in Lean's kernel over ALL `1,596` pairs `1 ≤ a < b ≤ 57` at `p = 3, m = 57`. -/
def checkFourParity (p m : Nat) : Bool :=
  let u := (m - 1) / 2
  let W := buildWArray p m
  let G := W.getD u 0
  let V := (List.range (m + 1)).foldl (fun arr k =>
    arr.push (if k == 0 then 0 else vPart p k)) #[]
  (List.range m).all fun a0 =>
    let a := a0 + 1
    let x := (a - 1) / 2
    let wx := W.getD x 0
    let va := V.getD a 0
    (List.range (m - a)).all fun d0 =>
      let b := a + 1 + d0
      let y := (m - b) / 2
      wx + W.getD y 0 + va + V.getD b 0 ≤ G + p

theorem four_parity_endpoint_lemma_p3_m57 :
    checkFourParity 3 57 = true := by
  decide +kernel

/-- Out-of-scope odd-middle negative controls (Section 7):
    (1) `p = 3, m = 273, x = 121` gives `W(15) + W(121) + V(243) = 679 > G + 3 = 463`;
    (2) `p = 3, m = 819, x = 121` gives `W(288) + W(121) + V(243) = 1824 > G + 9 = 1662`. -/
theorem odd_middle_negative_controls :
    (let W := buildWArray 3 273
     let G := W.getD 136 0
     W.getD 15 0 + W.getD 121 0 + vPart 3 243 = 679 ∧ G + 3 = 463) ∧
    (let W := buildWArray 3 819
     let G := W.getD 409 0
     W.getD 288 0 + W.getD 121 0 + vPart 3 243 = 1824 ∧ G + 9 = 1662) := by
  decide +kernel

/-- Direct `F_109[X]` good-reduction certificate for `n = 2 * 3^2 + 2 = 20` (`p = 3, r = 2, s = 3`,
    primitive `27`-th root `q = 81` in `F_109`, since `81^27 ≡ 1` and `81^9 ≡ 45 ≠ 1 mod 109`):
    verifies `gcd(P_20, P_20') = 1`, `gcd(P_20, P_19) = 1`, and `gcd(H_20, H_20') = 1` in `F_109[X]`
    via explicit Bezout cofactors. -/
def powModFuel (mod : Nat) : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, acc => acc
  | f + 1, base, exp, acc =>
    if exp == 0 then acc
    else
      let acc' := if exp % 2 == 1 then (acc * base) % mod else acc
      powModFuel mod f ((base * base) % mod) (exp / 2) acc'

def powMod (base exp mod : Nat) : Nat :=
  powModFuel mod 8 (base % mod) exp (1 % mod)

def trimF109 : List Nat → List Nat
  | [] => [0]
  | c :: cs =>
    match trimF109 cs with
    | [0] => if c % 109 == 0 then [0] else [c % 109]
    | t => (c % 109) :: t

def invF109 (a : Nat) : Nat := powMod (a % 109) 107 109

def polyAddRaw : List Nat → List Nat → List Nat
  | [], b => b
  | a, [] => a
  | x :: xs, y :: ys => ((x + y) % 109) :: polyAddRaw xs ys

def polyAddF109 (a b : List Nat) : List Nat :=
  trimF109 (polyAddRaw a b)

def polyScaleRaw (c : Nat) : List Nat → List Nat
  | [] => []
  | x :: xs => ((c * x) % 109) :: polyScaleRaw c xs

def polySubScaleRaw (c : Nat) : List Nat → List Nat → List Nat
  | a, [] => a
  | [], y :: ys => ((109 - (c * y) % 109) % 109) :: polySubScaleRaw c [] ys
  | x :: xs, y :: ys => ((x + 109 - (c * y) % 109) % 109) :: polySubScaleRaw c xs ys

def polyMulRaw : List Nat → List Nat → List Nat
  | [], _ => []
  | x :: xs, b => polyAddRaw (polyScaleRaw x b) (0 :: polyMulRaw xs b)

def polyMulF109 (a b : List Nat) : List Nat :=
  trimF109 (polyMulRaw a b)

def derivRaw (k : Nat) : List Nat → List Nat
  | [] => []
  | x :: xs => ((x * k) % 109) :: derivRaw (k + 1) xs

def derivF109 : List Nat → List Nat
  | [] => [0]
  | _ :: rest => trimF109 (derivRaw 1 rest)

def buildP20Step (q : Nat) : Nat → Nat → List Nat → List Nat → List Nat × List Nat
  | 0, _, prev, curr => (prev, curr)
  | n + 1, qPow, prev, curr =>
    let edge := (109 + 1 - qPow) % 109
    let nxt := polySubScaleRaw edge (0 :: curr) prev
    buildP20Step q n ((qPow * q) % 109) curr nxt

def buildP20F109 (q : Nat) : List Nat × List Nat :=
  buildP20Step q 19 (q % 109) [1] [0, 1]

def buildH20Step (q qInv : Nat) : Nat → Nat → Nat → Nat → List Nat
  | 0, _, _, _ => []
  | n + 1, cur, qHigh, qLow =>
    let num := (109 + 1 - qHigh) % 109
    let den := (109 + 1 - qLow) % 109
    let nxt := (((cur * num) % 109) * invF109 den) % 109
    nxt :: buildH20Step q qInv n nxt ((qHigh * qInv) % 109) ((qLow * q) % 109)

def buildH20F109 (q : Nat) : List Nat :=
  1 :: buildH20Step q (invF109 q) 20 1 (powMod q 20 109) (q % 109)

/-- Exact Bezout cofactors in F_109[X] at q = 81 (primitive 27th root of unity)
    certifying gcd(P_20, P_20') = 1, gcd(P_20, P_19) = 1, and gcd(H_20, H_20') = 1. -/
def bezoutP20DerivU : List Nat := [90, 0, 26, 0, 76, 0, 22, 0, 63, 0, 9, 0, 52, 0, 93, 0, 98, 0, 72]
def bezoutP20DerivV : List Nat := [0, 17, 0, 82, 0, 11, 0, 1, 0, 87, 0, 83, 0, 19, 0, 96, 0, 104, 0, 40]
def bezoutP20P19U   : List Nat := [90, 0, 14, 0, 87, 0, 89, 0, 43, 0, 90, 0, 68, 0, 40, 0, 37, 0, 56]
def bezoutP20P19V   : List Nat := [0, 67, 0, 62, 0, 95, 0, 94, 0, 55, 0, 50, 0, 99, 0, 15, 0, 56, 0, 53]
def bezoutH20DerivU : List Nat := [82, 97, 39, 76, 92, 27, 10, 62, 6, 84, 17, 46, 17, 83, 72, 73, 82, 90, 42]
def bezoutH20DerivV : List Nat := [19, 100, 103, 3, 60, 37, 7, 19, 75, 64, 2, 30, 82, 106, 74, 65, 56, 85, 2, 96]

theorem good_reduction_squarefree_n20_F109 :
    let q := 81
    let (P19, P20) := buildP20F109 q
    let H20 := buildH20F109 q
    powMod q 27 109 = 1 ∧ powMod q 9 109 ≠ 1 ∧
    polyAddF109 (polyMulF109 bezoutP20DerivU P20)
                (polyMulF109 bezoutP20DerivV (derivF109 P20)) = [1] ∧
    polyAddF109 (polyMulF109 bezoutP20P19U P20)
                (polyMulF109 bezoutP20P19V P19) = [1] ∧
    polyAddF109 (polyMulF109 bezoutH20DerivU H20)
                (polyMulF109 bezoutH20DerivV (derivF109 H20)) = [1] := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

end RogersSzegoMultidigit

#print axioms RogersSzegoMultidigit.separated_tail_lt_pow
#print axioms RogersSzegoMultidigit.legal_degree_bound
#print axioms RogersSzegoMultidigit.annulus_dominance_margin
#print axioms RogersSzegoMultidigit.boundary_gaps_jge2
#print axioms RogersSzegoMultidigit.boundary_gaps_bottom_p
#print axioms RogersSzegoMultidigit.adjacent_k3_gaps_positive
#print axioms RogersSzegoMultidigit.adjacent_kge4_separate_deficit
#print axioms RogersSzegoMultidigit.bottom_p_high_order_carry_neg
#print axioms RogersSzegoMultidigit.consecutive_coprimality_propagation
#print axioms RogersSzegoMultidigit.sparse_carry_lemma_multi_digit_p3
#print axioms RogersSzegoMultidigit.adjacent_cap_unique_equality_p3_p5
#print axioms RogersSzegoMultidigit.four_parity_endpoint_lemma_p3_m57
#print axioms RogersSzegoMultidigit.odd_middle_negative_controls
#print axioms RogersSzegoMultidigit.good_reduction_squarefree_n20_F109
