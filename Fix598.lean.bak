import Mathlib

/-! # Kernel-clean replacements for JSP-000598 `native_decide` lemmas -/

/-- Kummer bridge: to show `p ∣ C(n, k)` it suffices to exhibit one carry index. -/
theorem prime_dvd_choose_of_carry (p n k b : ℕ) (hp : p.Prime) (hkn : k ≤ n)
    (hnb : Nat.log p n < b)
    (i : ℕ) (hi1 : 1 ≤ i) (hib : i < b)
    (hcarry : p ^ i ≤ k % p ^ i + (n - k) % p ^ i) :
    p ∣ Nat.choose n k := by
  rw [Nat.Prime.dvd_iff_one_le_factorization hp (Nat.choose_pos hkn).ne',
    Nat.factorization_choose hp hkn hnb]
  have hmem : i ∈ (Finset.Ico 1 b).filter (fun j => p ^ j ≤ k % p ^ j + (n - k) % p ^ j) := by
    simp only [Finset.mem_filter, Finset.mem_Ico]
    exact ⟨⟨hi1, hib⟩, hcarry⟩
  exact Nat.one_le_iff_ne_zero.mpr (by
    intro hzero
    rw [Finset.card_eq_zero.mp hzero] at hmem
    simp at hmem)

/-- `2 ∣ C(176, 88)`: carry at i = 4 (2^4 = 16 ≤ 2 · (88 mod 16) = 16). -/
theorem dvd_two_choose176_88 : 2 ∣ Nat.choose 176 88 := by
  refine prime_dvd_choose_of_carry 2 176 88 8 (by decide) (by decide) (by decide) 4
    (by decide) (by decide) ?_
  decide

/-- `11 ∣ C(176, 88)`: carry at i = 2 (11² = 121 ≤ 2 · (88 mod 121) = 176). -/
theorem dvd_eleven_choose176_88 : 11 ∣ Nat.choose 176 88 := by
  refine prime_dvd_choose_of_carry 11 176 88 3 (by decide) (by decide) (by decide) 2
    (by decide) (by decide) ?_
  decide

/-- `5 ∣ C(174, 87)`: carry at i = 3 (5³ = 125 ≤ 2 · (87 mod 125) = 174). -/
theorem dvd_five_choose174_87 : 5 ∣ Nat.choose 174 87 := by
  refine prime_dvd_choose_of_carry 5 174 87 4 (by decide) (by decide) (by decide) 3
    (by decide) (by decide) ?_
  decide

/-- `7 ∣ C(174, 87)`: carry at i = 2 (7² = 49 ≤ 2 · (87 mod 49) = 76). -/
theorem dvd_seven_choose174_87 : 7 ∣ Nat.choose 174 87 := by
  refine prime_dvd_choose_of_carry 7 174 87 3 (by decide) (by decide) (by decide) 2
    (by decide) (by decide) ?_
  decide

/-- General scaling identity: `(n+1) · C(2n+2, n+1) = 2(2n+1) · C(2n, n)`. -/
theorem choose_two_n_scaling (n : ℕ) :
    Nat.choose (2 * n + 2) (n + 1) * (n + 1) = 2 * (2 * n + 1) * Nat.choose (2 * n) n := by
  have hkn1 : n + 1 ≤ 2 * n + 2 := by omega
  have hkn : n ≤ 2 * n := by omega
  have h1 := Nat.choose_mul_factorial_mul_factorial hkn1
  rw [show 2 * n + 2 - (n + 1) = n + 1 from by omega] at h1
  have h2 := Nat.choose_mul_factorial_mul_factorial hkn
  rw [show 2 * n - n = n from by omega] at h2
  -- h1 : C₁ * (n+1)! * (n+1)! = (2n+2)!
  -- h2 : C₀ * n! * n! = (2n)!
  have e1 : (2 * n + 2).factorial = (2 * n + 2) * ((2 * n + 1) * (2 * n).factorial) := by
    rw [Nat.factorial_succ, Nat.factorial_succ]
  have e2 : (n + 1).factorial = (n + 1) * n.factorial := Nat.factorial_succ n
  rw [e1, e2] at h1
  have hn0 : n.factorial ≠ 0 := Nat.factorial_ne_zero n
  have hpos : 0 < (n + 1) * (n.factorial * n.factorial) := by
    positivity
  apply Nat.mul_right_cancel hpos
  calc Nat.choose (2 * n + 2) (n + 1) * (n + 1)
        * ((n + 1) * (n.factorial * n.factorial))
      = Nat.choose (2 * n + 2) (n + 1) * ((n + 1) * n.factorial)
        * ((n + 1) * n.factorial) := by ring
    _ = (2 * n + 2) * ((2 * n + 1) * (2 * n).factorial) := h1
    _ = 2 * (2 * n + 1) * Nat.choose (2 * n) n
        * ((n + 1) * (n.factorial * n.factorial)) := by
        rw [← h2]
        ring
