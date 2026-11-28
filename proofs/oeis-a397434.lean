import OMAStatements.S_oeis_a397434
import Mathlib

open Finset

/-- Removing the threshold value `t` from the tail sum costs exactly `C(k,t)`. -/
theorem a397434_F_delta (k t : ℕ) :
    ∑ j ∈ range (k + 1), k.choose j * (if t ≤ j then 1 else 0)
      = ∑ j ∈ range (k + 1), k.choose j * (if t + 1 ≤ j then 1 else 0) + k.choose t := by
  have hterm : ∀ j ∈ range (k + 1), k.choose j * (if t ≤ j then 1 else 0)
      = k.choose j * (if t + 1 ≤ j then 1 else 0) + (if j = t then k.choose j else 0) := by
    intro j _
    split_ifs <;> omega
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_ite_eq']
  congr 1
  by_cases hk : t ∈ range (k + 1)
  · rw [if_pos hk]
  · rw [if_neg hk]
    exact (Nat.choose_eq_zero_of_lt (by rw [Finset.mem_range] at hk; omega)).symm

/-- Pascal's rule for the tail sums. -/
theorem a397434_F_pascal (k t : ℕ) :
    ∑ j ∈ range (k + 1 + 1), (k + 1).choose j * (if t + 1 ≤ j then 1 else 0)
      = ∑ j ∈ range (k + 1), k.choose j * (if t ≤ j then 1 else 0)
        + ∑ j ∈ range (k + 1), k.choose j * (if t + 1 ≤ j then 1 else 0) := by
  have e1 : ∑ j ∈ range (k + 1 + 1), (k + 1).choose j * (if t + 1 ≤ j then 1 else 0)
      = ∑ j ∈ range (k + 1), (k.choose j + k.choose (j + 1)) * (if t ≤ j then 1 else 0) := by
    rw [Finset.sum_range_succ']
    simp [Nat.choose_succ_succ']
  have e2 : ∑ j ∈ range (k + 1), k.choose j * (if t + 1 ≤ j then 1 else 0)
      = ∑ j ∈ range k, k.choose (j + 1) * (if t ≤ j then 1 else 0) := by
    rw [Finset.sum_range_succ']
    simp
  have e3 : ∑ j ∈ range (k + 1), k.choose (j + 1) * (if t ≤ j then 1 else 0)
      = ∑ j ∈ range k, k.choose (j + 1) * (if t ≤ j then 1 else 0) := by
    rw [Finset.sum_range_succ]
    simp
  have d : ∑ j ∈ range (k + 1), (k.choose j + k.choose (j + 1)) * (if t ≤ j then 1 else 0)
      = ∑ j ∈ range (k + 1), k.choose j * (if t ≤ j then 1 else 0)
        + ∑ j ∈ range (k + 1), k.choose (j + 1) * (if t ≤ j then 1 else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [e1, d, e2, e3]

/-- The tail sum of row `k+1` from `t+1` has the parity of `C(k,t)`. -/
theorem a397434_F_mod (k t : ℕ) :
    (∑ j ∈ range (k + 1 + 1), (k + 1).choose j * (if t + 1 ≤ j then 1 else 0)) % 2
      = k.choose t % 2 := by
  rw [a397434_F_pascal k t, a397434_F_delta k t]
  omega

/-- The coefficient depends only on the cardinality. -/
theorem a397434_coeff {α : Type*} (t : ℕ) (s : Finset α) :
    OMA.S_oeis_a397434.coefficient t s
      = (∑ j ∈ range (s.card + 1), s.card.choose j * (if t ≤ j then 1 else 0)) % 2 := by
  unfold OMA.S_oeis_a397434.coefficient
  have h := Finset.sum_powerset_apply_card (fun j : ℕ => if t ≤ j then (1 : ℕ) else 0) (x := s)
  simp only [smul_eq_mul] at h
  rw [h]

/-- Closed form: `monomials n = ∑_{k<n} C(n,k+1) * (C(k,q) mod 2)` when the threshold is `q+1`. -/
theorem a397434_monomials (n q : ℕ) (h : (n + 1) / 2 = q + 1) :
    OMA.S_oeis_a397434.monomials n = ∑ k ∈ range n, n.choose (k + 1) * (k.choose q % 2) := by
  unfold OMA.S_oeis_a397434.monomials
  rw [h]
  have key := Finset.sum_powerset_apply_card
    (fun k : ℕ => (∑ j ∈ range (k + 1), k.choose j * (if q + 1 ≤ j then 1 else 0)) % 2)
    (x := (univ : Finset (Fin n)))
  simp only [Finset.card_univ, Fintype.card_fin, smul_eq_mul] at key
  have h1 : ∑ s ∈ (univ : Finset (Fin n)).powerset, OMA.S_oeis_a397434.coefficient (q + 1) s
      = ∑ s ∈ (univ : Finset (Fin n)).powerset,
          (∑ j ∈ range (s.card + 1), s.card.choose j * (if q + 1 ≤ j then 1 else 0)) % 2 :=
    Finset.sum_congr rfl (fun s _ => a397434_coeff (q + 1) s)
  have hz : (∑ j ∈ range (0 + 1), (0 : ℕ).choose j * (if q + 1 ≤ j then 1 else 0)) % 2 = 0 := by
    simp
  rw [h1, key, Finset.sum_range_succ', hz, Nat.mul_zero, Nat.add_zero]
  apply Finset.sum_congr rfl
  intro k _
  rw [a397434_F_mod k q]

/-- Same threshold, one more variable. -/
theorem a397434_A_same (N q : ℕ) :
    ∑ k ∈ range (N + 1), (N + 1).choose (k + 1) * (k.choose q % 2)
      = ∑ k ∈ range N, N.choose (k + 1) * (k.choose q % 2)
        + ∑ k ∈ range (N + 1), N.choose k * (k.choose q % 2) := by
  have e1 : ∑ k ∈ range (N + 1), (N + 1).choose (k + 1) * (k.choose q % 2)
      = ∑ k ∈ range (N + 1), N.choose k * (k.choose q % 2)
        + ∑ k ∈ range (N + 1), N.choose (k + 1) * (k.choose q % 2) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [Nat.choose_succ_succ' N k]
    ring
  have e2 : ∑ k ∈ range (N + 1), N.choose (k + 1) * (k.choose q % 2)
      = ∑ k ∈ range N, N.choose (k + 1) * (k.choose q % 2) := by
    rw [Finset.sum_range_succ]
    simp
  rw [e1, e2]
  omega

theorem a397434_par (x y : ℕ) :
    y % 2 + (x + y) % 2 = x % 2 + 2 * (y % 2 * ((x + y) % 2)) := by
  have hy : y % 2 = 0 ∨ y % 2 = 1 := Nat.mod_two_eq_zero_or_one y
  have hxy : (x + y) % 2 = 0 ∨ (x + y) % 2 = 1 := Nat.mod_two_eq_zero_or_one (x + y)
  rcases hy with h | h <;> rcases hxy with h2 | h2 <;> rw [h, h2] <;> omega

theorem a397434_dist (C a b c d : ℕ) (h : a + b = c + 2 * d) :
    C * b + C * a = C * c + 2 * (C * d) := by
  calc C * b + C * a = C * (a + b) := by ring
    _ = C * (c + 2 * d) := by rw [h]
    _ = C * c + 2 * (C * d) := by ring

/-- Threshold and variable count both go up by one. -/
theorem a397434_A_step (N q : ℕ) :
    ∑ k ∈ range (N + 1), (N + 1).choose (k + 1) * (k.choose (q + 1) % 2)
      = ∑ k ∈ range N, N.choose (k + 1) * (k.choose q % 2)
        + 2 * ∑ k ∈ range N,
            N.choose (k + 1) * (k.choose (q + 1) % 2 * ((k + 1).choose (q + 1) % 2)) := by
  have e1 : ∑ k ∈ range (N + 1), (N + 1).choose (k + 1) * (k.choose (q + 1) % 2)
      = ∑ k ∈ range (N + 1), N.choose k * (k.choose (q + 1) % 2)
        + ∑ k ∈ range (N + 1), N.choose (k + 1) * (k.choose (q + 1) % 2) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [Nat.choose_succ_succ' N k]
    ring
  have e2 : ∑ k ∈ range (N + 1), N.choose k * (k.choose (q + 1) % 2)
      = ∑ k ∈ range N, N.choose (k + 1) * ((k + 1).choose (q + 1) % 2) := by
    rw [Finset.sum_range_succ']
    simp
  have e3 : ∑ k ∈ range (N + 1), N.choose (k + 1) * (k.choose (q + 1) % 2)
      = ∑ k ∈ range N, N.choose (k + 1) * (k.choose (q + 1) % 2) := by
    rw [Finset.sum_range_succ]
    simp
  have e4 : ∑ k ∈ range N, N.choose (k + 1) * ((k + 1).choose (q + 1) % 2)
        + ∑ k ∈ range N, N.choose (k + 1) * (k.choose (q + 1) % 2)
      = ∑ k ∈ range N, N.choose (k + 1) * (k.choose q % 2)
        + 2 * ∑ k ∈ range N,
            N.choose (k + 1) * (k.choose (q + 1) % 2 * ((k + 1).choose (q + 1) % 2)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    have hp := a397434_par (k.choose q) (k.choose (q + 1))
    rw [Nat.choose_succ_succ' k q]
    exact a397434_dist _ _ _ _ _ hp
  rw [e1, e2, e3]
  exact e4

/-- An even row has even entries in odd columns. -/
theorem a397434_even_odd (a b : ℕ) (ha : a % 2 = 0) (hb : b % 2 = 1) : a.choose b % 2 = 0 := by
  rcases a with _ | a'
  · rcases b with _ | b'
    · omega
    · simp
  · rcases b with _ | b'
    · omega
    · have h := Nat.add_one_mul_choose_eq a' b'
      have he : Even (a' + 1) := Nat.even_iff.mpr ha
      have h1 : Even ((a' + 1).choose (b' + 1) * (b' + 1)) := by
        rw [← h]
        exact he.mul_right _
      rcases Nat.even_mul.mp h1 with h2 | h2
      · exact Nat.even_iff.mp h2
      · exact absurd (Nat.even_iff.mp h2) (by omega)

theorem a397434_odd (m : ℕ) :
    OMA.S_oeis_a397434.monomials (2 * m + 1) < OMA.S_oeis_a397434.monomials (2 * m + 1 + 1) := by
  rw [a397434_monomials (2 * m + 1) m (by omega), a397434_monomials (2 * m + 1 + 1) m (by omega),
    a397434_A_same (2 * m + 1) m]
  have hmem : m ∈ range (2 * m + 1 + 1) := by
    rw [Finset.mem_range]
    omega
  have hb : m.choose m % 2 = 1 := by simp
  have hterm : (2 * m + 1).choose m * (m.choose m % 2) = (2 * m + 1).choose m := by
    rw [hb, Nat.mul_one]
  have hle : (2 * m + 1).choose m * (m.choose m % 2)
      ≤ ∑ k ∈ range (2 * m + 1 + 1), (2 * m + 1).choose k * (k.choose m % 2) :=
    Finset.single_le_sum (f := fun k => (2 * m + 1).choose k * (k.choose m % 2))
      (fun i _ => Nat.zero_le _) hmem
  have hc : 0 < (2 * m + 1).choose m := Nat.choose_pos (by omega)
  rw [hterm] at hle
  omega

theorem a397434_even (m : ℕ) :
    OMA.S_oeis_a397434.monomials (2 * m + 2) = OMA.S_oeis_a397434.monomials (2 * m + 2 + 1)
      ↔ m % 2 = 0 := by
  rw [a397434_monomials (2 * m + 2) m (by omega),
    a397434_monomials (2 * m + 2 + 1) (m + 1) (by omega), a397434_A_step (2 * m + 2) m]
  constructor
  · intro h
    by_contra hm
    have hmem : m + 1 ∈ range (2 * m + 2) := by
      rw [Finset.mem_range]
      omega
    have h2 : (m + 1 + 1) % 2 = 1 := by omega
    have hb1 : (m + 1).choose (m + 1) % 2 = 1 := by simp
    have hb2 : (m + 1 + 1).choose (m + 1) % 2 = 1 := by
      rw [Nat.choose_succ_self_right]
      exact h2
    have hterm : (2 * m + 2).choose (m + 1 + 1)
          * ((m + 1).choose (m + 1) % 2 * ((m + 1 + 1).choose (m + 1) % 2))
        = (2 * m + 2).choose (m + 1 + 1) := by
      rw [hb1, hb2, Nat.mul_one]
    have hle : (2 * m + 2).choose (m + 1 + 1)
          * ((m + 1).choose (m + 1) % 2 * ((m + 1 + 1).choose (m + 1) % 2))
        ≤ ∑ k ∈ range (2 * m + 2),
            (2 * m + 2).choose (k + 1) * (k.choose (m + 1) % 2 * ((k + 1).choose (m + 1) % 2)) :=
      Finset.single_le_sum
        (f := fun k => (2 * m + 2).choose (k + 1)
          * (k.choose (m + 1) % 2 * ((k + 1).choose (m + 1) % 2)))
        (fun i _ => Nat.zero_le _) hmem
    have hc : 0 < (2 * m + 2).choose (m + 1 + 1) := Nat.choose_pos (by omega)
    rw [hterm] at hle
    omega
  · intro hm
    have hz : ∑ k ∈ range (2 * m + 2),
        (2 * m + 2).choose (k + 1) * (k.choose (m + 1) % 2 * ((k + 1).choose (m + 1) % 2))
          = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      rcases Nat.mod_two_eq_zero_or_one k with hk | hk
      · rw [a397434_even_odd k (m + 1) hk (by omega)]
        simp
      · rw [a397434_even_odd (k + 1) (m + 1) (by omega) (by omega)]
        simp
    omega

theorem OMA.solution : type_of% @OMA.S_oeis_a397434.main := by
  intro n hn
  rcases Nat.even_or_odd' n with ⟨m, hm | hm⟩
  · obtain ⟨r, rfl⟩ : ∃ r, m = r + 1 := ⟨m - 1, by omega⟩
    subst hm
    have h := a397434_even r
    have e : 2 * (r + 1) = 2 * r + 2 := by ring
    rw [e, h]
    constructor <;> intro h' <;> omega
  · subst hm
    have h := a397434_odd m
    constructor <;> intro h' <;> omega
