import OMAStatements.S_oeis_a397434
import Mathlib

open Finset OMA.S_oeis_a397434

theorem Fdelta (k t : ℕ) :
    ∑ j ∈ range (k + 1), k.choose j * (if t ≤ j then 1 else 0)
      = ∑ j ∈ range (k + 1), k.choose j * (if t + 1 ≤ j then 1 else 0) + k.choose t := by
  have hterm : ∀ j ∈ range (k + 1), k.choose j * (if t ≤ j then 1 else 0)
      = k.choose j * (if t + 1 ≤ j then 1 else 0) + (if j = t then k.choose j else 0) := by
    intro j _
    split_ifs <;> omega
  rw [sum_congr rfl hterm, sum_add_distrib, sum_ite_eq']
  congr 1
  by_cases hk : t ∈ range (k + 1)
  · rw [if_pos hk]
  · rw [if_neg hk]
    exact (Nat.choose_eq_zero_of_lt (by rw [mem_range] at hk; omega)).symm

theorem Fpascal (k t : ℕ) :
    ∑ j ∈ range (k + 1 + 1), (k + 1).choose j * (if t + 1 ≤ j then 1 else 0)
      = ∑ j ∈ range (k + 1), k.choose j * (if t ≤ j then 1 else 0)
        + ∑ j ∈ range (k + 1), k.choose j * (if t + 1 ≤ j then 1 else 0) := by
  have e1 : ∑ j ∈ range (k + 1 + 1), (k + 1).choose j * (if t + 1 ≤ j then 1 else 0)
      = ∑ j ∈ range (k + 1), (k.choose j + k.choose (j + 1)) * (if t ≤ j then 1 else 0) := by
    rw [sum_range_succ']
    simp [Nat.choose_succ_succ']
  have e2 : ∑ j ∈ range (k + 1), k.choose j * (if t + 1 ≤ j then 1 else 0)
      = ∑ j ∈ range k, k.choose (j + 1) * (if t ≤ j then 1 else 0) := by
    rw [sum_range_succ']
    simp
  have e3 : ∑ j ∈ range (k + 1), k.choose (j + 1) * (if t ≤ j then 1 else 0)
      = ∑ j ∈ range k, k.choose (j + 1) * (if t ≤ j then 1 else 0) := by
    rw [sum_range_succ]
    simp
  have d : ∑ j ∈ range (k + 1), (k.choose j + k.choose (j + 1)) * (if t ≤ j then 1 else 0)
      = ∑ j ∈ range (k + 1), k.choose j * (if t ≤ j then 1 else 0)
        + ∑ j ∈ range (k + 1), k.choose (j + 1) * (if t ≤ j then 1 else 0) := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro j _
    ring
  rw [e1, d, e2, e3]

theorem Fmod (k t : ℕ) :
    (∑ j ∈ range (k + 1 + 1), (k + 1).choose j * (if t + 1 ≤ j then 1 else 0)) % 2
      = k.choose t % 2 := by
  rw [Fpascal k t, Fdelta k t]
  omega

theorem coeffEq {α : Type*} (t : ℕ) (s : Finset α) :
    coefficient t s
      = (∑ j ∈ range (s.card + 1), s.card.choose j * (if t ≤ j then 1 else 0)) % 2 := by
  unfold coefficient
  have h := sum_powerset_apply_card (fun j : ℕ => if t ≤ j then (1 : ℕ) else 0) (x := s)
  simp only [smul_eq_mul] at h
  rw [h]

theorem monoEq (n q : ℕ) (h : (n + 1) / 2 = q + 1) :
    monomials n = ∑ k ∈ range n, n.choose (k + 1) * (k.choose q % 2) := by
  unfold monomials
  rw [h]
  have key := sum_powerset_apply_card
    (fun k : ℕ => (∑ j ∈ range (k + 1), k.choose j * (if q + 1 ≤ j then 1 else 0)) % 2)
    (x := (univ : Finset (Fin n)))
  simp only [card_univ, Fintype.card_fin, smul_eq_mul] at key
  have h1 : ∑ s ∈ (univ : Finset (Fin n)).powerset, coefficient (q + 1) s
      = ∑ s ∈ (univ : Finset (Fin n)).powerset,
          (∑ j ∈ range (s.card + 1), s.card.choose j * (if q + 1 ≤ j then 1 else 0)) % 2 :=
    sum_congr rfl (fun s _ => coeffEq (q + 1) s)
  have hz : (∑ j ∈ range (0 + 1), (0 : ℕ).choose j * (if q + 1 ≤ j then 1 else 0)) % 2 = 0 := by
    simp
  rw [h1, key, sum_range_succ', hz, Nat.mul_zero, Nat.add_zero]
  apply sum_congr rfl
  intro k _
  rw [Fmod k q]

theorem Asame (N q : ℕ) :
    ∑ k ∈ range (N + 1), (N + 1).choose (k + 1) * (k.choose q % 2)
      = ∑ k ∈ range N, N.choose (k + 1) * (k.choose q % 2)
        + ∑ k ∈ range (N + 1), N.choose k * (k.choose q % 2) := by
  have e1 : ∑ k ∈ range (N + 1), (N + 1).choose (k + 1) * (k.choose q % 2)
      = ∑ k ∈ range (N + 1), N.choose k * (k.choose q % 2)
        + ∑ k ∈ range (N + 1), N.choose (k + 1) * (k.choose q % 2) := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro k _
    rw [Nat.choose_succ_succ' N k]
    ring
  have e2 : ∑ k ∈ range (N + 1), N.choose (k + 1) * (k.choose q % 2)
      = ∑ k ∈ range N, N.choose (k + 1) * (k.choose q % 2) := by
    rw [sum_range_succ]
    simp
  rw [e1, e2]
  omega

theorem parTwo (x y : ℕ) :
    y % 2 + (x + y) % 2 = x % 2 + 2 * (y % 2 * ((x + y) % 2)) := by
  have hy : y % 2 = 0 ∨ y % 2 = 1 := Nat.mod_two_eq_zero_or_one y
  have hxy : (x + y) % 2 = 0 ∨ (x + y) % 2 = 1 := Nat.mod_two_eq_zero_or_one (x + y)
  rcases hy with h | h <;> rcases hxy with h2 | h2 <;> rw [h, h2] <;> omega

theorem distTwo (C a b c d : ℕ) (h : a + b = c + 2 * d) :
    C * b + C * a = C * c + 2 * (C * d) := by
  calc C * b + C * a = C * (a + b) := by ring
    _ = C * (c + 2 * d) := by rw [h]
    _ = C * c + 2 * (C * d) := by ring

theorem Astep (N q : ℕ) :
    ∑ k ∈ range (N + 1), (N + 1).choose (k + 1) * (k.choose (q + 1) % 2)
      = ∑ k ∈ range N, N.choose (k + 1) * (k.choose q % 2)
        + 2 * ∑ k ∈ range N,
            N.choose (k + 1) * (k.choose (q + 1) % 2 * ((k + 1).choose (q + 1) % 2)) := by
  have e1 : ∑ k ∈ range (N + 1), (N + 1).choose (k + 1) * (k.choose (q + 1) % 2)
      = ∑ k ∈ range (N + 1), N.choose k * (k.choose (q + 1) % 2)
        + ∑ k ∈ range (N + 1), N.choose (k + 1) * (k.choose (q + 1) % 2) := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro k _
    rw [Nat.choose_succ_succ' N k]
    ring
  have e2 : ∑ k ∈ range (N + 1), N.choose k * (k.choose (q + 1) % 2)
      = ∑ k ∈ range N, N.choose (k + 1) * ((k + 1).choose (q + 1) % 2) := by
    rw [sum_range_succ']
    simp
  have e3 : ∑ k ∈ range (N + 1), N.choose (k + 1) * (k.choose (q + 1) % 2)
      = ∑ k ∈ range N, N.choose (k + 1) * (k.choose (q + 1) % 2) := by
    rw [sum_range_succ]
    simp
  have e4 : ∑ k ∈ range N, N.choose (k + 1) * ((k + 1).choose (q + 1) % 2)
        + ∑ k ∈ range N, N.choose (k + 1) * (k.choose (q + 1) % 2)
      = ∑ k ∈ range N, N.choose (k + 1) * (k.choose q % 2)
        + 2 * ∑ k ∈ range N,
            N.choose (k + 1) * (k.choose (q + 1) % 2 * ((k + 1).choose (q + 1) % 2)) := by
    rw [mul_sum, ← sum_add_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro k _
    have hp := parTwo (k.choose q) (k.choose (q + 1))
    rw [Nat.choose_succ_succ' k q]
    exact distTwo _ _ _ _ _ hp
  rw [e1, e2, e3]
  exact e4

theorem evenOdd (a b : ℕ) (ha : a % 2 = 0) (hb : b % 2 = 1) : a.choose b % 2 = 0 := by
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

theorem oddCase (m : ℕ) :
    monomials (2 * m + 1) < monomials (2 * m + 1 + 1) := by
  rw [monoEq (2 * m + 1) m (by omega), monoEq (2 * m + 1 + 1) m (by omega),
    Asame (2 * m + 1) m]
  have hmem : m ∈ range (2 * m + 1 + 1) := by
    rw [mem_range]
    omega
  have hb : m.choose m % 2 = 1 := by simp
  have hterm : (2 * m + 1).choose m * (m.choose m % 2) = (2 * m + 1).choose m := by
    rw [hb, Nat.mul_one]
  have hle : (2 * m + 1).choose m * (m.choose m % 2)
      ≤ ∑ k ∈ range (2 * m + 1 + 1), (2 * m + 1).choose k * (k.choose m % 2) :=
    single_le_sum (f := fun k => (2 * m + 1).choose k * (k.choose m % 2))
      (fun i _ => Nat.zero_le _) hmem
  have hc : 0 < (2 * m + 1).choose m := Nat.choose_pos (by omega)
  rw [hterm] at hle
  omega

theorem evenCase (m : ℕ) :
    monomials (2 * m + 2) = monomials (2 * m + 2 + 1)
      ↔ m % 2 = 0 := by
  rw [monoEq (2 * m + 2) m (by omega),
    monoEq (2 * m + 2 + 1) (m + 1) (by omega), Astep (2 * m + 2) m]
  constructor
  · intro h
    by_contra hm
    have hmem : m + 1 ∈ range (2 * m + 2) := by
      rw [mem_range]
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
      single_le_sum
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
      apply sum_eq_zero
      intro k _
      rcases Nat.mod_two_eq_zero_or_one k with hk | hk
      · rw [evenOdd k (m + 1) hk (by omega)]
        simp
      · rw [evenOdd (k + 1) (m + 1) (by omega) (by omega)]
        simp
    omega

theorem OMA.solution : type_of% @OMA.S_oeis_a397434.main := by
  intro n hn
  rcases Nat.even_or_odd' n with ⟨m, hm | hm⟩
  · obtain ⟨r, rfl⟩ : ∃ r, m = r + 1 := ⟨m - 1, by omega⟩
    subst hm
    have h := evenCase r
    have e : 2 * (r + 1) = 2 * r + 2 := by ring
    rw [e, h]
    constructor <;> intro h' <;> omega
  · subst hm
    have h := oddCase m
    constructor <;> intro h' <;> omega
