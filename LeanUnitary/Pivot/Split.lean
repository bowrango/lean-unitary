import Mathlib

/-!
# Balanced splits

The merge condition of `submission/decomposition.tex`, Sec. II.B. Demultiplexing `I ⊕ C`
assigns eigenphases `μ_k` of `C` to basis states `j`, `θ_j = μ_{k(j)} + 2π m_j` (Eq. 6), and the
final angle of the multiplexed rotation is `φ = (1/D) Σ_j h_j θ_j` (Eq. 3), with `h_j = ±1`.

Here `P` is the set of basis states with `h_j = +1`, `e` the assignment `j ↦ k(j)` and `m` the
branch shifts. This module proves:

* `walsh_eq` (Eq. 7): `Σ_j h_j θ_j = Σ_{k ∈ S} μ_k - Σ_{k ∉ S} μ_k + 2π ℓ` with `S = e(P)` and
  `ℓ = Σ_j h_j m_j`;
* `exists_walsh_eq_zero_iff` (Eq. 8): some assignment and branches give `φ = 0` iff there is a
  balanced split, a set `S` with `|S| = |P|` and `Σ_S μ - Σ_{Sᶜ} μ ∈ 2π ℤ`.
-/

namespace LeanUnitary.Pivot

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Walsh row `h_j`: `+1` on `P`, `-1` off it. -/
def walshSign (P : Finset ι) (j : ι) : ℝ := if j ∈ P then 1 else -1

/-- `D φ = Σ_j h_j θ_j` with `θ_j = μ_{e j} + 2π m_j` (Eqs. 3 and 6). -/
noncomputable def walsh (P : Finset ι) (μ : ι → ℝ) (e : Equiv.Perm ι) (m : ι → ℤ) : ℝ :=
  ∑ j, walshSign P j * (μ (e j) + 2 * Real.pi * m j)

/-- The split imbalance `Σ_{k ∈ S} μ_k - Σ_{k ∉ S} μ_k`. -/
def imbalance (S : Finset ι) (μ : ι → ℝ) : ℝ := ∑ k ∈ S, μ k - ∑ k ∈ Sᶜ, μ k

theorem sum_walshSign_mul (S : Finset ι) (μ : ι → ℝ) :
    ∑ k, walshSign S k * μ k = imbalance S μ := by
  rw [imbalance, ← Finset.sum_add_sum_compl S, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1 <;> refine Finset.sum_congr rfl fun k hk => ?_
  · simp [walshSign, hk]
  · simp [walshSign, Finset.mem_compl.mp hk]

/-- Eq. 7: the final angle depends only on the split `S = e(P)` and an integer `ℓ`. -/
theorem walsh_eq (P : Finset ι) (μ : ι → ℝ) (e : Equiv.Perm ι) (m : ι → ℤ) :
    walsh P μ e m =
      imbalance (P.map e.toEmbedding) μ + 2 * Real.pi * (∑ j, walshSign P j * m j) := by
  rw [walsh, ← sum_walshSign_mul, Finset.mul_sum,
    ← Equiv.sum_comp e (fun k => walshSign (P.map e.toEmbedding) k * μ k),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have : walshSign (P.map e.toEmbedding) (e j) = walshSign P j := by
    simp [walshSign]
  rw [this]
  ring

omit [Fintype ι] [DecidableEq ι] in
/-- A permutation carrying `P` onto any `S` of the same size. -/
theorem exists_perm_map_eq [Finite ι] {P S : Finset ι} (h : S.card = P.card) :
    ∃ e : Equiv.Perm ι, P.map e.toEmbedding = S := by
  classical
  have h₁ : Fintype.card {x // x ∈ P} = Fintype.card {x // x ∈ S} := by simp [h]
  let e := (Fintype.equivOfCardEq h₁).extendSubtype
  refine ⟨e, ?_⟩
  ext k
  rw [Finset.mem_map_equiv]
  constructor
  · intro hk
    have : e (e.symm k) ∈ S := Equiv.extendSubtype_mem (Fintype.equivOfCardEq h₁) _ hk
    rwa [Equiv.apply_symm_apply] at this
  · intro hk
    by_contra hP
    exact Equiv.extendSubtype_not_mem (Fintype.equivOfCardEq h₁) _ hP (by simpa [e] using hk)

/-- Eq. 8: `φ = 0` is attainable iff the eigenphases admit a balanced split. -/
theorem exists_walsh_eq_zero_iff {P : Finset ι} (hP : P.Nonempty) (μ : ι → ℝ) :
    (∃ (e : Equiv.Perm ι) (m : ι → ℤ), walsh P μ e m = 0) ↔
      ∃ S : Finset ι, S.card = P.card ∧ ∃ ℓ : ℤ, imbalance S μ = -(2 * Real.pi * ℓ) := by
  constructor
  · rintro ⟨e, m, h⟩
    refine ⟨P.map e.toEmbedding, by simp, ∑ j, if j ∈ P then m j else -m j, ?_⟩
    have hℓ : ∑ j, walshSign P j * (m j : ℝ) = ((∑ j, if j ∈ P then m j else -m j : ℤ) : ℝ) := by
      push_cast
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hj : j ∈ P <;> simp [walshSign, hj]
    rw [walsh_eq, hℓ] at h
    linarith
  · rintro ⟨S, hS, ℓ, hℓ⟩
    obtain ⟨e, he⟩ := exists_perm_map_eq hS
    obtain ⟨j₀, hj₀⟩ := hP
    refine ⟨e, fun j => if j = j₀ then ℓ else 0, ?_⟩
    rw [walsh_eq, he, hℓ]
    simp [walshSign, hj₀]

end LeanUnitary.Pivot
