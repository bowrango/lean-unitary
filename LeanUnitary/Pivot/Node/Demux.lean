import LeanUnitary.Pivot.Node.Factor
import LeanUnitary.LinearAlgebra

/-!
# Demultiplexing with prescribed eigenphases

Shende–Markov–Bullock, Thm. 12 (the paper, Eq. 1): `A ⊕ B = (V ⊕ V) · D(θ) · (W ⊕ W)` where
`D(θ)` is a multiplexed `R_z` on the top qubit and `e^{iθ_k}` are the eigenvalues of `B Aᴴ`.
For the pivot the assignment of eigenphases to basis states matters (Eq. 5–6), so
`demux_of_phases` takes *any* listing `θ` of the eigenphases of `C`, in any order and with any
branches, and demultiplexes `I ⊕ C` with exactly those angles. Both rest on the unitary
spectral theorem `LinearAlgebra.exists_unitary_diagonalize_of_mem_unitaryGroup`.
-/

namespace LeanUnitary.Pivot.Node

open Matrix Complex Finset

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- The multiplexed `R_z(θ)` on the top qubit, as a block matrix (`Blocks.mux_last_eq`). -/
noncomputable def Dz (θ : m → ℝ) : Matrix (m ⊕ m) (m ⊕ m) ℂ :=
  fromBlocks (diagonal fun k => exp (-((θ k / 2 : ℝ) : ℂ) * I)) 0 0
    (diagonal fun k => exp (((θ k / 2 : ℝ) : ℂ) * I))

theorem roots_charpoly_conj_diagonal {V : Matrix m m ℂ} (hV : V ∈ unitaryGroup m ℂ) (d : m → ℂ) :
    (V * diagonal d * star V).charpoly.roots = (univ : Finset m).val.map d := by
  rw [charpoly_mul_comm, ← Matrix.mul_assoc, mem_unitaryGroup_iff'.mp hV, Matrix.one_mul,
    charpoly_diagonal, Polynomial.roots_prod]
  · simp
  · exact Finset.prod_ne_zero_iff.mpr fun i _ => Polynomial.X_sub_C_ne_zero _

/-- A unitary is diagonalized with its eigenvalues in any prescribed order. -/
theorem exists_unitary_of_roots {C : Matrix m m ℂ} (hC : C ∈ unitaryGroup m ℂ) (f : m → ℂ)
    (hf : (univ : Finset m).val.map f = C.charpoly.roots) :
    ∃ V ∈ unitaryGroup m ℂ, C = V * diagonal f * star V := by
  obtain ⟨V', hV', θ', hC'⟩ := LinearAlgebra.exists_unitary_diagonalize_of_mem_unitaryGroup hC
  set e' : m → ℂ := fun i => exp (θ' i * I)
  have hroots : (univ : Finset m).val.map f = (univ : Finset m).val.map e' := by
    rw [hf, hC', roots_charpoly_conj_diagonal hV']
  obtain ⟨σ, hσ⟩ := exists_perm_of_map_eq hroots
  refine ⟨V'.submatrix id σ, ?_, ?_⟩
  · have hs := submatrix_mul_equiv V'ᴴ V' (⇑σ) (Equiv.refl m) (⇑σ)
    simp only [Equiv.coe_refl] at hs
    rw [mem_unitaryGroup_iff', star_eq_conjTranspose, conjTranspose_submatrix, hs,
      ← star_eq_conjTranspose, mem_unitaryGroup_iff'.mp hV']
    exact submatrix_one_equiv σ
  · rw [hC']
    ext i j
    simp only [Matrix.mul_apply, diagonal_apply, star_apply, submatrix_apply, id_eq,
      mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [← Equiv.sum_comp σ]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hσ]

/-- The block form of demultiplexing, from a diagonalization of `B Aᴴ`. -/
theorem demux_of_diag {A B V : Matrix m m ℂ} (hA : A ∈ unitaryGroup m ℂ)
    (hV : V ∈ unitaryGroup m ℂ) (θ : m → ℝ)
    (h : B * star A = V * diagonal (fun k => exp (θ k * I)) * star V) :
    ∃ W ∈ unitaryGroup m ℂ,
      fromBlocks A 0 0 B = fromBlocks V 0 0 V * Dz θ * fromBlocks W 0 0 W := by
  set Dp : Matrix m m ℂ := diagonal fun k => exp (((θ k / 2 : ℝ) : ℂ) * I) with hDp
  set Dm : Matrix m m ℂ := diagonal fun k => exp (-((θ k / 2 : ℝ) : ℂ) * I) with hDm
  have hDmp : Dm * Dp = 1 := by
    rw [hDm, hDp, diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext k; rw [← exp_add]; simp
  have hDpp : Dp * Dp = diagonal fun k => exp (θ k * I) := by
    rw [hDp, diagonal_mul_diagonal]
    congr 1; funext k; rw [← exp_add]; congr 1; push_cast; ring
  have hDpm : Dp ∈ unitaryGroup m ℂ := by
    rw [mem_unitaryGroup_iff', star_eq_conjTranspose, hDp, diagonal_conjTranspose,
      diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext k
    simp only [Pi.star_apply, Complex.star_def, ← exp_conj, ← exp_add, map_mul, conj_ofReal,
      conj_I]
    ring_nf; simp
  refine ⟨Dp * star V * A, Submonoid.mul_mem _ (Submonoid.mul_mem _ hDpm (Unitary.star_mem hV)) hA,
    ?_⟩
  rw [Dz, fromBlocks_multiply, fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  congr 1
  · rw [← hDm, Matrix.mul_assoc, ← Matrix.mul_assoc Dm, ← Matrix.mul_assoc Dm, hDmp, Matrix.one_mul,
      ← Matrix.mul_assoc, mem_unitaryGroup_iff.mp hV, Matrix.one_mul]
  · rw [← hDp, Matrix.mul_assoc, ← Matrix.mul_assoc Dp, ← Matrix.mul_assoc Dp, hDpp,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← h, Matrix.mul_assoc, mem_unitaryGroup_iff'.mp hA,
      Matrix.mul_one]

/-- **Demultiplexing** (Shende–Markov–Bullock, Thm. 12). -/
theorem demux {A B : Matrix m m ℂ} (hA : A ∈ unitaryGroup m ℂ) (hB : B ∈ unitaryGroup m ℂ) :
    ∃ V ∈ unitaryGroup m ℂ, ∃ W ∈ unitaryGroup m ℂ, ∃ θ : m → ℝ,
      fromBlocks A 0 0 B = fromBlocks V 0 0 V * Dz θ * fromBlocks W 0 0 W := by
  obtain ⟨V, hV, θ, h⟩ := LinearAlgebra.exists_unitary_diagonalize_of_mem_unitaryGroup
    (Submonoid.mul_mem _ hB (Unitary.star_mem hA))
  obtain ⟨W, hW, h'⟩ := demux_of_diag hA hV θ h
  exact ⟨V, hV, W, hW, θ, h'⟩

/-- **Demultiplexing `I ⊕ C` with prescribed angles**: any listing `θ` of the eigenphases of `C`
(in any order, with any `2π` branches) is realized. -/
theorem demux_of_phases {C : Matrix m m ℂ} (hC : C ∈ unitaryGroup m ℂ) (θ : m → ℝ)
    (hθ : (univ : Finset m).val.map (fun k => exp (θ k * I)) = C.charpoly.roots) :
    ∃ V ∈ unitaryGroup m ℂ, ∃ W ∈ unitaryGroup m ℂ,
      fromBlocks 1 0 0 C = fromBlocks V 0 0 V * Dz θ * fromBlocks W 0 0 W := by
  obtain ⟨V, hV, h⟩ := exists_unitary_of_roots hC _ hθ
  have h1 : C * star (1 : Matrix m m ℂ) = V * diagonal (fun k => exp (θ k * I)) * star V := by
    rw [star_one, Matrix.mul_one]; exact h
  obtain ⟨W, hW, h'⟩ := demux_of_diag (Submonoid.one_mem _) hV θ h1
  exact ⟨V, hV, W, hW, h'⟩

end LeanUnitary.Pivot.Node
