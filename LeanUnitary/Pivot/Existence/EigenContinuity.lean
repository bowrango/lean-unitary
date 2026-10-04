import LeanUnitary.Pivot.Path.Eigenvalues

/-!
# Continuity of eigenvalues

The eigenvalues of a matrix depend continuously on it, as a multiset. Mathlib has no
perturbation theory for eigenvalues, so this module proves the statement from scratch, in the
form used for the eigenphases of `C(β)`:

* `norm_le_of_mem_roots_charpoly`: every eigenvalue satisfies `‖τ‖ ≤ Σ_{i,j} ‖M_{ij}‖`;
* `eventually_exists_perm_close`: if `β ↦ M(β)` is continuous at `β₀`, then for `β` near `β₀`
  any listing of the eigenvalues of `M(β)` can be matched, by a permutation, to within `ε` of a
  listing of the eigenvalues of `M(β₀)`.

The proof is by compactness. Suppose no such matching exists along some sequence `β_n → β₀`. The
eigenvalue lists are bounded, so a subsequence converges to some list `r`. Then
`∏ (t - r_k) = lim det (t - M(β_n)) = det (t - M(β₀))` for every `t`, so `r` lists the
eigenvalues of `M(β₀)` (`multiset_eq_of_prod_sub_eq`): a contradiction.
-/

namespace LeanUnitary.Pivot

open Matrix Filter Topology Finset

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- Every eigenvalue is bounded by the sum of the entry norms. -/
theorem norm_le_of_mem_roots_charpoly {M : Matrix m m ℂ} {τ : ℂ} (hτ : τ ∈ M.charpoly.roots) :
    ‖τ‖ ≤ ∑ i, ∑ j, ‖M i j‖ := by
  have hroot := (Polynomial.mem_roots M.charpoly_monic.ne_zero).mp hτ
  rw [Polynomial.IsRoot, eval_charpoly] at hroot
  obtain ⟨x, hx0, hx⟩ := exists_mulVec_eq_zero_iff.mpr hroot
  have hm : Nonempty m := by
    by_contra h
    exact hx0 (funext fun i => absurd ⟨i⟩ h)
  obtain ⟨i, hi⟩ := Finite.exists_max fun j => ‖x j‖
  have hxi : 0 < ‖x i‖ := by
    by_contra h
    push Not at h
    exact hx0 (funext fun j => norm_le_zero_iff.mp ((hi j).trans h))
  -- row `i` of `M x = τ x`
  have hrow : τ * x i = ∑ j, M i j * x j := by
    have := congrFun hx i
    simp only [sub_mulVec, Pi.sub_apply, Pi.zero_apply, sub_eq_zero, scalar_apply,
      mulVec_diagonal] at this
    rw [this]; rfl
  have hbound : ‖τ‖ * ‖x i‖ ≤ (∑ j, ‖M i j‖) * ‖x i‖ := by
    rw [← norm_mul, hrow, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hi j) (norm_nonneg _)
  have hrowle : ∑ j, ‖M i j‖ ≤ ∑ i, ∑ j, ‖M i j‖ :=
    Finset.single_le_sum (f := fun i => ∑ j, ‖M i j‖)
      (fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _) (Finset.mem_univ i)
  exact (le_of_mul_le_mul_right hbound hxi).trans hrowle

/-- `∏_k (t - v_k) = det (t - M)` when `v` lists the eigenvalues of `M`. -/
theorem prod_sub_eq_det {D : ℕ} {M : Matrix m m ℂ} {v : Fin D → ℂ}
    (hv : (univ : Finset (Fin D)).val.map v = M.charpoly.roots) (t : ℂ) :
    ∏ k, (t - v k) = ((-1 : ℂ) • M + t • (1 : Matrix m m ℂ)).det := by
  rw [det_smul_add_smul_one, ← hv, Multiset.map_map]
  simp only [Function.comp_def, neg_one_mul, neg_add_eq_sub]
  rfl

/-- Eigenvalues depend continuously on the matrix: near `β₀`, every listing of the eigenvalues
of `M(β)` is within `ε` of a permutation of a listing `u` of those of `M(β₀)`. -/
theorem eventually_exists_perm_close {M : ℝ → Matrix m m ℂ} {β₀ : ℝ}
    (hM : ContinuousAt M β₀) {D : ℕ} {u : Fin D → ℂ}
    (hu : (univ : Finset (Fin D)).val.map u = (M β₀).charpoly.roots) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ β in 𝓝 β₀, ∀ v : Fin D → ℂ, (univ : Finset (Fin D)).val.map v = (M β).charpoly.roots →
      ∃ σ : Equiv.Perm (Fin D), ∀ k, ‖v k - u (σ k)‖ < ε := by
  by_contra hcon
  rw [not_eventually] at hcon
  obtain ⟨βs, hβs, hbad⟩ := exists_seq_forall_of_frequently hcon
  push Not at hbad
  choose v hv hvbad using hbad
  -- the eigenvalue lists are eventually bounded
  set B : Matrix m m ℂ → ℝ := fun N => ∑ i, ∑ j, ‖N i j‖
  have hB : Continuous B := by fun_prop
  have hMs : Tendsto (fun n => M (βs n)) atTop (𝓝 (M β₀)) := hM.tendsto.comp hβs
  have hBev : ∀ᶠ n in atTop, B (M (βs n)) < B (M β₀) + 1 :=
    (hB.tendsto _ |>.comp hMs).eventually (gt_mem_nhds (by linarith))
  have hbdd : ∀ᶠ n in atTop, v n ∈ Metric.closedBall (0 : Fin D → ℂ) (B (M β₀) + 1) := by
    filter_upwards [hBev] with n hn
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (by positivity)]
    intro k
    have hk : v n k ∈ (M (βs n)).charpoly.roots := by
      rw [← hv n]; exact Multiset.mem_map_of_mem _ (mem_univ_val k)
    exact (norm_le_of_mem_roots_charpoly hk).trans hn.le
  obtain ⟨r, -, φ, hφ, hlim⟩ :=
    tendsto_subseq_of_frequently_bounded Metric.isBounded_closedBall hbdd.frequently
  -- the limit lists the eigenvalues of `M β₀`
  have hr : (univ : Finset (Fin D)).val.map r = (M β₀).charpoly.roots := by
    rw [← hu]
    apply multiset_eq_of_prod_sub_eq
    intro t
    simp only [Multiset.map_map, Function.comp_def]
    have h1 : Tendsto (fun n => ∏ k, (t - v (φ n) k)) atTop (𝓝 (∏ k, (t - r k))) :=
      tendsto_finset_prod _ fun k _ =>
        tendsto_const_nhds.sub ((continuous_apply k).continuousAt.tendsto.comp hlim)
    have hdet : Continuous fun N : Matrix m m ℂ => ((-1 : ℂ) • N + t • (1 : Matrix m m ℂ)).det :=
      (continuous_const.smul continuous_id |>.add continuous_const).matrix_det
    have h2 : Tendsto (fun n => ∏ k, (t - v (φ n) k)) atTop
        (𝓝 ((-1 : ℂ) • M β₀ + t • (1 : Matrix m m ℂ)).det) := by
      simp only [prod_sub_eq_det (hv _)]
      exact (hdet.tendsto _).comp (hMs.comp hφ.tendsto_atTop)
    have := tendsto_nhds_unique h1 h2
    rw [← prod_sub_eq_det hu] at this
    exact this
  obtain ⟨σ, hσ⟩ := exists_perm_of_map_eq (hr.trans hu.symm)
  -- far along the subsequence the matching `σ` works, contradicting the choice of `v`
  have hclose : ∀ᶠ n in atTop, ‖v (φ n) - r‖ < ε :=
    (tendsto_iff_norm_sub_tendsto_zero.mp hlim).eventually (gt_mem_nhds hε)
  obtain ⟨n, hn⟩ := hclose.exists
  obtain ⟨k, hk⟩ := hvbad (φ n) σ
  rw [hσ k] at hk
  exact absurd ((norm_le_pi_norm (v (φ n) - r) k).trans_lt hn) (not_lt.mpr hk)

end LeanUnitary.Pivot
