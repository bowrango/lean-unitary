import LeanUnitary.Pivot.Multiplexor.Phase
import LeanUnitary.Pivot.Existence.Rotation
import LeanUnitary.Pivot.Existence.EigenContinuity
import LeanUnitary.Pivot.Existence.PhaseList
import LeanUnitary.Pivot.Existence.Imbalance

/-!
# The pivot angles exist, and the extra CX merges

`submission/decomposition.tex`, Sec. II.C, assembled. For a pivot angle `α` with no `τ_k` real and
`N₊ = N₋`, let `ν(β)` be the normalized lift of the eigenphases of `C(β)` whose sum is the
continuous phase `σ(β)` of `det C(β)`.

* `exists_lift_sigma`, `continuousOn_lift`: `ν` exists and is continuous on `[0, π]`, from the
  continuity of eigenvalues, of `σ`, and the stability of normalized lifts;
* `exists_pivot_beta`: since `σ(π) = -σ(0)` and the phases of `C(π)` are those of `C(0)` negated,
  `ν(π) = -ν(0) ∘ rev`, so the intermediate value theorem gives `β*` with `φ = 0`;
* `exists_pivot`: `α*` exists when the eigenvalues of `X⁻¹ Y` have distinct crossing angles
  (`exists_rotation_half_upper`), so both pivot angles exist;
* `pivot_merge` (Eqs. 1–3): for generic `U`, the pivot `g = R_z(α*) R_y(β*)` is a single-qubit
  unitary, and the Block-ZXZ multiplexor of `U (g ⊗ I)` has demultiplexing angles with final
  Gray-code angle `φ = 0`, so the extra CX merges.
-/

namespace LeanUnitary.Pivot

open Matrix Complex Finset Filter Topology
open scoped ComplexOrder

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- For every `β`, the eigenphases of `C(β)` have a normalized lift with sum `σ(β)`. -/
theorem exists_lift_sigma (α : ℝ) {X Y : Matrix m m ℂ} (hX : IsUnit X.det)
    (hτ : ∀ τ ∈ taus α X Y, τ.im ≠ 0) {n : ℕ} (hcard : Fintype.card m = n + 1)
    (h4 : 4 ∣ Fintype.card m) (β : ℝ) :
    ∃ ν : Fin (n + 1) → ℝ, Normalized ν ∧ IsPhaseList (multiplexor α β X Y) ν ∧
      ∑ k, ν k = sigma α β X Y := by
  have hU := multiplexor_mem_unitaryGroup α β (isUnit_det_Xg α β hX Y hτ)
    (isUnit_det_Yg α β hX Y hτ)
  obtain ⟨w, hw⟩ := exists_phaseList hU hcard
  obtain ⟨k, hk⟩ := exists_int_of_exp_eq hw (exp_sigma α β hX hτ h4)
  obtain ⟨ν, hν, hres, hsum⟩ := exists_normalized_lift w k
  exact ⟨ν, hν, hw.of_sameResidues hres, by rw [hsum, hk]⟩

/-- A lift of the eigenphases of `C(β)` that is normalized and has sum `σ(β)` for every `β` is
continuous on `[0, π]`. -/
theorem continuousOn_lift (α : ℝ) {X Y : Matrix m m ℂ} (hX : IsUnit X.det)
    (hτ : ∀ τ ∈ taus α X Y, τ.im ≠ 0) {n : ℕ} (ν : ℝ → Fin (n + 1) → ℝ)
    (hνn : ∀ β, Normalized (ν β)) (hνp : ∀ β, IsPhaseList (multiplexor α β X Y) (ν β))
    (hνs : ∀ β, ∑ k, ν β k = sigma α β X Y) :
    ContinuousOn ν (Set.Icc 0 Real.pi) := by
  intro β₀ hβ₀
  rw [ContinuousWithinAt, Metric.tendsto_nhds]
  intro ε hε
  have hπ := Real.pi_pos
  set ε' := min (ε / 2) (Real.pi / (2 * (n + 1))) with hε'
  have hε'pos : 0 < ε' := lt_min (by linarith) (by positivity)
  have hε'le : ε' ≤ ε / 2 := min_le_left _ _
  have hDε : (n + 1) * ε' < Real.pi := by
    have : ε' ≤ Real.pi / (2 * (n + 1)) := min_le_right _ _
    calc (n + 1 : ℝ) * ε' ≤ (n + 1) * (Real.pi / (2 * (n + 1))) := by gcongr
      _ = Real.pi / 2 := by field_simp
      _ < Real.pi := by linarith
  obtain ⟨η, hη, hphase⟩ := exists_phase_close hε'pos
  -- eigenvalues near `β₀` are close to those at `β₀`
  have hroots := eventually_exists_perm_close
    (continuous_multiplexor α hX Y hτ).continuousAt (hνp β₀).symm hη
  -- `σ` is continuous
  have hsig : ∀ᶠ β in 𝓝[Set.Icc 0 Real.pi] β₀, |sigma α β X Y - sigma α β₀ X Y| < Real.pi := by
    have := Metric.tendsto_nhds.mp (continuousOn_sigma α X Y hτ β₀ hβ₀) Real.pi hπ
    simpa [Real.dist_eq] using this
  filter_upwards [nhdsWithin_le_nhds hroots, hsig] with β hβr hβs
  obtain ⟨σp, hσp⟩ := hβr (fun k => exp (ν β k * I)) (hνp β).symm
  -- lift the phases at `β` close to those at `β₀`
  have hlift : ∀ k, ∃ θ' : ℝ, exp (θ' * I) = exp (ν β k * I) ∧ |θ' - ν β₀ (σp k)| < ε' :=
    fun k => hphase (ν β₀ (σp k)) _ (norm_exp_ofReal_mul_I _) (hσp k)
  choose μ hμe hμc using hlift
  have hres : SameResidues μ (ν β) := ⟨Equiv.refl _, fun k => by
    obtain ⟨j, hj⟩ := exp_eq_exp_iff_exists_int.mp (hμe k).symm
    refine ⟨j, ?_⟩
    have := congrArg Complex.im hj
    simp at this
    simp only [Equiv.refl_apply]
    linarith⟩
  have hstable := normalized_lift_stable (hνn β₀) (hνn β) σp (fun k => (hμc k).le) hres
    (by rw [hνs, hνs]; linarith)
  rw [dist_pi_lt_iff hε]
  intro j
  rw [Real.dist_eq]
  linarith [hstable j]

/-- **Existence of `β*`** (Sec. II.C). Let `X`, `Y` be invertible `D × D` blocks with
`D = 4(q + 1)`, and let `α` be a pivot angle with no `τ_k` real and `N₊ = N₋`. Then for some
`β* ∈ [0, π]`, the eigenphases `μ` of `C(β*)` can be assigned to basis states, with branch shifts,
so that the final angle `φ` of the multiplexed rotation vanishes. -/
theorem exists_pivot_beta (α : ℝ) {X Y : Matrix m m ℂ} (hX : IsUnit X.det) (hY : IsUnit Y.det)
    (q : ℕ) (hcard : Fintype.card m = 4 * (q + 1)) (hτ : ∀ τ ∈ taus α X Y, τ.im ≠ 0)
    (hN : ((taus α X Y).filter fun τ => 0 < τ.im).card =
      ((taus α X Y).filter fun τ => ¬ 0 < τ.im).card) :
    ∃ β ∈ Set.Icc 0 Real.pi, ∃ μ : Fin (4 * (q + 1)) → ℝ,
      IsPhaseList (n := 4 * q + 3) (multiplexor α β X Y) μ ∧
      ∃ (e : Equiv.Perm (Fin (4 * (q + 1)))) (m' : Fin (4 * (q + 1)) → ℤ),
        walsh (topPlus (q + 1)) μ e m' = 0 := by
  have hcard' : Fintype.card m = 4 * q + 3 + 1 := by rw [hcard]; ring
  have h4 : 4 ∣ Fintype.card m := ⟨q + 1, hcard⟩
  choose ν hνn hνp hνs using exists_lift_sigma α hX hτ hcard' h4
  have hcont := continuousOn_lift α hX hτ ν hνn hνp hνs
  have hsum : ∑ k, ν Real.pi k = -∑ k, ν 0 k := by
    rw [hνs, hνs, sigma_pi_eq_neg α X Y hτ hN]
  -- the endpoint relation `ν(π) = -ν(0) ∘ rev`, from negated phases and a negated sum
  have hend := neg_rev_eq_of_lift (hνn 0) (hνn Real.pi)
    (multiplexor_phases_neg α hX hY (hνp 0) (hνp Real.pi)) hsum
  obtain ⟨β, hβ, e, m', h⟩ := exists_walsh_eq_zero_of_lift (Nat.succ_pos q) ν hcont hend
  exact ⟨β, hβ, ν β, hνp β, e, m', h⟩

/-- `exists_rotation_half_upper` for a list of any even length `D = 2r`. -/
theorem exists_rotation_half_upper' {D r : ℕ} (hD : D = 2 * r) (τ : Fin D → ℂ)
    (hτ : ∀ k, τ k ≠ 0)
    (hline : ∀ j k, j ≠ k → ∀ z : ℤ, arg (τ j) - arg (τ k) ≠ z * Real.pi) :
    ∃ α : ℝ, (∀ k, (exp (α * I) * τ k).im ≠ 0) ∧
      (univ.filter fun k => 0 < (exp (α * I) * τ k).im).card = r := by
  subst hD
  exact exists_rotation_half_upper τ hτ hline

/-- **The pivot exists** (Sec. II.C). Let `X`, `Y` be invertible `D × D` blocks, `D = 4(q + 1)`,
and let `u` list the eigenvalues of `X⁻¹ Y`, no two on a common line through the origin (distinct
crossing angles). Then there are pivot angles `α*`, `β* ∈ [0, π]` such that the eigenphases of
`C(β*)` can be assigned to basis states, with branch shifts, so that the final angle `φ` of the
multiplexed rotation vanishes, and the extra CX merges. -/
theorem exists_pivot {X Y : Matrix m m ℂ} (hX : IsUnit X.det) (hY : IsUnit Y.det) (q : ℕ)
    (hcard : Fintype.card m = 4 * (q + 1)) (u : Fin (4 * (q + 1)) → ℂ)
    (hu : (univ : Finset (Fin (4 * (q + 1)))).val.map u = (X⁻¹ * Y).charpoly.roots)
    (hline : ∀ j k, j ≠ k → ∀ z : ℤ, arg (u j) - arg (u k) ≠ z * Real.pi) :
    ∃ α : ℝ, ∃ β ∈ Set.Icc 0 Real.pi, ∃ μ : Fin (4 * (q + 1)) → ℝ,
      IsPhaseList (n := 4 * q + 3) (multiplexor α β X Y) μ ∧
      ∃ (e : Equiv.Perm (Fin (4 * (q + 1)))) (m' : Fin (4 * (q + 1)) → ℤ),
        walsh (topPlus (q + 1)) μ e m' = 0 := by
  -- the eigenvalues of `X⁻¹ Y` are nonzero
  have hu0 : ∀ k, u k ≠ 0 := fun k => by
    have hmem : u k ∈ taus 0 X Y := by
      rw [taus_eq_map, ofReal_zero, zero_mul, exp_zero]
      simp only [one_mul, Multiset.map_id']
      rw [← hu]; exact Multiset.mem_map_of_mem _ (mem_univ_val k)
    exact ne_zero_of_mem_taus 0 hX hY hmem
  obtain ⟨α, hreal, hcount⟩ := exists_rotation_half_upper' (r := 2 * (q + 1)) (by ring) u hu0 hline
  have htaus : taus α X Y = (univ : Finset (Fin (4 * (q + 1)))).val.map
      fun k => exp (α * I) * u k := by
    rw [taus_eq_map, ← hu, Multiset.map_map]; rfl
  have hτ : ∀ τ ∈ taus α X Y, τ.im ≠ 0 := fun τ hτ => by
    rw [htaus] at hτ
    obtain ⟨k, -, rfl⟩ := Multiset.mem_map.mp hτ
    exact hreal k
  have hpos : ((taus α X Y).filter fun τ => 0 < τ.im).card = 2 * (q + 1) := by
    rw [htaus, Multiset.filter_map, Multiset.card_map, ← hcount, Finset.card_def,
      Finset.filter_val]
    rfl
  have hneg : ((taus α X Y).filter fun τ => ¬ 0 < τ.im).card = 2 * (q + 1) := by
    have hsplit := congrArg Multiset.card
      (Multiset.filter_add_not (p := fun τ : ℂ => 0 < τ.im) (taus α X Y))
    rw [Multiset.card_add] at hsplit
    have htot : (taus α X Y).card = 4 * (q + 1) := by
      rw [htaus, Multiset.card_map, Finset.card_val, Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨β, hβ, μ, hμ, e, m', h⟩ :=
    exists_pivot_beta α hX hY q hcard hτ (hpos.trans hneg.symm)
  exact ⟨α, β, hβ, μ, hμ, e, m', h⟩

/-! ## The extra CX merges -/

/-- **The pivot allows the extra CX merge.** Let `U = [X Y; Z W]` have invertible `D × D` blocks
`X`, `Y`, `D = 4(q + 1)`, with the eigenvalues `u` of `X⁻¹ Y` at distinct crossing angles. Then
some pivot `g = R_z(α) R_y(β)`, `β ∈ [0, π]`, gives `U (g ⊗ I)` top blocks `X'`, `Y'` whose
Block-ZXZ multiplexor `C = zxzC X' Y'` has eigenvalues `e^{iθ_j}` with final angle `φ = 0`. -/
theorem pivot_merge {X Y Z W : Matrix m m ℂ} (hX : IsUnit X.det) (hY : IsUnit Y.det) (q : ℕ)
    (hcard : Fintype.card m = 4 * (q + 1)) (u : Fin (4 * (q + 1)) → ℂ)
    (hu : (univ : Finset (Fin (4 * (q + 1)))).val.map u = (X⁻¹ * Y).charpoly.roots)
    (hline : ∀ j k, j ≠ k → ∀ z : ℤ, arg (u j) - arg (u k) ≠ z * Real.pi) :
    ∃ α β : ℝ, β ∈ Set.Icc 0 Real.pi ∧ gate α β ∈ unitaryGroup (Fin 2) ℂ ∧
      ∃ X' Y' Z' W' : Matrix m m ℂ,
      fromBlocks X Y Z W * lift (gate α β) = fromBlocks X' Y' Z' W' ∧
      ∃ θ : Fin (4 * (q + 1)) → ℝ,
        (zxzC X' Y').charpoly.roots = (univ : Finset (Fin (4 * (q + 1)))).val.map
          (fun j => exp (θ j * I)) ∧
        finalAngle (q + 1) θ = 0 := by
  obtain ⟨α, β, hβ, μ, hμ, e, m', h⟩ := exists_pivot hX hY q hcard u hu hline
  refine ⟨α, β, hβ, gate_mem_unitaryGroup α β, _, _, _, _, fromBlocks_mul_lift α β X Y Z W,
    fun j => μ (e j) + 2 * Real.pi * m' j, ?_, ?_⟩
  · -- the shifted, reassigned phases list the same eigenvalues
    change (multiplexor α β X Y).charpoly.roots = _
    rw [hμ]
    have hexp : ∀ j, exp (((μ (e j) + 2 * Real.pi * m' j : ℝ)) * I) = exp (μ (e j) * I) :=
      fun j => by
        rw [show ((μ (e j) + 2 * Real.pi * m' j : ℝ) : ℂ) * I =
            μ (e j) * I + m' j * (2 * Real.pi * I) by push_cast; ring,
          exp_add, exp_int_mul_two_pi_mul_I, mul_one]
    rw [Multiset.map_congr rfl fun j _ => hexp j,
      show (fun j => exp (μ (e j) * I)) = (fun k => exp (μ k * I)) ∘ e from rfl,
      ← Multiset.map_map, Multiset.map_univ_val_equiv]
    rfl
  · -- `φ` is the Walsh sum, which vanishes
    rw [finalAngle, show ∑ j, walshSign (topPlus (q + 1)) j * (μ (e j) + 2 * Real.pi * m' j) =
      walsh (topPlus (q + 1)) μ e m' from rfl, h, mul_zero]

end LeanUnitary.Pivot
