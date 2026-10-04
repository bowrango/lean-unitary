import LeanUnitary.Pivot.Multiplexor.Continuity

/-!
# The phase of `det C(β)`

`submission/decomposition.tex`, Eqs. 12–14. The paper follows the continuous phase `σ(β)` of
`det C(β)` along the pivot path. This module constructs it explicitly. With `D` divisible by
four, `det C(β)` is a positive multiple of `det Y_g / det X_g = ∏_k (c τ_k - s)/(c + s τ_k)`
(Eq. 12). For nonreal `τ_k` and `β ∈ [0, π]`, both `c τ_k - s` and `c + s τ_k` stay in the closed
half-plane containing `τ_k` and never vanish, where a rotated `arg` (`halfPhase`) is continuous.
So

    σ(β) = Σ_k [halfPhase (c τ_k - s) - halfPhase (c + s τ_k)]

is a continuous phase of `det C(β)`:

* `continuousOn_sigma`: `σ` is continuous on `[0, π]`;
* `exp_sigma`: `e^{iσ(β)} = det C(β)`;
* `sigma_zero`, `sigma_pi`: `σ(0) = Σ_k arg τ_k` and `σ(π) = π (N₊ - N₋) - Σ_k arg τ_k` (Eq. 13);
* `sigma_pi_eq_neg`: with `N₊ = N₋`, `σ(π) = -σ(0)` (Eq. 14).
-/

namespace LeanUnitary.Pivot

open Matrix Complex
open scoped ComplexOrder

/-! ## A continuous phase on a closed half-plane -/

/-- A phase on the closed upper half-plane, continuous there away from `0`. -/
noncomputable def phaseUp (z : ℂ) : ℝ := arg (-I * z) + Real.pi / 2

/-- A phase on the closed lower half-plane, continuous there away from `0`. -/
noncomputable def phaseDn (z : ℂ) : ℝ := arg (I * z) - Real.pi / 2

/-- The phase adapted to the half-plane containing `τ`. -/
noncomputable def halfPhase (τ z : ℂ) : ℝ := if 0 < τ.im then phaseUp z else phaseDn z

theorem norm_mul_exp_phaseUp (z : ℂ) : (‖z‖ : ℂ) * exp (phaseUp z * I) = z := by
  have h := norm_mul_exp_arg_mul_I (-I * z)
  rw [norm_mul, norm_neg, norm_I, one_mul] at h
  rw [phaseUp, ofReal_add, add_mul, exp_add, ← mul_assoc, h, ofReal_div, ofReal_ofNat,
    exp_pi_div_two_mul_I]
  ring_nf; rw [I_sq]; ring

theorem norm_mul_exp_phaseDn (z : ℂ) : (‖z‖ : ℂ) * exp (phaseDn z * I) = z := by
  have h := norm_mul_exp_arg_mul_I (I * z)
  rw [norm_mul, norm_I, one_mul] at h
  rw [phaseDn, ofReal_sub, sub_mul, exp_sub, mul_div_assoc', h, ofReal_div, ofReal_ofNat,
    exp_pi_div_two_mul_I]
  field_simp

theorem norm_mul_exp_halfPhase (τ z : ℂ) : (‖z‖ : ℂ) * exp (halfPhase τ z * I) = z := by
  unfold halfPhase; split_ifs
  · exact norm_mul_exp_phaseUp z
  · exact norm_mul_exp_phaseDn z

theorem neg_I_mul_mem_slitPlane {z : ℂ} (hz : z ≠ 0) (him : 0 ≤ z.im) : -I * z ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  rcases him.lt_or_eq with h | h
  · left; simpa using h
  · right
    have e : (-I * z).im = -z.re := by simp
    rw [e]; intro h'
    exact hz (Complex.ext (by simp; linarith) (by simp; linarith))

theorem I_mul_mem_slitPlane {z : ℂ} (hz : z ≠ 0) (him : z.im ≤ 0) : I * z ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  rcases him.lt_or_eq with h | h
  · left; simpa using h
  · right
    have e : (I * z).im = z.re := by simp
    rw [e]; intro h'
    exact hz (Complex.ext (by simp; linarith) (by simp; linarith))

theorem continuousAt_phaseUp {z : ℂ} (hz : z ≠ 0) (him : 0 ≤ z.im) : ContinuousAt phaseUp z :=
  ((continuousAt_arg (neg_I_mul_mem_slitPlane hz him)).comp
    (continuous_const.mul continuous_id).continuousAt).add continuousAt_const

theorem continuousAt_phaseDn {z : ℂ} (hz : z ≠ 0) (him : z.im ≤ 0) : ContinuousAt phaseDn z :=
  ((continuousAt_arg (I_mul_mem_slitPlane hz him)).comp
    (continuous_const.mul continuous_id).continuousAt).sub continuousAt_const

/-- On the closed upper half-plane, `phaseUp` is `arg` (for `z ≠ 0`). -/
theorem phaseUp_eq_arg {z : ℂ} (hz : z ≠ 0) (him : 0 ≤ z.im) : phaseUp z = arg z := by
  have harg : 0 ≤ arg z := arg_nonneg_iff.mpr him
  have hle : arg z ≤ Real.pi := arg_le_pi z
  have hnz : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have h : -I * z = (‖z‖ : ℂ) * (Real.cos (arg z - Real.pi / 2) +
      Real.sin (arg z - Real.pi / 2) * I) := by
    conv_lhs => rw [← norm_mul_exp_arg_mul_I z]
    rw [Real.cos_sub_pi_div_two, Real.sin_sub_pi_div_two, ← cos_add_sin_I (arg z : ℂ)]
    push_cast; ring_nf; rw [I_sq]; ring
  rw [ofReal_cos, ofReal_sin] at h
  rw [phaseUp, h, arg_mul_cos_add_sin_mul_I hnz ⟨by linarith [Real.pi_pos], by linarith⟩]
  ring

/-- On the closed lower half-plane, `phaseDn` is `arg` (for `z` not on the negative axis). -/
theorem phaseDn_eq_arg {z : ℂ} (hz : z ≠ 0) (him : z.im < 0) : phaseDn z = arg z := by
  have harg : arg z < 0 := arg_neg_iff.mpr him
  have hle : -Real.pi < arg z := neg_pi_lt_arg z
  have hnz : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have h : I * z = (‖z‖ : ℂ) * (Real.cos (arg z + Real.pi / 2) +
      Real.sin (arg z + Real.pi / 2) * I) := by
    conv_lhs => rw [← norm_mul_exp_arg_mul_I z]
    rw [Real.cos_add_pi_div_two, Real.sin_add_pi_div_two, ← cos_add_sin_I (arg z : ℂ)]
    push_cast; ring_nf; rw [I_sq]; ring
  rw [ofReal_cos, ofReal_sin] at h
  rw [phaseDn, h, arg_mul_cos_add_sin_mul_I hnz ⟨by linarith, by linarith [Real.pi_pos]⟩]
  ring

theorem phaseUp_one : phaseUp 1 = 0 := by simp [phaseUp, arg_neg_I]

theorem phaseDn_one : phaseDn 1 = 0 := by simp [phaseDn, arg_I]

theorem phaseUp_neg_one : phaseUp (-1) = Real.pi := by simp [phaseUp, arg_I]

theorem phaseDn_neg_one : phaseDn (-1) = -Real.pi := by simp [phaseDn, arg_neg_I]; ring

/-! ## The continuous phase `σ(β)` -/

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- The numerator factor `c τ - s` of Eq. 12. -/
noncomputable def numF (β : ℝ) (τ : ℂ) : ℂ := (Real.cos (β / 2) : ℂ) * τ - (Real.sin (β / 2) : ℂ)

/-- The denominator factor `c + s τ` of Eq. 12. -/
noncomputable def denF (β : ℝ) (τ : ℂ) : ℂ := (Real.cos (β / 2) : ℂ) + (Real.sin (β / 2) : ℂ) * τ

/-- The continuous phase of `det C(β)`: `σ(β) = Σ_k [phase (c τ_k - s) - phase (c + s τ_k)]`. -/
noncomputable def sigma (α β : ℝ) (X Y : Matrix m m ℂ) : ℝ :=
  ((taus α X Y).map fun τ => halfPhase τ (numF β τ) - halfPhase τ (denF β τ)).sum

theorem numF_ne_zero (β : ℝ) {τ : ℂ} (hτ : τ.im ≠ 0) : numF β τ ≠ 0 :=
  (add_mul_ne_zero_and_mul_sub_ne_zero (Real.cos_sq_add_sin_sq _) hτ).2

theorem denF_ne_zero (β : ℝ) {τ : ℂ} (hτ : τ.im ≠ 0) : denF β τ ≠ 0 :=
  (add_mul_ne_zero_and_mul_sub_ne_zero (Real.cos_sq_add_sin_sq _) hτ).1

theorem cos_half_nonneg {β : ℝ} (hβ : β ∈ Set.Icc 0 Real.pi) : 0 ≤ Real.cos (β / 2) :=
  Real.cos_nonneg_of_mem_Icc ⟨by linarith [hβ.1, Real.pi_pos], by linarith [hβ.2]⟩

theorem sin_half_nonneg {β : ℝ} (hβ : β ∈ Set.Icc 0 Real.pi) : 0 ≤ Real.sin (β / 2) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hβ.1]) (by linarith [hβ.2, Real.pi_pos])

theorem im_numF (β : ℝ) (τ : ℂ) : (numF β τ).im = Real.cos (β / 2) * τ.im := by
  simp only [numF, sub_im, mul_im, ofReal_re, ofReal_im]; ring

theorem im_denF (β : ℝ) (τ : ℂ) : (denF β τ).im = Real.sin (β / 2) * τ.im := by
  simp only [denF, add_im, mul_im, ofReal_re, ofReal_im]; ring

theorem continuous_numF (τ : ℂ) : Continuous fun β => numF β τ := by unfold numF; fun_prop

theorem continuous_denF (τ : ℂ) : Continuous fun β => denF β τ := by unfold denF; fun_prop

/-- On `[0, π]`, the phase of a factor that stays in the closed half-plane of `τ` is continuous. -/
theorem continuousOn_halfPhase {τ : ℂ} (hτ : τ.im ≠ 0) {g : ℝ → ℂ} (hg : Continuous g)
    (hne : ∀ β ∈ Set.Icc 0 Real.pi, g β ≠ 0)
    (hside : ∀ β ∈ Set.Icc 0 Real.pi, 0 ≤ (g β).im * τ.im) :
    ContinuousOn (fun β => halfPhase τ (g β)) (Set.Icc 0 Real.pi) := by
  refine continuousOn_of_forall_continuousAt fun β hβ => ?_
  have hg0 := hne β hβ
  have hs := hside β hβ
  unfold halfPhase
  by_cases hpos : 0 < τ.im
  · simp only [if_pos hpos]
    have : 0 ≤ (g β).im := by by_contra h; push Not at h; nlinarith
    exact (continuousAt_phaseUp hg0 this).comp hg.continuousAt
  · simp only [if_neg hpos]
    have hneg : τ.im < 0 := lt_of_le_of_ne (not_lt.mp hpos) hτ
    have : (g β).im ≤ 0 := by by_contra h; push Not at h; nlinarith
    exact (continuousAt_phaseDn hg0 this).comp hg.continuousAt

/-- `σ` is continuous on `[0, π]` when no `τ_k` is real. -/
theorem continuousOn_sigma (α : ℝ) (X Y : Matrix m m ℂ) (hτ : ∀ τ ∈ taus α X Y, τ.im ≠ 0) :
    ContinuousOn (fun β => sigma α β X Y) (Set.Icc 0 Real.pi) := by
  unfold sigma
  refine continuousOn_multiset_sum _ fun τ hτm => ?_
  have h := hτ τ hτm
  refine ContinuousOn.sub ?_ ?_
  · refine continuousOn_halfPhase h (continuous_numF τ) (fun β _ => numF_ne_zero β h)
      fun β hβ => ?_
    rw [im_numF]; have := cos_half_nonneg hβ; nlinarith [sq_nonneg τ.im]
  · refine continuousOn_halfPhase h (continuous_denF τ) (fun β _ => denF_ne_zero β h)
      fun β hβ => ?_
    rw [im_denF]; have := sin_half_nonneg hβ; nlinarith [sq_nonneg τ.im]

/-- `σ(0) = Σ_k arg τ_k`. -/
theorem sigma_zero (α : ℝ) (X Y : Matrix m m ℂ) (hτ : ∀ τ ∈ taus α X Y, τ.im ≠ 0) :
    sigma α 0 X Y = ((taus α X Y).map fun τ => arg τ).sum := by
  unfold sigma
  congr 1
  refine Multiset.map_congr rfl fun τ hτm => ?_
  have h := hτ τ hτm
  have hτ0 : τ ≠ 0 := fun h0 => h (by simp [h0])
  simp only [numF, denF, zero_div, Real.cos_zero, Real.sin_zero, ofReal_one, ofReal_zero, one_mul,
    sub_zero, zero_mul, add_zero, halfPhase]
  split_ifs with hpos
  · rw [phaseUp_eq_arg hτ0 hpos.le, phaseUp_one, sub_zero]
  · have hneg : τ.im < 0 := lt_of_le_of_ne (not_lt.mp hpos) h
    rw [phaseDn_eq_arg hτ0 hneg, phaseDn_one, sub_zero]

/-- Eq. 13: `σ(π) = π (N₊ - N₋) - Σ_k arg τ_k`, written as a sum of `±π - arg τ_k`. -/
theorem sigma_pi (α : ℝ) (X Y : Matrix m m ℂ) (hτ : ∀ τ ∈ taus α X Y, τ.im ≠ 0) :
    sigma α Real.pi X Y =
      ((taus α X Y).map fun τ => (if 0 < τ.im then Real.pi else -Real.pi) - arg τ).sum := by
  unfold sigma
  congr 1
  refine Multiset.map_congr rfl fun τ hτm => ?_
  have h := hτ τ hτm
  have hτ0 : τ ≠ 0 := fun h0 => h (by simp [h0])
  simp only [numF, denF, Real.cos_pi_div_two, Real.sin_pi_div_two, ofReal_one, ofReal_zero,
    zero_mul, zero_sub, zero_add, one_mul, halfPhase]
  split_ifs with hpos
  · rw [phaseUp_neg_one, phaseUp_eq_arg hτ0 hpos.le]
  · have hneg : τ.im < 0 := lt_of_le_of_ne (not_lt.mp hpos) h
    rw [phaseDn_neg_one, phaseDn_eq_arg hτ0 hneg]

/-- Eq. 14: with `N₊ = N₋`, `σ(π) = -σ(0)`. -/
theorem sigma_pi_eq_neg (α : ℝ) (X Y : Matrix m m ℂ) (hτ : ∀ τ ∈ taus α X Y, τ.im ≠ 0)
    (hN : ((taus α X Y).filter fun τ => 0 < τ.im).card =
      ((taus α X Y).filter fun τ => ¬ 0 < τ.im).card) :
    sigma α Real.pi X Y = -sigma α 0 X Y := by
  have hite : ((taus α X Y).map fun τ => if 0 < τ.im then Real.pi else -Real.pi).sum = 0 := by
    conv_lhs => rw [← Multiset.filter_add_not (p := fun τ : ℂ => 0 < τ.im) (taus α X Y)]
    rw [Multiset.map_add, Multiset.sum_add,
      Multiset.map_congr rfl fun τ (hτ' : τ ∈ (taus α X Y).filter fun τ : ℂ => 0 < τ.im) =>
        if_pos (Multiset.mem_filter.mp hτ').2,
      Multiset.map_congr rfl fun τ (hτ' : τ ∈ (taus α X Y).filter fun τ : ℂ => ¬ 0 < τ.im) =>
        if_neg (Multiset.mem_filter.mp hτ').2]
    simp only [Multiset.map_const', Multiset.sum_replicate, nsmul_eq_mul, hN]
    ring
  rw [sigma_pi α X Y hτ, sigma_zero α X Y hτ, Multiset.sum_map_sub, hite, zero_sub]

/-! ## `e^{iσ(β)} = det C(β)` -/

/-- `det A^{-1/2}` is a nonnegative real for Hermitian `A`. -/
theorem det_invSqrt {A : Matrix m m ℂ} (hA : A.IsHermitian) :
    ∃ r : ℝ, 0 ≤ r ∧ (invSqrt A).det = r := by
  refine ⟨∏ i, (Real.sqrt (hA.eigenvalues i))⁻¹,
    Finset.prod_nonneg fun i _ => inv_nonneg.mpr (Real.sqrt_nonneg _), ?_⟩
  have hU : (hA.eigenvectorUnitary : Matrix m m ℂ) * star (hA.eigenvectorUnitary : Matrix m m ℂ)
      = 1 := Unitary.mul_star_self_of_mem hA.eigenvectorUnitary.2
  have hdetU := congrArg det hU
  rw [det_mul, det_one] at hdetU
  rw [invSqrt, hA.cfc_eq, IsHermitian.cfc, Unitary.conjStarAlgAut_apply, det_mul, det_mul,
    det_diagonal]
  rw [mul_comm, ← mul_assoc, mul_comm (det (star _)), hdetU, one_mul]
  push_cast
  exact Finset.prod_congr rfl fun i _ => by simp

theorem ofReal_multiset_sum' (s : Multiset ℝ) :
    ((s.sum : ℝ) : ℂ) = (s.map fun x : ℝ => ((x : ℝ) : ℂ)).sum :=
  map_multiset_sum Complex.ofRealHom s

theorem ofReal_multiset_prod' (s : Multiset ℝ) :
    ((s.prod : ℝ) : ℂ) = (s.map fun x : ℝ => ((x : ℝ) : ℂ)).prod :=
  map_multiset_prod Complex.ofRealHom s

/-- A complex number of norm one that is a nonnegative multiple of `e^{iθ}` equals `e^{iθ}`. -/
theorem eq_exp_of_norm_eq_one {z : ℂ} {ρ θ : ℝ} (hρ : 0 ≤ ρ) (hz : z = ρ * exp (θ * I))
    (hn : ‖z‖ = 1) : z = exp (θ * I) := by
  have : ρ = 1 := by
    rw [hz, norm_mul, norm_exp_ofReal_mul_I, mul_one, norm_real, Real.norm_of_nonneg hρ] at hn
    exact hn
  rw [hz, this, ofReal_one, one_mul]

/-- `conj(c + s τ) (c τ - s) = |c + s τ| |c τ - s| e^{i (phase (c τ - s) - phase (c + s τ))}`. -/
theorem star_denF_mul_numF (β : ℝ) (τ : ℂ) :
    star (denF β τ) * numF β τ = ((‖denF β τ‖ * ‖numF β τ‖ : ℝ) : ℂ) *
      exp (((halfPhase τ (numF β τ) - halfPhase τ (denF β τ) : ℝ)) * I) := by
  set d := denF β τ
  set n := numF β τ
  have hd := norm_mul_exp_halfPhase τ d
  have hn := norm_mul_exp_halfPhase τ n
  have hstar : star (exp (halfPhase τ d * I)) = exp (-(halfPhase τ d * I)) := by
    rw [Complex.star_def, ← exp_conj, map_mul, conj_ofReal, conj_I, mul_neg]
  conv_lhs => rw [← hd, ← hn]
  rw [star_mul', hstar, Complex.star_def, conj_ofReal]
  rw [show ((halfPhase τ n - halfPhase τ d : ℝ) : ℂ) * I = halfPhase τ n * I + -(halfPhase τ d * I)
    by push_cast; ring, exp_add]
  push_cast
  ring

/-- `det C(β) = e^{iσ(β)}` when `D` is divisible by four, `X` is invertible and no `τ_k` is real. -/
theorem exp_sigma (α β : ℝ) {X Y : Matrix m m ℂ} (hX : IsUnit X.det)
    (hτ : ∀ τ ∈ taus α X Y, τ.im ≠ 0) (h4 : 4 ∣ Fintype.card m) :
    exp (sigma α β X Y * I) = (multiplexor α β X Y).det := by
  set K := star (ph α) ^ Fintype.card m * X.det
  have hXg : (Xg α β X Y).det = K * ((taus α X Y).map (denF β)).prod := det_Xg_eq_prod α β hX Y
  have hYg : (Yg α β X Y).det = K * ((taus α X Y).map (numF β)).prod := det_Yg_eq_prod α β hX Y
  obtain ⟨r₁, hr₁, hd₁⟩ := det_invSqrt (isHermitian_mul_conjTranspose_self (Xg α β X Y))
  obtain ⟨r₂, hr₂, hd₂⟩ := det_invSqrt (isHermitian_mul_conjTranspose_self (Yg α β X Y))
  have hI : (-I) ^ Fintype.card m = 1 := by
    obtain ⟨k, hk⟩ := h4
    rw [hk, pow_mul, show (-I) ^ 4 = 1 by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, neg_sq, I_sq]; norm_num, one_pow]
  -- the product of the factors in polar form
  have hprod : star ((taus α X Y).map (denF β)).prod * ((taus α X Y).map (numF β)).prod =
      (((taus α X Y).map fun τ => ‖denF β τ‖ * ‖numF β τ‖).prod : ℝ) *
        exp (sigma α β X Y * I) := by
    rw [show star ((taus α X Y).map (denF β)).prod =
        ((taus α X Y).map fun τ => star (denF β τ)).prod by
          rw [Complex.star_def, map_multiset_prod, Multiset.map_map]; rfl,
      ← Multiset.prod_map_mul]
    simp only [star_denF_mul_numF]
    rw [Multiset.prod_map_mul, sigma, ofReal_multiset_sum', Multiset.map_map,
      ← Multiset.sum_map_mul_right, exp_multiset_sum, Multiset.map_map, ofReal_multiset_prod',
      Multiset.map_map]
    rfl
  have hdet : (multiplexor α β X Y).det =
      ((r₁ * r₂ * ‖K‖ ^ 2 * ((taus α X Y).map fun τ => ‖denF β τ‖ * ‖numF β τ‖).prod : ℝ) : ℂ) *
        exp (sigma α β X Y * I) := by
    rw [multiplexor, zxzC, det_smul, det_mul, det_mul, det_mul, det_conjTranspose, hd₁, hd₂, hI,
      hXg, hYg, star_mul']
    rw [show star K * star ((taus α X Y).map (denF β)).prod * ↑r₁ * ↑r₂ *
        (K * ((taus α X Y).map (numF β)).prod) = (r₁ * r₂ : ℂ) * (star K * K) *
        (star ((taus α X Y).map (denF β)).prod * ((taus α X Y).map (numF β)).prod) by ring]
    rw [hprod, Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  have hunit : ‖(multiplexor α β X Y).det‖ = 1 := CStarRing.norm_of_mem_unitary (det_of_mem_unitary
    (multiplexor_mem_unitaryGroup α β (isUnit_det_Xg α β hX Y hτ) (isUnit_det_Yg α β hX Y hτ)))
  refine (eq_exp_of_norm_eq_one ?_ hdet hunit).symm
  have : 0 ≤ ((taus α X Y).map fun τ => ‖denF β τ‖ * ‖numF β τ‖).prod :=
    Multiset.prod_nonneg fun x hx => by
      obtain ⟨τ, -, rfl⟩ := Multiset.mem_map.mp hx
      positivity
  positivity

end LeanUnitary.Pivot
