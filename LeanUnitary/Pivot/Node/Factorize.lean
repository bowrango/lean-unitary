import LeanUnitary.Pivot.Node.Glue
import LeanUnitary.Pivot.Existence.Pivot

/-!
# The pivoted node

The circuit-level form of the paper's Sec. II: for a generic `(n + 1)`-qubit unitary `U`,
`n = k + 2 ≥ 2`, there is a pivot gate `g` on the top qubit such that

    U (g ⊗ I) = (V_a ⊕ V_a) · R_a · (V_b ⊕ V_b) · M · (W_b ⊕ W_b) · R_c · (W_c ⊕ W_c),

with `n`-qubit unitaries `V_a, V_b, W_b, W_c` and circuits of top-qubit gates `R_a`, `M`, `R_c` of
`2^n - 1`, `2^n` and `2^n - 2` CNOTs (`node_factor`). Block-ZXZ has `2^n - 1` CNOTs in the
left-side multiplexor `R_c`; the pivot (`pivot_merge`) makes its final angle vanish, so the Gray
code circuit ends `CX_0, R_z(0), CX_{n-1}` (`core_split`) and *both* CNOTs merge into the central
multiplexor through `CX_c = (H ⊗ I)(I ⊕ Z_c)(H ⊗ I)`, replacing `B` by
`Z_{n-1} W_a B V_c Z_{n-1} Z_0`
before it is demultiplexed. The Block-ZXZ factorization (`exists_zxz_factor`) and demultiplexing
(`demux`, `demux_of_phases`) are proved, not assumed.
-/

namespace LeanUnitary.Pivot.Node

open Matrix Complex LeanUnitary.Spec LeanUnitary.Blocks LeanUnitary.Circuit Finset

/-! ## `g ⊗ I` -/

section lift
variable {m : Type*} [Fintype m] [DecidableEq m]

theorem lift_mul (g h : Matrix (Fin 2) (Fin 2) ℂ) :
    (Pivot.lift g : Matrix (m ⊕ m) (m ⊕ m) ℂ) * Pivot.lift h = Pivot.lift (g * h) := by
  rw [Pivot.lift, Pivot.lift, Pivot.lift, fromBlocks_multiply]
  simp only [smul_mul_smul, Matrix.mul_one, ← add_smul, Matrix.mul_apply, Fin.sum_univ_two]

omit [Fintype m] in
theorem lift_one : (Pivot.lift 1 : Matrix (m ⊕ m) (m ⊕ m) ℂ) = 1 := by
  rw [Pivot.lift, ← fromBlocks_one]; simp

omit [Fintype m] in
theorem star_lift (g : Matrix (Fin 2) (Fin 2) ℂ) :
    star (Pivot.lift g : Matrix (m ⊕ m) (m ⊕ m) ℂ) = Pivot.lift (star g) := by
  rw [Pivot.lift, Pivot.lift, star_eq_conjTranspose, fromBlocks_conjTranspose]
  simp [conjTranspose_smul]

theorem lift_mem {g : Matrix (Fin 2) (Fin 2) ℂ} (hg : g ∈ unitaryGroup (Fin 2) ℂ) :
    (Pivot.lift g : Matrix (m ⊕ m) (m ⊕ m) ℂ) ∈ unitaryGroup (m ⊕ m) ℂ := by
  rw [mem_unitaryGroup_iff, star_lift, lift_mul, mem_unitaryGroup_iff.mp hg, lift_one]

end lift

/-! ## Genericity -/

/-- A generic node (the paper's assumption, Sec. II.C): the top blocks `X`, `Y` of `U` are
invertible and the eigenvalues of `X⁻¹ Y` have distinct crossing angles. -/
def Generic {n : ℕ} (U : Op (n + 1)) : Prop :=
  IsUnit (topBlocks U).toBlocks₁₁.det ∧ IsUnit (topBlocks U).toBlocks₁₂.det ∧
    ∃ u : Fin (2 ^ n) → ℂ,
      (univ : Finset (Fin (2 ^ n))).val.map u =
        ((topBlocks U).toBlocks₁₁⁻¹ * (topBlocks U).toBlocks₁₂).charpoly.roots ∧
      ∀ j k, j ≠ k → ∀ z : ℤ, arg (u j) - arg (u k) ≠ z * Real.pi

/-! ## The final angle -/

theorem sum_fin_eq_sum_range {N : ℕ} (θ : Fin N → ℝ) (f : ℕ → ℝ) (hf : ∀ k : Fin N, f k = θ k) :
    ∑ j, θ j = ∑ x ∈ range N, f x := by
  rw [← Fin.sum_univ_eq_sum_range]; exact Finset.sum_congr rfl fun k _ => (hf k).symm

/-- The paper's final angle (Eq. 3, `finalAngle`) is the last Gray-code angle of `core`. -/
theorem firstAngle_minus_eq_zero {k q : ℕ} (hq : 4 * (q + 1) = 2 ^ (k + 2))
    (θ : Fin (4 * (q + 1)) → ℝ) (h : finalAngle (q + 1) θ = 0) :
    firstAngle (k + 1) (minus (k + 1) (extθ (θ ∘ Fin.cast hq.symm))) = 0 := by
  set ψ := extθ (θ ∘ Fin.cast hq.symm) with hψ
  have hψθ : ∀ j : Fin (4 * (q + 1)), ψ j = θ j := fun j => by
    rw [hψ, extθ, dif_pos (hq ▸ j.isLt)]; rfl
  have hsum : ∑ j, walshSign (topPlus (q + 1)) j * θ j =
      ∑ x ∈ range (2 ^ (k + 2)), (if x < 2 ^ (k + 1) then 1 else -1) * ψ x := by
    rw [← hq]
    apply sum_fin_eq_sum_range
    intro j
    rw [hψθ, walshSign, topPlus]
    congr 1
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have : 2 * (q + 1) = 2 ^ (k + 1) := by rw [pow_succ] at hq ⊢; omega
    rw [this]
  have hsplit : ∑ x ∈ range (2 ^ (k + 2)), (if x < 2 ^ (k + 1) then 1 else -1) * ψ x =
      ∑ y ∈ range (2 ^ (k + 1)), (ψ y - ψ (2 ^ (k + 1) + y)) := by
    rw [show 2 ^ (k + 2) = 2 ^ (k + 1) + 2 ^ (k + 1) by ring, Finset.sum_range_add,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun y hy => ?_
    have hy' := Finset.mem_range.mp hy
    rw [if_pos hy', if_neg (by omega)]; ring
  rw [firstAngle_eq]
  have hfa : finalAngle (q + 1) θ =
      (1 / (4 * (q + 1) : ℝ)) * ∑ j, walshSign (topPlus (q + 1)) j * θ j := by
    rw [finalAngle]; push_cast; ring
  rw [hfa, hsum, hsplit] at h
  have hq' : (0 : ℝ) < 4 * (q + 1) := by positivity
  have h0 : ∑ y ∈ range (2 ^ (k + 1)), (ψ y - ψ (2 ^ (k + 1) + y)) = 0 := by
    rcases mul_eq_zero.mp h with h | h
    · exfalso; rw [one_div, inv_eq_zero] at h; linarith
    · exact h
  have : ∑ y ∈ range (2 ^ (k + 1)), minus (k + 1) ψ y =
      (∑ y ∈ range (2 ^ (k + 1)), (ψ y - ψ (2 ^ (k + 1) + y))) / 2 := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [minus, Nat.mod_eq_of_lt (Finset.mem_range.mp hy), add_comm y]
  rw [this, h0]; simp


/-! ## The merge into the central multiplexor -/

section middle
variable {m : Type*} [Fintype m] [DecidableEq m]

theorem fromBlocks_dup_comm_hBlk (W : Matrix m m ℂ) :
    fromBlocks W 0 0 W * (hBlk : Matrix (m ⊕ m) (m ⊕ m) ℂ) = hBlk * fromBlocks W 0 0 W := by
  rw [hBlk_eq, fromBlocks_multiply, fromBlocks_multiply]
  simp

/-- **The merge.** The CNOTs `CX_{n-1}` (from the right-side multiplexor) and `CX_{n-1} CX_0` (from
the pivoted left-side multiplexor) pass into the central block as `Z_{n-1}` and `Z_{n-1} Z_0`. -/
theorem middle_eq (Wa Vc B zT z0 : Matrix m m ℂ) :
    (hBlk * fromBlocks 1 0 0 zT * hBlk) * fromBlocks Wa 0 0 Wa *
      (hBlk * fromBlocks 1 0 0 B * hBlk) * fromBlocks Vc 0 0 Vc *
        (hBlk * fromBlocks 1 0 0 zT * hBlk) * (hBlk * fromBlocks 1 0 0 z0 * hBlk) =
    hBlk * fromBlocks (Wa * Vc) 0 0 (zT * Wa * B * Vc * zT * z0) * hBlk := by
  have hh : ∀ X : Matrix (m ⊕ m) (m ⊕ m) ℂ, hBlk * (hBlk * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hBlk_mul_hBlk, Matrix.one_mul]
  have hc : ∀ (W : Matrix m m ℂ) (X : Matrix (m ⊕ m) (m ⊕ m) ℂ),
      fromBlocks W 0 0 W * (hBlk * X) = hBlk * (fromBlocks W 0 0 W * X) := fun W X => by
    rw [← Matrix.mul_assoc, fromBlocks_dup_comm_hBlk, Matrix.mul_assoc]
  have inner : fromBlocks (Wa * Vc) 0 0 (zT * Wa * B * Vc * zT * z0) =
      fromBlocks 1 0 0 zT * (fromBlocks Wa 0 0 Wa * (fromBlocks 1 0 0 B * (fromBlocks Vc 0 0 Vc *
        (fromBlocks 1 0 0 zT * fromBlocks (1 : Matrix m m ℂ) 0 0 z0)))) := by
    simp only [fromBlocks_multiply]; simp [Matrix.mul_assoc]
  rw [inner]
  simp only [Matrix.mul_assoc, hh, hc]

end middle

theorem map_univ_comp_equiv {α β γ : Type*} [Fintype α] [Fintype β] (e : α ≃ β) (f : β → γ) :
    (univ : Finset α).val.map (f ∘ e) = (univ : Finset β).val.map f := by
  rw [← Multiset.map_map, Multiset.map_univ_val_equiv]

/-! ## The node -/

/-- **The pivoted node** (circuit form of Sec. II): a generic `(n + 1)`-qubit unitary, `n = k + 2`,
is `(V_a ⊕ V_a) R_a (V_b ⊕ V_b) M (W_b ⊕ W_b) R_c (W_c ⊕ W_c) (g ⊗ I)ᴴ` with top-qubit circuits
`R_a`, `M`, `R_c` of `2^n - 1`, `2^n` and `2^n - 2` CNOTs. -/
theorem node_factor (k : ℕ) (U : Op (k + 2 + 1)) (hU : U ∈ unitaryGroup (Fin (2 ^ (k + 2 + 1))) ℂ)
    (hgen : Generic U) :
    ∃ g : unitaryGroup (Fin 2) ℂ, ∃ Va Vb Wb Wc : Op (k + 2),
      Va ∈ unitaryGroup _ ℂ ∧ Vb ∈ unitaryGroup _ ℂ ∧ Wb ∈ unitaryGroup _ ℂ ∧
      Wc ∈ unitaryGroup _ ℂ ∧
      ∃ Ra Mid Rc : Circuit (k + 2 + 1), TopGates Ra ∧ TopGates Mid ∧ TopGates Rc ∧
        Ra.cnotCount = 2 ^ (k + 2) - 1 ∧ Mid.cnotCount = 2 ^ (k + 2) ∧
        Rc.cnotCount = 2 ^ (k + 2) - 2 ∧
        U * (Gate.single (Fin.last (k + 2)) g).denote =
          dup Va * Ra.denote * dup Vb * Mid.denote * dup Wb * Rc.denote * dup Wc := by
  obtain ⟨hX, hY, u, hu, hline⟩ := hgen
  set M := topBlocks U with hMdef
  have hMm : M ∈ unitaryGroup _ ℂ := (ofBlocks_mem_iff M).mp (by rw [ofBlocks_topBlocks]; exact hU)
  have hM : M = fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂ :=
    (fromBlocks_toBlocks M).symm
  -- the pivot (Sec. II.C), on `D = 4(q + 1) = 2^n` basis states
  have hq : 4 * (2 ^ k - 1 + 1) = 2 ^ (k + 2) := by
    have := Nat.one_le_two_pow (n := k); rw [pow_add]; omega
  have hcard : Fintype.card (Fin (2 ^ (k + 2))) = 4 * (2 ^ k - 1 + 1) := by simp [hq]
  have hu' : (univ : Finset (Fin (4 * (2 ^ k - 1 + 1)))).val.map (u ∘ finCongr hq) =
      (M.toBlocks₁₁⁻¹ * M.toBlocks₁₂).charpoly.roots := by rw [map_univ_comp_equiv]; exact hu
  have hline' : ∀ j l : Fin (4 * (2 ^ k - 1 + 1)), j ≠ l → ∀ z : ℤ,
      arg ((u ∘ finCongr hq) j) - arg ((u ∘ finCongr hq) l) ≠ z * Real.pi :=
    fun j l hjl z => hline _ _ (fun e => hjl ((finCongr hq).injective e)) z
  obtain ⟨α, β, -, hg, X', Y', Z', W', hXY', hX', hY', θ, hθ, hfin⟩ :=
    pivot_merge (Z := M.toBlocks₂₁) (W := M.toBlocks₂₂) hX hY (2 ^ k - 1) hcard _ hu' hline'
  -- Block-ZXZ of `U (g ⊗ I)` (Sec. 4.1 of Krol–Al-Ars)
  have hM'm : fromBlocks X' Y' Z' W' ∈ unitaryGroup _ ℂ := by
    rw [← hXY', ← hM]; exact Submonoid.mul_mem _ hMm (lift_mem hg)
  obtain ⟨A₁, hA₁, A₂, hA₂, B, hB, hfac⟩ := exists_zxz_factor hM'm hX' hY'
  have hCm := zxzC_mem_unitaryGroup hX' hY'
  -- demultiplex the three multiplexors; the left one with the pivot's phases
  set θc : Fin (2 ^ (k + 2)) → ℝ := θ ∘ finCongr hq.symm with hθcdef
  have hθc : (univ : Finset (Fin (2 ^ (k + 2)))).val.map (fun x => exp (θc x * I)) =
      (zxzC X' Y').charpoly.roots := by
    rw [hθ, hθcdef]
    exact map_univ_comp_equiv (finCongr hq.symm) (fun j => exp (θ j * I))
  obtain ⟨Vc, hVc, Wc, hWc, hdc⟩ := demux_of_phases hCm θc hθc
  obtain ⟨Va, hVa, Wa, hWa, θa, hda⟩ := demux hA₁ hA₂
  set zT := zc (⟨k + 1, by omega⟩ : Fin (k + 2)) with hzT
  set z0 := zc (⟨0, by omega⟩ : Fin (k + 2)) with hz0
  have hP : Wa * Vc ∈ unitaryGroup _ ℂ := Submonoid.mul_mem _ hWa hVc
  have hQ : zT * Wa * B * Vc * zT * z0 ∈ unitaryGroup _ ℂ :=
    Submonoid.mul_mem _ (Submonoid.mul_mem _ (Submonoid.mul_mem _ (Submonoid.mul_mem _
      (Submonoid.mul_mem _ (zc_mem _) hWa) hB) hVc) (zc_mem _)) (zc_mem _)
  obtain ⟨Vb, hVb, Wb, hWb, θb, hdb⟩ := demux hP hQ
  -- the Gray-code circuits
  obtain ⟨Rc, hcore, hRc⟩ := core_split k (extθ θc)
  have hφ : firstAngle (k + 1) (minus (k + 1) (extθ θc)) = 0 := firstAngle_minus_eq_zero hq θ hfin
  set Ra : Circuit (k + 2 + 1) := (core (k + 2) (k + 2) le_rfl (extθ θa)).reverse with hRadef
  set Gb : Circuit (k + 2 + 1) := grayMux (k + 2) (by omega) (extθ θb) with hGb
  set Mid : Circuit (k + 2 + 1) := [hTop (k + 2)] ++ Gb ++ [hTop (k + 2)] with hMid
  refine ⟨⟨_, hg⟩, Va, Vb, Wb, Wc, hVa, hVb, hWb, hWc, Ra, Mid, Rc, (topGates_core _ _ _).reverse,
    ((topGates_hTop.append ((topGates_core _ _ _).append (topGates_cxTop _))).append topGates_hTop),
    fun g hg => topGates_core _ _ (extθ θc) g (by rw [hcore]; exact List.mem_append_left _ hg),
    by rw [hRadef, cnotCount_reverse, cnotCount_core],
    by rw [hMid, cnotCount_append, cnotCount_append, hGb, cnotCount_grayMux, cnotCount_hTop]; simp,
    hRc, ?_⟩
  -- the multiplexors as circuits
  set cxT := (cxTop (⟨k + 1, by omega⟩ : Fin (k + 2))).denote with hcxT
  set cx0 := (cxTop (⟨0, by omega⟩ : Fin (k + 2))).denote with hcx0
  have hRa : Ra.denote * cxT = ofBlocks (Dz θa) := by
    have := grayMuxRev_denote (n := k + 2) (by omega) (extθ θa)
    rw [grayMuxRev, denote_append, denote_singleton] at this
    rw [hRadef, hcxT, ofBlocks_Dz, ← this]
    rfl
  have hRc' : cxT * (cx0 * Rc.denote) = ofBlocks (Dz θc) := by
    have := grayMux_denote (n := k + 2) (by omega) (extθ θc)
    rw [grayMux, hcore, denote_append, denote_append, denote_singleton, denote_cons,
      denote_singleton, hφ, denote_rzTop, Rz_zero, mux_const_one, Matrix.one_mul] at this
    rw [ofBlocks_Dz, ← this, hcxT, hcx0]
    rfl
  have hMidd : Mid.denote = ofBlocks hBlk * ofBlocks (Dz θb) * ofBlocks hBlk := by
    rw [hMid, denote_append, denote_append, denote_singleton, denote_hTop_eq,
      hGb, grayMux_denote, ofBlocks_Dz, Matrix.mul_assoc]
  -- the merge
  have hmid : cxT * dup Wa * ofBlocks hBlk * ofBlocks (fromBlocks 1 0 0 B) * ofBlocks hBlk *
      dup Vc * cxT * cx0 = dup Vb * Mid.denote * dup Wb := by
    rw [hcxT, hcx0, denote_cxTop_eq, denote_cxTop_eq, dup, dup, dup, dup, hMidd]
    simp only [ofBlocks_mul]
    congr 1
    rw [show hBlk * fromBlocks 1 0 0 zT * hBlk * fromBlocks Wa 0 0 Wa * hBlk *
        fromBlocks 1 0 0 B * hBlk * fromBlocks Vc 0 0 Vc * (hBlk * fromBlocks 1 0 0 zT * hBlk) *
        (hBlk * fromBlocks 1 0 0 z0 * hBlk) =
      (hBlk * fromBlocks 1 0 0 zT * hBlk) * fromBlocks Wa 0 0 Wa *
        (hBlk * fromBlocks 1 0 0 B * hBlk) * fromBlocks Vc 0 0 Vc *
        (hBlk * fromBlocks 1 0 0 zT * hBlk) * (hBlk * fromBlocks 1 0 0 z0 * hBlk) by
      simp only [Matrix.mul_assoc]]
    rw [middle_eq, hdb]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc hBlk (fromBlocks Vb 0 0 Vb), ← fromBlocks_dup_comm_hBlk,
      fromBlocks_dup_comm_hBlk Wb]
    simp only [Matrix.mul_assoc]
  have hmid' : ∀ X : Op (k + 2 + 1),
      cxT * (dup Wa * (ofBlocks hBlk * (ofBlocks (fromBlocks 1 0 0 B) *
      (ofBlocks hBlk * (dup Vc * (cxT * (cx0 * X))))))) = dup Vb * (Mid.denote * (dup Wb * X)) := by
    intro X
    simp only [← Matrix.mul_assoc]
    rw [hmid]
  -- assemble
  rw [denote_single_last_eq, ← ofBlocks_topBlocks U, ← hMdef, ofBlocks_mul, hM, hXY', hfac, hda,
    hdc]
  simp only [← ofBlocks_mul]
  rw [← dup, ← dup, ← dup, ← dup, ← hRa, ← hRc']
  simp only [Matrix.mul_assoc]
  rw [hmid']

end LeanUnitary.Pivot.Node
