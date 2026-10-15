import LeanUnitary.Pivot.Multiplexor.Continuity
import LeanUnitary.Pivot.Node.TopGates

/-!
# The Block-ZXZ factorization

Krol–Al-Ars (arXiv:2403.13692, Sec. 4.1): a unitary `U = [X Y; Z W]` with invertible `X`, `Y`
factors as

    U = (A₁ ⊕ A₂) · (H ⊗ I) · (I ⊕ B) · (H ⊗ I) · (I ⊕ C),     C = zxzC X Y,

with `A₁`, `A₂`, `B` unitary. This is the step that identifies `zxzC` (and hence `C(β)`,
Eq. 10) as the left-side multiplexor of the node. Write the polar decompositions
`X = S_X U_X`, `Y = S_Y U_Y` with `S_X = (X Xᴴ)^{1/2}`, `S_Y = (Y Yᴴ)^{1/2}`. Unitarity of the
top block row gives `S_X² + S_Y² = 1`, and `S_X`, `S_Y` commute, so `V = S_X - i S_Y` is unitary.
Then `C = -i U_Xᴴ U_Y`, `A₁ = Vᴴ U_X` and `B = U_Xᴴ V² U_X`; `A₂` is read off from the unitary
`U (I ⊕ C)ᴴ ((H ⊗ I)(I ⊕ B)(H ⊗ I))ᴴ`, whose off-diagonal blocks vanish.
-/

namespace LeanUnitary.Pivot.Node

open Matrix Complex LeanUnitary.Pivot
open scoped ComplexOrder

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- `H ⊗ I` on a register split by its top qubit. -/
noncomputable abbrev hBlk : Matrix (m ⊕ m) (m ⊕ m) ℂ := Pivot.lift had

omit [Fintype m] in
theorem hBlk_eq : (hBlk : Matrix (m ⊕ m) (m ⊕ m) ℂ) =
    fromBlocks (((Real.sqrt 2)⁻¹ : ℂ) • 1) (((Real.sqrt 2)⁻¹ : ℂ) • 1)
      (((Real.sqrt 2)⁻¹ : ℂ) • 1) ((-(Real.sqrt 2)⁻¹ : ℂ) • 1) := by
  simp [hBlk, Pivot.lift, had]

theorem sqrt_two_inv_sq : ((Real.sqrt 2 : ℂ))⁻¹ * ((Real.sqrt 2 : ℂ))⁻¹ = 1 / 2 := by
  have hs : ((Real.sqrt 2 : ℂ)) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  rw [← mul_inv, ← sq, hs]; norm_num

/-- `(H ⊗ I)(I ⊕ B)(H ⊗ I) = ½ [1 + B, 1 - B; 1 - B, 1 + B]`. -/
theorem hBlk_mul_mul_hBlk (B : Matrix m m ℂ) :
    hBlk * fromBlocks 1 0 0 B * hBlk =
      ((1 / 2 : ℂ)) • fromBlocks (1 + B) (1 - B) (1 - B) (1 + B) := by
  rw [hBlk_eq, fromBlocks_multiply, fromBlocks_multiply, fromBlocks_smul]
  simp only [Matrix.mul_zero, add_zero, zero_add, Matrix.smul_mul, Complex.ofReal_inv,
    Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul, neg_mul, mul_neg, neg_neg,
    sqrt_two_inv_sq]
  congr 1 <;> module

theorem hBlk_mul_hBlk : (hBlk : Matrix (m ⊕ m) (m ⊕ m) ℂ) * hBlk = 1 := by
  have := hBlk_mul_mul_hBlk (m := m) 1
  rw [fromBlocks_one, Matrix.mul_one] at this
  rw [this, sub_self, fromBlocks_smul, smul_zero, ← fromBlocks_one]
  congr 1 <;> rw [← two_smul ℂ (1 : Matrix m m ℂ), smul_smul] <;> norm_num

omit [Fintype m] in
theorem hBlk_conjTranspose : (hBlk : Matrix (m ⊕ m) (m ⊕ m) ℂ)ᴴ = hBlk := by
  rw [hBlk_eq, fromBlocks_conjTranspose]
  simp only [conjTranspose_smul, conjTranspose_one, star_neg, Complex.star_def,
    Complex.conj_ofReal, map_inv₀]

theorem hBlk_mem : (hBlk : Matrix (m ⊕ m) (m ⊕ m) ℂ) ∈ unitaryGroup (m ⊕ m) ℂ := by
  rw [mem_unitaryGroup_iff, star_eq_conjTranspose, hBlk_conjTranspose, hBlk_mul_hBlk]

theorem fromBlocks_diag_mem {A D : Matrix m m ℂ} (hA : A ∈ unitaryGroup m ℂ)
    (hD : D ∈ unitaryGroup m ℂ) : fromBlocks A 0 0 D ∈ unitaryGroup (m ⊕ m) ℂ := by
  rw [mem_unitaryGroup_iff, star_eq_conjTranspose, fromBlocks_conjTranspose, fromBlocks_multiply]
  rw [mem_unitaryGroup_iff, star_eq_conjTranspose] at hA hD
  simp [hA, hD, fromBlocks_one]

/-- A unitary block matrix with a zero top-right block is block diagonal. -/
theorem eq_zero_of_fromBlocks_mem {A R D : Matrix m m ℂ} (hA : A ∈ unitaryGroup m ℂ)
    (hT : fromBlocks A 0 R D ∈ unitaryGroup (m ⊕ m) ℂ) : R = 0 ∧ D ∈ unitaryGroup m ℂ := by
  have h := mem_unitaryGroup_iff'.mp hT
  rw [star_eq_conjTranspose, fromBlocks_conjTranspose, fromBlocks_multiply, ← fromBlocks_one,
    fromBlocks_inj] at h
  obtain ⟨h11, -, -, h22⟩ := h
  have hAA : Aᴴ * A = 1 := by rw [← star_eq_conjTranspose]; exact mem_unitaryGroup_iff'.mp hA
  have hRR : Rᴴ * R = 0 := by
    have : Aᴴ * A + Rᴴ * R = Aᴴ * A := by rw [h11, hAA]
    simpa using this
  have hR : R = 0 := by
    rw [← trace_conjTranspose_mul_self_eq_zero_iff, hRR, trace_zero]
  refine ⟨hR, ?_⟩
  rw [mem_unitaryGroup_iff', star_eq_conjTranspose]
  simpa [hR] using h22

/-- **Block-ZXZ factorization** (Krol–Al-Ars, Sec. 4.1), with left-side multiplexor `zxzC X Y`. -/
theorem exists_zxz_factor {X Y Z W : Matrix m m ℂ}
    (hU : fromBlocks X Y Z W ∈ unitaryGroup (m ⊕ m) ℂ) (hX : IsUnit X.det) (hY : IsUnit Y.det) :
    ∃ A₁ ∈ unitaryGroup m ℂ, ∃ A₂ ∈ unitaryGroup m ℂ, ∃ B ∈ unitaryGroup m ℂ,
      fromBlocks X Y Z W =
        fromBlocks A₁ 0 0 A₂ * (hBlk * fromBlocks 1 0 0 B * hBlk) *
          fromBlocks 1 0 0 (zxzC X Y) := by
  -- the top block row has orthonormal rows
  have hrow : X * Xᴴ + Y * Yᴴ = 1 := by
    have h := mem_unitaryGroup_iff.mp hU
    rw [star_eq_conjTranspose, fromBlocks_conjTranspose, fromBlocks_multiply, ← fromBlocks_one,
      fromBlocks_inj] at h
    exact h.1
  set A := X * Xᴴ with hAdef
  set B' := Y * Yᴴ with hB'def
  set P := invSqrt A with hPdef
  set Q := invSqrt B' with hQdef
  have hApd : A.PosDef := posDef_mul_conjTranspose_self hX
  have hBpd : B'.PosDef := posDef_mul_conjTranspose_self hY
  have hPAP : P * A * P = 1 := invSqrt_mul_self_mul_invSqrt hApd
  have hQBQ : Q * B' * Q = 1 := invSqrt_mul_self_mul_invSqrt hBpd
  -- everything in sight commutes: `B' = 1 - A`, and `P`, `Q` are functions of `A`, `B'`
  have hAB : Commute A B' := by
    have : B' = 1 - A := by rw [← hrow]; abel
    rw [this]; exact (Commute.one_right A).sub_right (Commute.refl A)
  have hPA : Commute P A := (Commute.refl A).cfc_real _
  have hQB : Commute Q B' := (Commute.refl B').cfc_real _
  have hPB : Commute P B' := hAB.cfc_real _
  have hQA : Commute Q A := hAB.symm.cfc_real _
  have hQP : Commute Q P := hPB.symm.cfc_real _
  -- `S_X = A P`, `S_Y = B' Q` (the positive square roots)
  set Sx := A * P with hSx
  set Sy := B' * Q with hSy
  have hAPP : A * P * P = 1 := by rw [← hPAP, hPA.eq, Matrix.mul_assoc]
  have hBQQ : B' * Q * Q = 1 := by rw [← hQBQ, hQB.eq, Matrix.mul_assoc]
  have hPh : Pᴴ = P := conjTranspose_invSqrt A
  have hQh : Qᴴ = Q := conjTranspose_invSqrt B'
  have hAh : Aᴴ = A := by rw [hAdef, conjTranspose_mul, conjTranspose_conjTranspose]
  have hBh : B'ᴴ = B' := by rw [hB'def, conjTranspose_mul, conjTranspose_conjTranspose]
  have hSxh : Sxᴴ = Sx := by rw [hSx, conjTranspose_mul, hPh, hAh, hPA.eq]
  have hSyh : Syᴴ = Sy := by rw [hSy, conjTranspose_mul, hQh, hBh, hQB.eq]
  have hSxSy : Sx * Sy = Sy * Sx := by
    rw [hSx, hSy]
    have h1 : Commute (A * P) (B' * Q) :=
      (hAB.mul_right hQA.symm).mul_left ((hPB.mul_right hQP.symm))
    exact h1.eq
  have hSq : Sx * Sx + Sy * Sy = 1 := by
    have e1 : Sx * Sx = A := by
      rw [hSx, Matrix.mul_assoc, ← Matrix.mul_assoc P A P, hPAP, Matrix.mul_one]
    have e2 : Sy * Sy = B' := by
      rw [hSy, Matrix.mul_assoc, ← Matrix.mul_assoc Q B' Q, hQBQ, Matrix.mul_one]
    rw [e1, e2, hrow]
  -- the polar factors
  set Ux := P * X with hUx
  set Uy := Q * Y with hUy
  have hUxm : Ux ∈ unitaryGroup m ℂ := invSqrt_mul_mem_unitaryGroup hX
  have hUym : Uy ∈ unitaryGroup m ℂ := invSqrt_mul_mem_unitaryGroup hY
  have hUxU : Ux * Uxᴴ = 1 := by rw [← star_eq_conjTranspose]; exact mem_unitaryGroup_iff.mp hUxm
  have hUyU : Uy * Uyᴴ = 1 := by rw [← star_eq_conjTranspose]; exact mem_unitaryGroup_iff.mp hUym
  have hXeq : X = Sx * Ux := by
    rw [hSx, hUx, show A * P * (P * X) = (A * P * P) * X by simp only [Matrix.mul_assoc], hAPP,
      Matrix.one_mul]
  have hYeq : Y = Sy * Uy := by
    rw [hSy, hUy, show B' * Q * (Q * Y) = (B' * Q * Q) * Y by simp only [Matrix.mul_assoc], hBQQ,
      Matrix.one_mul]
  have hC : zxzC X Y = (-I) • (Uxᴴ * Uy) := by
    rw [zxzC, hUx, hUy, conjTranspose_mul, hPh, hPdef, hQdef, hAdef, hB'def]
    simp only [Matrix.mul_assoc]
  have hCm : zxzC X Y ∈ unitaryGroup m ℂ := zxzC_mem_unitaryGroup hX hY
  clear_value Ux Uy Sx Sy P Q A B'
  -- `V = S_X - i S_Y` is unitary with `Vᴴ = S_X + i S_Y`
  obtain ⟨V, hV⟩ : ∃ V, V = Sx - I • Sy := ⟨_, rfl⟩
  have hVh : Vᴴ = Sx + I • Sy := by
    rw [hV, conjTranspose_sub, conjTranspose_smul, hSxh, hSyh]
    simp [sub_eq_add_neg]
  have hVVh : V * Vᴴ = 1 := by
    rw [hVh, hV, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, I_mul_I, hSxSy]
    rw [← hSq]; simp only [neg_smul, one_smul]; abel
  have hVm : V ∈ unitaryGroup m ℂ := by
    rw [mem_unitaryGroup_iff, star_eq_conjTranspose]; exact hVVh
  have hVhm : Vᴴ ∈ unitaryGroup m ℂ := by
    rw [← star_eq_conjTranspose]; exact Unitary.star_mem hVm
  have hUxhm : Uxᴴ ∈ unitaryGroup m ℂ := by
    rw [← star_eq_conjTranspose]; exact Unitary.star_mem hUxm
  obtain ⟨A₁, hA₁⟩ : ∃ A₁, A₁ = Vᴴ * Ux := ⟨_, rfl⟩
  obtain ⟨Bm, hBm⟩ : ∃ Bm, Bm = Uxᴴ * V * V * Ux := ⟨_, rfl⟩
  have hA₁m : A₁ ∈ unitaryGroup m ℂ := hA₁ ▸ Submonoid.mul_mem _ hVhm hUxm
  have hBmm : Bm ∈ unitaryGroup m ℂ := hBm ▸
    Submonoid.mul_mem _ (Submonoid.mul_mem _ (Submonoid.mul_mem _ hUxhm hVm) hVm) hUxm
  obtain ⟨C, hCdef⟩ : ∃ C, C = zxzC X Y := ⟨_, rfl⟩
  rw [← hCdef] at hC hCm ⊢
  have hChm : Cᴴ ∈ unitaryGroup m ℂ := by
    rw [← star_eq_conjTranspose]; exact Unitary.star_mem hCm
  have hBmhm : Bmᴴ ∈ unitaryGroup m ℂ := by
    rw [← star_eq_conjTranspose]; exact Unitary.star_mem hBmm
  -- `K = (H⊗I)(I⊕B)(H⊗I)` and its inverse `K' = (H⊗I)(I⊕Bᴴ)(H⊗I)`
  have hDD : fromBlocks (1 : Matrix m m ℂ) 0 0 Bmᴴ * fromBlocks 1 0 0 Bm = 1 := by
    have hBB : Bmᴴ * Bm = 1 := by rw [← star_eq_conjTranspose]; exact mem_unitaryGroup_iff'.mp hBmm
    rw [fromBlocks_multiply]; simp [hBB, fromBlocks_one]
  have hKK : (hBlk * fromBlocks 1 0 0 Bmᴴ * hBlk) * (hBlk * fromBlocks 1 0 0 Bm * hBlk) = 1 := by
    calc (hBlk * fromBlocks 1 0 0 Bmᴴ * hBlk) * (hBlk * fromBlocks 1 0 0 Bm * hBlk)
        = hBlk * fromBlocks 1 0 0 Bmᴴ * (hBlk * hBlk) * fromBlocks 1 0 0 Bm * hBlk := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [hBlk_mul_hBlk, Matrix.mul_one, Matrix.mul_assoc hBlk, hDD, Matrix.mul_one,
            hBlk_mul_hBlk]
  have hCC : fromBlocks (1 : Matrix m m ℂ) 0 0 Cᴴ * fromBlocks 1 0 0 C = 1 := by
    have : Cᴴ * C = 1 := by rw [← star_eq_conjTranspose]; exact mem_unitaryGroup_iff'.mp hCm
    rw [fromBlocks_multiply]; simp [this, fromBlocks_one]
  -- `T = U (I ⊕ C)ᴴ K'` is unitary with top row `(A₁, 0)`
  obtain ⟨T, hT⟩ : ∃ T, T = fromBlocks X Y Z W * fromBlocks 1 0 0 Cᴴ *
      (hBlk * fromBlocks 1 0 0 Bmᴴ * hBlk) := ⟨_, rfl⟩
  have hTm : T ∈ unitaryGroup (m ⊕ m) ℂ := by
    rw [hT]
    refine Submonoid.mul_mem _ (Submonoid.mul_mem _ hU (fromBlocks_diag_mem
      (Submonoid.one_mem _) hChm)) ?_
    exact Submonoid.mul_mem _ (Submonoid.mul_mem _ hBlk_mem
      (fromBlocks_diag_mem (Submonoid.one_mem _) hBmhm)) hBlk_mem
  -- the top row of `T`
  have hYC : Y * Cᴴ = I • (Sy * Ux) := by
    rw [hC, conjTranspose_smul, conjTranspose_mul, conjTranspose_conjTranspose, hYeq]
    simp only [star_neg, Complex.star_def, Complex.conj_I, neg_neg, Matrix.mul_smul]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Uy, hUyU, Matrix.one_mul]
  have hBmh : Bmᴴ = Uxᴴ * Vᴴ * Vᴴ * Ux := by
    rw [hBm]; simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
  have hXB : X * Bmᴴ = Sx * (Vᴴ * Vᴴ * Ux) := by
    rw [hBmh, hXeq]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Ux Uxᴴ, hUxU, Matrix.one_mul]
  have hYB : I • (Sy * Ux) * Bmᴴ = I • (Sy * (Vᴴ * Vᴴ * Ux)) := by
    rw [Matrix.smul_mul, hBmh]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Ux Uxᴴ, hUxU, Matrix.one_mul]
  have hW3 : V * (Vᴴ * Vᴴ * Ux) = Vᴴ * Ux := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc V Vᴴ Vᴴ, hVVh, Matrix.one_mul]
  have e : Sx * (Vᴴ * Vᴴ * Ux) - I • (Sy * (Vᴴ * Vᴴ * Ux)) = Vᴴ * Ux := by
    rw [← Matrix.smul_mul, ← Matrix.sub_mul, ← hV, hW3]
  have e' : Sx * Ux + I • (Sy * Ux) = Vᴴ * Ux := by
    rw [← Matrix.smul_mul, ← Matrix.add_mul, hVh]
  have hTtop : T.toBlocks₁₁ = A₁ ∧ T.toBlocks₁₂ = 0 := by
    rw [hT, hBlk_mul_mul_hBlk, fromBlocks_multiply, Matrix.mul_smul, fromBlocks_multiply,
      fromBlocks_smul]
    simp only [Matrix.mul_zero, add_zero, zero_add, Matrix.mul_one,
      toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, Matrix.mul_add, Matrix.mul_sub]
    rw [hYC, hXB, hYB, hXeq]
    constructor
    · rw [hA₁]
      calc (1 / 2 : ℂ) • (Sx * Ux + Sx * (Vᴴ * Vᴴ * Ux) +
            (I • (Sy * Ux) - I • (Sy * (Vᴴ * Vᴴ * Ux))))
          = (1 / 2 : ℂ) • ((Sx * Ux + I • (Sy * Ux)) +
              (Sx * (Vᴴ * Vᴴ * Ux) - I • (Sy * (Vᴴ * Vᴴ * Ux)))) := by congr 1; abel
        _ = Vᴴ * Ux := by rw [e, e', ← two_smul ℂ, smul_smul]; norm_num
    · calc (1 / 2 : ℂ) • (Sx * Ux - Sx * (Vᴴ * Vᴴ * Ux) +
            (I • (Sy * Ux) + I • (Sy * (Vᴴ * Vᴴ * Ux))))
          = (1 / 2 : ℂ) • ((Sx * Ux + I • (Sy * Ux)) -
              (Sx * (Vᴴ * Vᴴ * Ux) - I • (Sy * (Vᴴ * Vᴴ * Ux)))) := by congr 1; abel
        _ = 0 := by rw [e, e', sub_self, smul_zero]
  -- `T` is block diagonal
  have hTblk : T = fromBlocks A₁ 0 T.toBlocks₂₁ T.toBlocks₂₂ := by
    conv_lhs => rw [← fromBlocks_toBlocks T]
    rw [hTtop.1, hTtop.2]
  obtain ⟨hR, hA₂⟩ := eq_zero_of_fromBlocks_mem hA₁m (hTblk ▸ hTm)
  rw [hR] at hTblk
  refine ⟨A₁, hA₁m, T.toBlocks₂₂, hA₂, Bm, hBmm, ?_⟩
  rw [← hTblk, hT]
  calc fromBlocks X Y Z W
      = fromBlocks X Y Z W * (fromBlocks 1 0 0 Cᴴ * (((hBlk * fromBlocks 1 0 0 Bmᴴ * hBlk) *
          (hBlk * fromBlocks 1 0 0 Bm * hBlk)) * fromBlocks 1 0 0 C)) := by
        rw [hKK, Matrix.one_mul, hCC, Matrix.mul_one]
    _ = _ := by simp only [Matrix.mul_assoc]

end LeanUnitary.Pivot.Node
