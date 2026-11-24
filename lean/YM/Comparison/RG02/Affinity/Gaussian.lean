import YM.Comparison.RG02.Laplace.Fields
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Affinity
open Function Filter Finset MeasureTheory
open YM.Marker YM.Multi Order Assembly Actual YM.Lattice YM.Tree
open YM.Precision YM.Next.SectorChange
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff ENNReal
variable {G : Gauge} {V : Type} [DecidableEq V] {R : Census V}
variable {I : Type} [Fintype I] [DecidableEq I]
local notation "Λ" => I→ℝ

open Gaussian Matrix
lemma linear_paid (B : Matrix I I ℝ) (m : Λ) (hB : 0<B.det) {X:Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (f : (I→ℝ)→ X) :
   (Integrable f ↔ Integrable (fun v=> f (m + B *ᵥ v))) ∧
      (∫ v,f v)= B.det • ∫ v: I→ℝ, f (m + B *ᵥ v) := by
   have he := (Real.map_matrix_volume_pi_eq_smul_volume_pi hB.ne')
   rw [abs_of_nonneg (inv_nonneg.mpr hB.le)] at he
   let p:Vec I≃ᵐVec I:=
    { toFun:=fun y=> B *ᵥ y, invFun:=fun y=> B⁻¹ *ᵥ y
      left_inv:=fun y=> by dsimp only; rw [Matrix.mulVec_mulVec, B.nonsing_inv_mul (isUnit_iff_ne_zero.mpr hB.ne'), Matrix.one_mulVec]
      right_inv:=fun y=> by dsimp only; rw [Matrix.mulVec_mulVec, B.mul_nonsing_inv (isUnit_iff_ne_zero.mpr hB.ne'),Matrix.one_mulVec]
      measurable_toFun:= acts_meas _, measurable_invFun:=acts_meas _}
   let q:Vec I≃ᵐVec I:= MeasurableEquiv.addLeft m
   let h : MeasurePreserving q volume volume := measurePreserving_add_left ..
   rw [show ⇑(Matrix.toLin' B)=p from funext (fun y=> Matrix.toLin'_apply ..)] at he
   have hp : Measure.map (p.trans q) volume = ENNReal.ofReal B.det⁻¹ • volume := by
      show Measure.map (q ∘ p) _=_
      rw [← Measure.map_map q.measurable p.measurable, he,Measure.map_smul,h.map_eq]
   constructor
   · change _ ↔ Integrable (f ∘ p.trans q) volume
     rw [← (p.trans q).measurableEmbedding.integrable_map_iff,hp,integrable_smul_measure (by exact (ENNReal.ofReal_pos.mpr (inv_pos.mpr hB)).ne') (by simp)]
   change _ = B.det • ∫ v:I→ℝ, f (p.trans q v)
   rw [← integral_map_equiv, hp, integral_smul_measure,ENNReal.toReal_ofReal (inv_nonneg.mpr hB.le),smul_smul,mul_inv_cancel₀ hB.ne',one_smul]

/-- Radon factor for pulling back to a Gaussian of the same width. Weights INSIDE determinant
    and force, applies INV determinant convention via exact non-deformed identity. -/
def toll (Q B : Matrix I I ℝ) (m v : I→ℝ) := B.det * Real.exp (force Q v/2-force Q (m+B *ᵥ v)/2)

theorem adjust (Q B : Matrix I I ℝ) (m : Λ) (hB : 0<B.det) (hQ : Q.PosDef)
    {X:Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (f : (I→ℝ) → X) :
    let y := fun v=> toll Q B m v • f (m+B *ᵥ v)
    (Integrable f (cloud Q) ↔ Integrable y (cloud Q)) ∧
      (∫ v, f v ∂cloud Q)= ∫ v, y v ∂cloud Q := by
   intro y
   let p := fun v:I→ℝ=> Real.exp (-(force Q v/2)) • f v
   let u := fun v:I→ℝ=> p (m+B *ᵥ v)
   let g := fun v:I→ℝ=> Real.exp (force Q v/2) • u v
   have hp (v:I→ℝ) : Real.exp (force Q v/2) • p v=f v := by unfold p; rw [smul_smul, ← Real.exp_add, add_neg_cancel,Real.exp_zero,one_smul]
   have hg: B.det • g=y := by
      funext v; unfold y toll g u p; rw [Real.exp_sub,Pi.smul_apply,smul_smul,smul_smul, Real.exp_neg]; simp [div_eq_mul_inv,mul_assoc]
   obtain ⟨hi,hh⟩:= under_cloud hQ p
   dsimp only at hi hh; simp_rw [hp] at hi hh
   obtain ⟨hm,hl⟩ := under_cloud hQ u
   change _ ↔ Integrable g _ at hm
   change _= coat Q • ∫ v,g v ∂cloud Q at hl
   obtain ⟨hv,h⟩ := linear_paid B m hB p
   change _=B.det • ∫ v,u v at h
   rw [hh,hl,smul_comm B.det] at h
   constructor
   · refine hi.symm |>.trans (hv.trans (hm.trans ?_)); rw [← hg]; constructor
     · exact fun hz=> hz.smul B.det
     intro hz; have hr := hz.smul B.det⁻¹
     convert hr using 1; simp [Pi.smul_def,smul_smul,hB.ne']
   rw [← hg]; change _ = ∫ v,B.det • g v ∂cloud Q
   rw [integral_smul]
   exact (smul_right_inj (coat_pos hQ).ne').mp h

-- in assembled price sectors

def account (Q B : Matrix I I ℝ) (m : I→ℝ) (p : Lit R (I→ℝ)) : Lit R (I→ℝ) := fun v=> (↑(toll Q B m v):ℂ) • p (m+B *ᵥ v)

lemma at_account (Q B : Matrix I I ℝ) (m : Λ) (hB : 0<B.det) (hQ : Q.PosDef) (p : Lit R (I→ℝ)) :
    (Good (cloud Q) p ↔ Good (cloud Q) (account Q B m p)) ∧ charge (cloud Q) (account Q B m p)=charge (cloud Q) p := by
   have he (i:R.Mode) : atMark i (account Q B m p)= fun v=> toll Q B m v • atMark i p (m+B *ᵥ v) := by funext v; unfold atMark account; rw [Poly.part_smul, Complex.real_smul]
   constructor
   · unfold Good; simp_rw [he]; exact forall_congr' (fun i=> (adjust Q B m hB hQ (atMark i p)).1)
   ext i; rw [components,components,he]; exact (adjust Q B m hB hQ (atMark i p)).2.symm

lemma on_cut (Q B : Matrix I I ℝ) (m : Λ) (p : Lit R (I→ℝ)) (A : Set (I→ℝ)) :
    ((fun v:I→ℝ=> m+B *ᵥ v) ⁻¹' A).indicator (account Q B m p)=account Q B m (A.indicator p) := by
   funext v; by_cases h : m+B *ᵥ v ∈ A <;> simp [account,h]
end YM.Comparison.RG02.Affinity
