import YM.Integration.WilsonPhysicalHistoryRetainedSpringFaceMoment

/-! The original plaquette address runs over six axes at the fixed site.
The normalized signed rotation average costs exactly this finite number. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.OriginalMarkedRunAction
open Function MeasureTheory Lattice RG Wilson Precision Exterior Work.F03 Bid Finset
open WilsonMeasuredPathTaylor
open scoped Topology BigOperators Classical
variable {G : Gauge} {n : Side}

def faceTaylorAt (x : Site n) (z : Dir G n) (q : ℕ) (g : ℝ) : ℝ :=
  Patch.average fun s : Signed=>∑ a : PlaqAxes,faceRay (collect G (pulled z s)) x a q g

theorem face_first (x : Site n) (z : Dir G n) (g : ℝ) : faceTaylorAt x z 1 g=0:=by
  simp [faceTaylorAt,Patch.average,face_ray_first]

theorem face_at (x : Site n) (z : Dir G n) (q : ℕ) (g : ℝ) :
    facePriceAt x (represent (g • z))-faceTaylorAt x z q g=
      (Fintype.card Signed:ℝ)⁻¹*∑ i : Signed×PlaqAxes,
        (G.price (faceValue (field (collect G (pulled z i.1)) g) (x,i.2))-
          faceRay (collect G (pulled z i.1)) x i.2 q g) := by
  have eq (s : Signed) : pull s 0 (represent (g • z))=field (collect G (pulled z s)) g:=by
    rw [Work.F03.represent_pulled]
    funext e
    rw [Work.F03.represent_link]
    rfl
  simp only [facePriceAt,faceTaylorAt,Patch.average,eq,Fintype.sum_prod_type,sum_sub_distrib,mul_sub]

theorem signed_average {Ω V A : Type*} [MeasurableSpace Ω] [Fintype V] [Nonempty V] [Fintype A]
    (μ : Measure Ω) (d : V×A→Ω→ℝ) (l : ℕ) {M : ℝ} (pos : 0≤M)
    (read : ∀ i,AEStronglyMeasurable (d i) μ) (paid : ∀ i,Integrable (fun z=>|d i z|^(l+1)) μ ∧
      (∫ z,|d i z|^(l+1) ∂μ)≤M^(l+1)) :
    let e:=fun z=>(Fintype.card V:ℝ)⁻¹*∑ i,d i z
    Integrable (fun z=>|e z|^(l+1)) μ ∧ (∫ z,|e z|^(l+1) ∂μ)≤((Fintype.card A:ℝ)*M)^(l+1) := by
  intro e
  let c:=(Fintype.card V:ℝ)⁻¹
  have hV : 0<(Fintype.card V:ℝ):=Nat.cast_pos.mpr Fintype.card_pos
  have cpos : 0≤c:=inv_nonneg.mpr hV.le
  have shape:=pool_finite μ univ (fun _ : V×A=>M) (fun i z=>|d i z|)
    (fun _ _=>pos) (fun _ _ _=>abs_nonneg _) (fun i _=>continuous_abs.comp_aestronglyMeasurable (read i)) l (fun i _=>paid i)
  have major : Integrable (fun z=>c^(l+1)*(∑ i,|d i z|)^(l+1)) μ:=shape.1.const_mul _
  have bound (z : Ω) : |e z|^(l+1)≤c^(l+1)*(∑ i,|d i z|)^(l+1):=by
    rw [←mul_pow]
    apply pow_le_pow_left₀ (abs_nonneg _)
    change |c*∑ i,d i z|≤_
    rw [abs_mul,abs_of_nonneg cpos]
    exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) cpos
  have measurable : AEStronglyMeasurable e μ:=
    (Finset.aestronglyMeasurable_fun_sum _ fun i _=>read i).const_mul _
  have h:=major.mono' ((continuous_abs.pow (l+1)).comp_aestronglyMeasurable measurable) (ae_of_all _ fun z=>by
    rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]; exact bound z)
  refine ⟨h,(integral_mono h major bound).trans ?_⟩
  rw [integral_const_mul]
  apply (mul_le_mul_of_nonneg_left shape.2 (pow_nonneg cpos _)).trans_eq
  simp only [sum_const,card_univ,Fintype.card_prod,Nat.cast_mul,nsmul_eq_mul,←mul_pow]
  congr 1
  dsimp only [c]
  field_simp

end YM.Integration.OriginalMarkedRunAction
