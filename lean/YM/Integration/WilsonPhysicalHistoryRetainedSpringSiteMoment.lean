import YM.Integration.WilsonPhysicalHistoryRetainedSpringRowMoment
import YM.Integration.WilsonPhysicalHistoryRetainedSpringRoot

/-! The finite symmetry average of one original enrolled site keeps the full
moment bound on its single joint Gaussian. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.OriginalMarkedRunAction
open Function Lattice RG Pressure Pressure.Tube Tree Wilson Finset Precision Exterior Work.F03 Bid
open ConnectedActivityE6 Shell Coat Control Window RGLocalTaylor PhysicalNext.Repeat.Legato
open MeasureTheory WilsonMeasuredPathTaylor FundedCurvatureRayTaylor
open scoped BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}
variable {P : Teller G} {η r Q Y : ℝ} {X : Coat T F}

theorem site_moment (h : Rotator P L η r Q Y X) {k : ℕ} (A : ℕ→Atom G k) {σ C : ℝ}
    (hs : 0<σ) (paid : SumBudget (fun i=>(A i).budget σ) C) (x : Site f) (q l : ℕ) (t : ℝ) :
    let d:=fun z : Air f G=>(sitePacket A x (represent (t • angularSample F z)):ℂ)-
      siteTaylor A x (angularSample F z) q t
    Integrable (fun z=>‖d z‖^(l+1)) X.dice ∧ (∫ z,‖d z‖^(l+1) ∂X.dice)≤
      (C*(2*speedPrice G L η r Q ((q+1)*(l+1)-1)*|t|/σ)^(q+1))^(l+1) := by
  intro d
  let v (s : Signed) (z : Air f G):=collect G (pulled (angularSample F z) s)
  let D (s : Signed) (z : Air f G):=(∑' i,((A i).unmasked (field (v s z) t) x:ℂ))-
    ∑' i,polynomial (A i) x (v s z) q t
  let j:=(q+1)*(l+1)-1
  have index : j+1=(q+1)*(l+1):=Nat.sub_add_cancel (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _))
  let room:=C*(2*speedPrice G L η r Q j*|t|/σ)^(q+1)
  have c0 : 0≤C:=(tsum_nonneg (fun i=>by unfold Atom.budget Atom.magnitude; positivity)).trans paid.2.2
  have room0 : 0≤room:=by
    unfold room
    have hM:=speed_price_pos G L η r Q j
    positivity
  have charge (s : Signed) : Integrable (fun z=>‖D s z‖^(l+1)) X.dice ∧
      (∫ z,‖D s z‖^(l+1) ∂X.dice)≤room^(l+1) :=
    row_moment X.dice (v s) (rotated_continuous F s).measurable A hs (speed_price_pos G L η r Q j)
      paid x q l t (fun e=>(rotated_receipt h s j e).1) (fun e=>by
        simpa only [index] using (rotated_receipt h s j e).2)
  have measured (s : Signed) : AEStronglyMeasurable (D s) X.dice :=
    (measured_row X.dice (v s) (rotated_continuous F s).measurable A hs
      (speed_price_pos G L η r Q q) paid x q t
      (fun e=>(rotated_receipt h s q e).1) (fun e=>(rotated_receipt h s q e).2)).1.aestronglyMeasurable
  have repr (s : Signed) (z : Air f G) : pull s 0 (represent (t • angularSample F z))=field (v s z) t := by
    rw [Work.F03.represent_pulled]
    funext e
    rw [Work.F03.represent_link]
    rfl
  have eq (z : Air f G) : (sitePacket A x (represent (t • angularSample F z)):ℂ)-
      siteTaylor A x (angularSample F z) q t=(Fintype.card Signed:ℂ)⁻¹*∑ s,D s z := by
    simp only [sitePacket,Patch.average,siteTaylor,repr,Complex.ofReal_mul,Complex.ofReal_sum,
      Complex.ofReal_inv,Complex.ofReal_natCast,Complex.ofReal_tsum,D,v,Finset.sum_sub_distrib,mul_sub]
  have card : (0:ℝ)<Fintype.card Signed:=Nat.cast_pos.mpr Fintype.card_pos
  let α:=(Fintype.card Signed:ℝ)⁻¹
  have alpha : 0≤α:=inv_nonneg.mpr card.le
  have pool:=pool_finite X.dice univ (fun _ : Signed=>α*room) (fun s z=>α*‖D s z‖)
    (fun _ _=>mul_nonneg alpha room0) (fun _ _ _=>mul_nonneg alpha (norm_nonneg _))
    (fun s _=>(measured s).norm.const_mul α) l (fun s _=>by
      simp only [mul_pow,integral_const_mul]
      exact ⟨(charge s).1.const_mul _,mul_le_mul_of_nonneg_left (charge s).2 (pow_nonneg alpha _)⟩)
  have bound (z : Air f G) : ‖d z‖^(l+1)≤(∑ s,α*‖D s z‖)^(l+1):=by
    apply pow_le_pow_left₀ (norm_nonneg _)
    change ‖(sitePacket A x (represent (t • angularSample F z)):ℂ)-siteTaylor A x (angularSample F z) q t‖≤_
    rw [eq,norm_mul,norm_inv,Complex.norm_natCast,←Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) alpha
  have dm:=(site_in_mean h A hs paid x q t).1.norm.aestronglyMeasurable
  have hi:=pool.1.mono' ((continuous_pow (l+1)).comp_aestronglyMeasurable dm) (ae_of_all _ fun z=>by
    rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (norm_nonneg _) _)]; exact bound z)
  refine ⟨hi,(integral_mono hi pool.1 bound).trans (pool.2.trans_eq ?_)⟩
  rw [sum_const,card_univ,nsmul_eq_mul,←mul_assoc,mul_inv_cancel₀ card.ne',one_mul]

end YM.Integration.OriginalMarkedRunAction
