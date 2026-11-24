import YM.Integration.WilsonPhysicalHistoryRetainedSpringMean
import YM.Integration.WilsonPhysicalHistoryRetainedSpringDirections

/-! The complete signed orientation average at one true rooted site under
the measured covariance, before taking a connected logarithm. -/
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

theorem site_in_mean (h : Rotator P L η r Q Y X) {k : ℕ} (A : ℕ→Atom G k) {σ C : ℝ}
    (hs : 0<σ) (paid : SumBudget (fun i=>(A i).budget σ) C) (x : Site f) (q : ℕ) (t : ℝ) :
    let d:=fun z : Air f G=>(sitePacket A x (represent (t • angularSample F z)):ℂ)-
      siteTaylor A x (angularSample F z) q t
    Integrable d X.dice ∧ (∫ z,‖d z‖ ∂X.dice)≤C*(2*speedPrice G L η r Q q*|t|/σ)^(q+1) := by
  let v (s : Signed) (z : Air f G):=collect G (pulled (angularSample F z) s)
  let D (s : Signed) (z : Air f G):=(∑' i,((A i).unmasked (field (v s z) t) x:ℂ))-
    ∑' i,polynomial (A i) x (v s z) q t
  let room:=C*(2*speedPrice G L η r Q q*|t|/σ)^(q+1)
  have bill (s : Signed) : Integrable (D s) X.dice ∧ (∫ z,‖D s z‖ ∂X.dice)≤room :=
    measured_row X.dice (v s) (rotated_continuous F s).measurable A hs
      (speed_price_pos G L η r Q q) paid x q t
      (fun e=>(rotated_receipt h s q e).1) (fun e=>(rotated_receipt h s q e).2)
  have repr (s : Signed) (z : Air f G) : pull s 0 (represent (t • angularSample F z))=field (v s z) t := by
    rw [Work.F03.represent_pulled]
    funext e
    rw [Work.F03.represent_link]
    rfl
  have eq (z : Air f G) : (sitePacket A x (represent (t • angularSample F z)):ℂ)-
      siteTaylor A x (angularSample F z) q t=(Fintype.card Signed:ℂ)⁻¹*∑ s,D s z := by
    simp only [sitePacket,Patch.average,siteTaylor,repr,Complex.ofReal_mul,Complex.ofReal_sum,
      Complex.ofReal_inv,Complex.ofReal_natCast,Complex.ofReal_tsum,D,v,Finset.sum_sub_distrib,mul_sub]
  have card : 0<(Fintype.card Signed:ℝ):=Nat.cast_pos.mpr Fintype.card_pos
  have si:=integrable_finsetSum (s:=Finset.univ) (fun s _=>(bill s).1)
  have ni:=integrable_finsetSum (s:=Finset.univ) (fun s _=>(bill s).1.norm)
  have actual:=si.const_mul (Fintype.card Signed:ℂ)⁻¹
  dsimp only
  simp_rw [eq]
  refine ⟨actual,?_⟩
  have bd (z : Air f G) : ‖(Fintype.card Signed:ℂ)⁻¹*∑ s,D s z‖≤
      (Fintype.card Signed:ℝ)⁻¹*∑ s,‖D s z‖ := by
    rw [norm_mul,norm_inv,Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr card.le)
  apply (integral_mono actual.norm (ni.const_mul _) bd).trans
  rw [integral_const_mul,integral_finsetSum _ (fun s _=>(bill s).1.norm)]
  apply (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun s _=>(bill s).2) (inv_nonneg.mpr card.le)).trans
  rw [sum_const,card_univ,nsmul_eq_mul,←mul_assoc,inv_mul_cancel₀ card.ne',one_mul]

theorem site_with_tester (h : Rotator P L η r Q Y X) {k : ℕ} (A : ℕ→Atom G k) {σ C B : ℝ}
    (hs : 0<σ) (paid : SumBudget (fun i=>(A i).budget σ) C) (x : Site f) (q : ℕ) (t : ℝ)
    (H : Air f G→ℂ) (hm : AEStronglyMeasurable H X.dice) (bd : ∀ z,‖H z‖≤B) :
    let d:=fun z : Air f G=>(sitePacket A x (represent (t • angularSample F z)):ℂ)-
      siteTaylor A x (angularSample F z) q t
    Integrable (fun z=>H z*d z) X.dice ∧
      ‖∫ z,H z*d z ∂X.dice‖≤B*(C*(2*speedPrice G L η r Q q*|t|/σ)^(q+1)) := by
  let d:=fun z : Air f G=>(sitePacket A x (represent (t • angularSample F z)):ℂ)-
    siteTaylor A x (angularSample F z) q t
  have row:=site_in_mean h A hs paid x q t
  have M:=row.1.norm.const_mul B
  have each (z : Air f G) : ‖H z*d z‖≤B*‖d z‖:=by
    rw [norm_mul]; exact mul_le_mul_of_nonneg_right (bd z) (norm_nonneg _)
  have actual:=M.mono' (hm.mul row.1.aestronglyMeasurable) (ae_of_all _ each)
  refine ⟨actual,(norm_integral_le_of_norm_le M (ae_of_all _ each)).trans ?_⟩
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left row.2 ((norm_nonneg _).trans (bd 0))

end YM.Integration.OriginalMarkedRunAction
