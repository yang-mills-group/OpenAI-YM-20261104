import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionShortRegularPrice

/-! The observed complete density and both terms of its actual regular/forced
decomposition all use the very same original finite physical law. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Exchange.RoseCut
open Function Finset Set MeasureTheory Lattice RG YM.Wilson Marker QuadraticLocal Extra.Trajectories
open scoped Classical BigOperators
open private lit_regular from YM.Integration.FVA1Physical.Exchange.CovarianceExpansionShortRegularPrice
variable {G:Gauge}{n:Side}{V T I:Type}[Fintype V][DecidableEq V]{C:Census V}
  {o:V→Site n}{P:Rep G n}(A:Gallery T I o P C)

theorem physical_singleton_exact {w:V→ℝ}(wp:∀v,0<w v){e c κ:ℝ}(paid:A.Pays w e c κ)
    (en:0≤e)(t:T)(U:Config G n)(live:0<P.eval U)(a:V):
    (w a:ℂ)*(((P.eval U:ℂ)⁻¹ • A.density t U).part (C.fire a)) =
      (w a:ℂ)*originalRaw A t (C.fire a) U+(w a:ℂ)*(A.E.log t U).part (C.fire a):=by
  let ν:=P.activities.gas P.p U
  let X:=(P.eval U:ℂ)⁻¹ • A.density t U
  let K:=(ν:ℂ)⁻¹ • A.gas t U
  have gp:0<ν:=pos_of_mul_pos_right live (Real.exp_nonneg _)
  have xu:X.part C.quiet=1:=by
    rw [show X.part C.quiet = _ from Poly.part_smul ..,A.same paid en wp,
      inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr live.ne')]
  have ku:K.part C.quiet=1:=by
    change ((ν:ℂ)⁻¹ • A.gas t U).part C.quiet=1
    rw [Poly.part_smul,Gallery.gas,Hard.packet_of_quiet A.K t U
      (Hard.packet_summing _ paid.wages en wp t U),inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr gp.ne')]
  have same:=WilsonReportNormalizedGallery.connected A wp en paid.wages t U live
  change connected X=A.E.log t U+connected K at same
  have coord:=congrArg (fun Q:Poly C=>Q.part (C.fire a)) same
  change (connected X).part (C.fire a)=(A.E.log t U+connected K).part (C.fire a) at coord
  rw [Poly.part_plus,Comparison.RG02.Cumulants.lamp a X xu,Comparison.RG02.Cumulants.lamp a K ku] at coord
  have q:K.part (C.fire a)=originalRaw A t (C.fire a) U:=by
    change ((ν:ℂ)⁻¹ • A.gas t U).part (C.fire a)=_/_
    rw [Poly.part_smul,div_eq_mul_inv];exact mul_comm .. 
  change (w a:ℂ)*X.part (C.fire a)=_
  rw [coord,q];ring

omit [Fintype V] in
theorem regular_singleton_borel [Countable I](t:T)(a:V)(w:V→ℝ):
    Measurable (fun U:Config G n=>(w a:ℂ)*(A.E.log t U).part (C.fire a))
    :=by
  apply measurable_const.mul
  apply (Poly.part_cont _).measurable.comp
  apply Measurable.tsum
  intro i
  exact (Overlay.Bands.sends _).measurable.comp (lit_regular A.E t i).2.1

end YM.Integration.FVA1Physical.Exchange.RoseCut
