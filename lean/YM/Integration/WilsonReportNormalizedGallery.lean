import YM.QuadraticLocal.Lamps
import YM.FormalOPE.RG10.MarkerLog

/-! The normalized connected field in the original complete gallery of
any finite marked roster. The original signed compatible hard family
and its genuine positive vacuum are retained at the same field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportNormalizedGallery
open Function Finset Lattice Wilson RG QuadraticLocal Marker

theorem connected {G:Gauge} {n:Side} {V:Type} {I T:Type*} [Fintype V] [DecidableEq V] {C:Marker.Census V}
    {o:V→Site n} {P:RG.Rep G n} (A:Gallery T I o P C) {w:V→ℝ} (pos:∀j,0 < w j)
    {α m:ℝ} (width:0 ≤ α) (hard:A.K.Paid w P.p.B α m)
    (t:T) (U:Config G n) (physicalValue:0 < P.eval U):
    Extra.Trajectories.connected ((P.eval U:ℂ)⁻¹ • A.density t U) =
      A.E.log t U + Extra.Trajectories.connected (((P.activities.gas P.p U:ℂ)⁻¹) • A.gas t U):=by
  let g:=P.activities.gas P.p U
  have bare:g≠0:=((mul_ne_zero_iff.mp (show Real.exp (P.exponent U)*g≠0 from physicalValue.ne')).2)
  have hn:(g:ℂ)≠0:=by exact_mod_cast bare
  have hex : ((Real.exp (P.exponent U):ℝ):ℂ)≠0:=by exact_mod_cast (Real.exp_pos _).ne'
  have coef:(P.eval U:ℂ)⁻¹*(Real.exp (P.exponent U):ℂ)=(g:ℂ)⁻¹:=by
    rw [RG.Rep.eval,Complex.ofReal_mul]
    change (((Real.exp (P.exponent U):ℂ)*(g:ℂ))⁻¹)*(Real.exp (P.exponent U):ℂ)=(g:ℂ)⁻¹
    field_simp
  have normalized:(P.eval U:ℂ)⁻¹ • A.density t U =
      Poly.pass (A.E.log t U)*((g:ℂ)⁻¹ • A.gas t U):=by
    rw [Gallery.density,smul_smul,coef,mul_smul_comm]
  have quiet:(A.E.log t U).part C.quiet=0:=by
    by_cases h:Summable (fun j=>A.E.frame j t U)
    · exact Lamps.quiet_of_hasSum t U h
    rw [Lamps.log,tsum_eq_zero_of_not_summable h]
    rfl
  have neutral:(A.gas t U).part C.quiet=(g:ℂ):=
    Hard.packet_of_quiet A.K t U (Hard.packet_summing _ hard width pos t U)
  have unit:((g:ℂ)⁻¹ • A.gas t U).part C.quiet=1:=by
    rw [Poly.part_smul,neutral]
    exact inv_mul_cancel₀ hn
  rw [normalized,FormalOPE.RG10.PolyUtil.conn_mul (Poly.pass_part _ quiet) unit,
    FormalOPE.RG10.PolyUtil.conn_pass _ quiet]

end YM.Integration.WilsonReportNormalizedGallery
end
