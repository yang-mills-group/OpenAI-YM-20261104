import YM.Integration.WilsonOriginalTwoFlatIRSocketAppointment
import YM.Integration.WilsonIndependentConditionedStoppedFaculty

/-! The same capture issues the original signed socket at a stop admitted by the independent public ruler. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedStoppedSocket
open Filter Real Set Function Lattice Wilson RG OPE OPE.Log Source Labels
open PhysicalNext.Repeat.Legato WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Mer
open WilsonIndependentCapturedPages WilsonOriginalTwoFlatIRCapturedCross
open RG16 RG16.Literal Planned.GuardedAtom Extra.Histories Next.Foundations Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat Pert.Asymptotics WilsonPositionProgramReporterBand
open StressFlux.Matching Cells Analysis Table Spec Extraction Next.UVStress Next.Rank
open WilsonReceivedChronologicalFixedCellFee (factor capture)
open WilsonIndependentConditionedGramSpatialHost (date)
open WilsonOriginalPublicRelativeGramKineticMesh (thermal)
open scoped Classical Topology
variable {G:Gauge}(R:Run G)(simple:G.Simple)
local notation "A" => R.family.path.levels

include simple in
theorem cold {n:ℕ}(φ:Test n):∀ᶠ c:ℕ in atTop,
    8*thermal R c < factor R φ:=by
  let F:=factor R φ
  have fp:0<F:=WilsonReceivedChronologicalFixedCellFee.positive R φ
  filter_upwards [(Station.hat_rate A simple).eventually_gt_atTop ((8/F)^2)] with c heat
  have positive:0<(A).clock.hatBeta c:=zero_lt_one.trans ((A).fits.delayed c)
  have lt:8/F<sqrt ((A).clock.hatBeta c):=by
    have sq:=sq_sqrt positive.le
    have sp:=sqrt_nonneg ((A).clock.hatBeta c)
    have credit:0<8/F:=div_pos (by norm_num) fp
    nlinarith only [heat,sq,sp,credit]
  change 8*(sqrt ((A).clock.hatBeta c))⁻¹<F
  rw [←div_eq_mul_inv]
  exact (div_lt_iff₀ (sqrt_pos.mpr positive)).mpr (by simpa only [mul_comm] using (div_lt_iff₀ fp).mp lt)

theorem fits {n:ℕ}(φ:Test n){r:ℝ}(rp:0<r)(small:factor R φ*r≤R.family.S.a 0)
    {N per v d:ℕ}(hd:0<d)(live:capture R φ r≤N)(lease:8*thermal R (capture R φ r)<factor R φ)
    (gpos:0<regulatorRun R.family N per (capture R φ r))(gsmall:regulatorRun R.family N per (capture R φ r)≤1)
    (dist:R.family.S.a (capture R φ r)/R.family.S.a v≤(regulatorRun R.family N per (capture R φ r)^d)^2):
    v<date R simple r:=by
  let c:=capture R φ r
  let g:=regulatorRun R.family N per c
  have fp:=WilsonReceivedChronologicalFixedCellFee.positive R φ
  have inside:=WilsonCloseCaptureDate.bracket R.family.S (mul_pos fp rp) small
  have weak:g≤8*thermal R c:=(le_abs_self g).trans
    (WilsonOriginalPublicRelativeGramKineticMesh.original_gauge R simple c c N per le_rfl live)
  have one:g^d≤g:=by
    obtain ⟨l,rfl⟩:=Nat.exists_eq_add_one.mpr hd
    rw [pow_succ]
    exact mul_le_of_le_one_left gpos.le (pow_le_one₀ gpos.le gsmall)
  have twice:(g^d)^2≤g:=by
    rw [pow_two]
    exact (mul_le_of_le_one_right (pow_nonneg gpos.le _) (one.trans gsmall)).trans one
  have paid:=lt_of_le_of_lt (dist.trans twice) (weak.trans_lt lease)
  have finer:factor R φ*r<factor R φ*R.family.S.a v:=
    inside.2.trans_lt ((div_lt_iff₀ (R.family.S.a_pos v)).mp paid)
  have limit:=WilsonIndependentConditionedGramSpatialHost.fits R simple rp
  by_contra! mv
  exact (not_lt_of_ge ((R.family.S.strictAnti.antitone mv).trans limit)) ((mul_lt_mul_iff_right₀ fp).mp finer)

theorem original (slow:∀m,(R.family.S.block m).val ≤ log (Lambda A m))
    (ready:WilsonReportLampForecast.Ready A)(D₀:XSpace.Run){stage u d:ℕ}
    (band:Band R D₀ stage)(v:WilsonIndependentCapturedPages.Stop R D₀ band u d)(cu:R.family.ref 0 ≤ u)(hd:0<d)(P:ℕ)
    {n:ℕ}(φ:Test n)(floor:ℕ):
    ∃radius:ℝ,0<radius ∧ ∀r:ℝ,0<r → r≤radius →
    let c:=capture R φ r
    ∃h:ℕ,∃_same:c=band.reporter+h,∃uc:u≤c,∃vc:v.date h≤c,
      floor+1≤c ∧ factor R φ*r≤R.family.S.a 0 ∧ u≤v.date h ∧ v.date h<date R simple r ∧
      ∀N per:ℕ,c<N → Quote R N per u (v.date h) c P d uc vc:=by
  obtain ⟨stop,heard⟩:=eventually_atTop.mp v.heard
  obtain ⟨warm,room⟩:=eventually_atTop.mp (cold R simple φ)
  obtain ⟨radius,rp,sold⟩:=WilsonOriginalTwoFlatIRSocketAppointment.original R simple slow ready D₀ band v cu P φ
    (max floor (max (band.reporter+stop) warm))
  refine ⟨radius,rp,?_⟩
  intro r pos short c
  obtain ⟨h,same,uc,vc,shelf,small,quote⟩:=sold r pos short
  have old:stop≤h:=by omega
  have purchased:=heard h old
  have uniform:=purchased.2 c 0 (by omega)
  rw [←same] at uniform
  have warmAt:warm≤c:=by omega
  refine ⟨h,same,uc,vc,by omega,small,purchased.1,?_,quote⟩
  exact fits R simple φ pos small hd (N:=c) (per:=0) le_rfl (room c warmAt) uniform.1 uniform.2.1 uniform.2.2.1

end YM.Integration.WilsonIndependentConditionedStoppedSocket
