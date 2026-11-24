import YM.Integration.WilsonOriginalCompanionFourValues
import YM.Integration.WilsonOriginalCompanionBeforePeer

/-! Every actually occupied canonical hard entry is withdrawn within the complete charged conditioned inventory. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalCompanionSpent
open QuadraticLocal QuadraticLocal.Earn Filter Set Finset MeasureTheory Lattice Wilson Labels RG Source Marker Push
open Push.Local RG12 Extra.Histories Extra.Histories.Relay Ac GridApprox.Nil MergeProof MergeProof.Accent MergeProof.Menu
open RG05Readout RG05Readout.Native RG05Readout.Address RG05Readout.Many RG05Readout.Pantry Records
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Mallow Motion Bandage
open Extra.Multi Extra.Trajectories ConnectedActivityE6 Pressure Extra.Iteration Next.Foundations Lotus
open Trace.Physical.GermGraph Lodestar WilsonOriginalGalleryTwins WilsonOriginalCompanionLinearFiling
open WilsonOriginalCompanionClearReturn WilsonThermometerUnitFilingCoarse WilsonThermometerOccupiedGallery
open private hard_le from YM.Integration.WilsonOriginalCompanionTwinIntake
open ActualRunKernelPackets Pert.Asymptotics
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G)(simple:G.Simple)
local notation "A"=>R.family.path.levels
local notation "J"=>Stock.census (Fin 3)
local notation "X"=>Unit×(Fin 3×Bool)
def tariff:ℝ:=120*premium*WilsonOriginalCompanionCorridorCurrency.constant

include simple in
private theorem late : ∀ᶠ f:ℕ in atTop,LocalComparison.forcedDivisor R.family f≤1/12:=by
  filter_upwards [WilsonOriginalCompanionHardCurrency.original R simple 0 0 1 0,
    (Next.Rank.Station.hat_rate (A) simple).eventually_ge_atTop 12] with f pay large
  have income:=pay 0 (by simp) f 1 le_rfl
  simp only [zero_mul,zero_add,pow_zero,pow_one] at income
  exact (le_div_iff₀ (by norm_num : (0:ℝ)<12)).2
    ((mul_le_mul_of_nonneg_left large (Real.sqrt_nonneg _)).trans income)

include simple in
theorem original (cater:Cater R.family R.doors)(bank:WilsonThermometerClusterProjectionBudget.Ready (A))
    (book:WilsonReportLampForecast.Ready (A))(c l q:ℕ):
    ∀ᶠ j:ℕ in atTop,∀(T I:Type) [Countable I],∀N p f (height:j+2≤f)(_fn:f≤N),
    (f-(j+2):ℕ)≤(c:ℝ)*Real.log (RG16.Lambda (A) f)+2 →
    let P:=R.family.path.rep N p f
    let κ:=LocalComparison.forcedDivisor R.family f
    ∀(o:Fin 3→Site (R.family.side f p))(D:Gallery T I o P (J))(x:T)(w:Fin 3→ℝ)
      (route:∀k,(X)→Site (R.family.side k p))(anchor:(X)),(∀v,0<w v) →
    route f=(o ∘ Prod.fst) ∘ Prod.snd →
    (∀k,j+1≤k → k<f → route k=((A).clock.op k p).ratio.parent ∘ route (k+1)) →
    0≤((A).budget f).supportExponent-2 →
    D.E.Paid w P.p.B (((A).budget f).supportExponent-2) 1 →
    D.K.Paid w P.p.B P.p.supportExponent (4*κ) →
    (∀v,coverNumber (R.family.path.rep N p (j+1)).p.B ({route (j+1) anchor,route (j+1) v}:Support _)≤l) →
    ((A).clock.op j p).ratio.parent (route (j+1) anchor)=0 →
    ∀u:ℕ,R.family.ref 0≤u → ∀uj:u≤j,Opened R.family 0 u p → Opened R.family 0 j p →
    ∀s:(J).Mode,let Y:=fun U=>(D.density x U).part s-P.eval U*(Poly.pass (D.E.log x U)).part s
    Integrable Y (prior G _) ∧ Poly.toll w s*‖reading R (N:=N) Y u (uj.trans (by omega))‖≤
      tariff*(regulatorRun R.family N p f)^q:=by
  obtain ⟨age,ready⟩:=eventually_atTop.mp ((late R simple).and (WilsonOriginalCompanionCorridorCurrency.reserve R simple c l q))
  filter_upwards [WilsonOriginalCompanionBeforeRoster.original R simple cater bank book,eventually_ge_atTop age]
    with j offer cutoff
  intro T I inst N p f height fn span P κ o D x w route anchor wp home parent expo regular bill close fixed u ref uj ou oj s Y
  have params:P.p=(A).budget f:=(R.makes.wilson.represents N p f fn).vac
  have within:((A).budget f).supportExponent-2≤P.p.supportExponent:=by rw [params];linarith
  let law:=((R.T.sticks N p).prices f (Nat.zero_le _) fn).1.valid
  have kp:0<κ:=Real.sqrt_pos.mpr (Real.exp_pos _)
  have earn:=ready f (by omega)
  let amp:ℝ:=(12*κ)⁻¹
  have big:1≤amp:=(one_le_inv₀ (by positivity :0<12*κ)).mpr (by linarith only [earn.1])
  have room:3*amp*(4*κ)=1:=by dsimp [amp];field_simp [kp.ne'];ring
  let half:=fun i=>Real.sqrt (w i)
  have hp:∀i,0<half i:=fun i=>Real.sqrt_pos.mpr (wp i)
  have sq:(fun i=>half i^2)=w:=funext (fun i=>Real.sq_sqrt (wp i).le)
  let uf:u≤f:=by omega
  let fare:=WilsonOriginalCompanionTwinCredit.fare R f j l
  have fnn:0≤fare:=by
    unfold fare WilsonOriginalCompanionTwinCredit.fare
    have good:0≤(A).clock.hatBeta f:=zero_le_one.trans ((A).fits.delayed f).le
    positivity
  have raw:D.K.Paid w P.p.B P.p.supportExponent 1:=Hard.mono _ bill (by linarith only [earn.1])
  have live:=QuadraticLocal.Tariff.integrable (J) o w wp D x ⟨regular,hard_le D.K wp within raw⟩ expo law
  have fund(z:ℂ)(hz:‖z‖≤3*amp):(gallery z D).K.Paid w P.p.B P.p.supportExponent 1:=by
    rw [←room]
    exact WilsonThermometerOccupiedHard.paid D.K z (by linarith) hz wp bill
  have node(z:ℂ)(hz:‖z‖≤3*amp):Integrable ((gallery z D).density x) (prior G _) ∧
      Poly.toll w s*‖reading R (N:=N) (fun U=>((gallery z D).density x U).part s) u uf‖≤premium*fare:=by
    let B:=gallery z D
    have soft:B.E.Paid (fun i=>half i^2) P.p.B (((A).budget f).supportExponent-2) 1:=by rw [sq];exact regular
    have hard:B.K.Paid (fun i=>half i^2) P.p.B (((A).budget f).supportExponent-2) 1:=by rw [sq];exact hard_le B.K wp within (fund z hz)
    have adm:=QuadraticLocal.Tariff.integrable (J) o _ (fun i=>pow_pos (hp i) 2) B x ⟨soft,hard⟩ expo law
    refine ⟨adm,?_⟩
    rw [←sq,←coordinate R (B.density x) adm s uf]
    exact WilsonOriginalCompanionClearReturn.original R B x half hp expo soft hard adm uf fnn
      (offer T I N p f height fn l o B x half route anchor hp home parent expo soft hard adm close fixed u ref uj ou oj) s
  have gross:=WilsonOriginalCompanionFourValues.original R D x w wp uf s amp (premium*fare) big live fund node
  refine ⟨gross.1,gross.2.trans ?_⟩
  have pp:0≤premium:=by unfold premium WilsonOriginalCompanionClearRange.ceiling;positivity
  calc 10*(premium*fare)/amp=120*premium*(κ*fare):=by simp only [amp,div_eq_mul_inv,inv_inv];ring
       _≤_:=mul_le_mul_of_nonneg_left (earn.2 j span N p fn) (by positivity)
       _=tariff*(regulatorRun R.family N p f)^q:=by unfold tariff;ring

end YM.Integration.WilsonOriginalCompanionSpent
end
