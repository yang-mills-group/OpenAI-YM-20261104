import YM.Integration.WilsonOriginalTwoFlatIRHeard
import YM.Integration.WilsonOriginalTwoFlatIRPurchase

/-! The ordinary scalar after the genuine physical phase receipt, continued
on the original linear kernels at two stops using the freshly compiled
complete independent product at capture. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 1000000
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatIRCapturedCross
open Function Filter Finset MeasureTheory Lattice Wilson RG Source Labels Marker Multi Gauge
open Push Push.AbsoluteSums QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Affinity QuadraticLocal.Poetry
open Planned.GuardedAtom Extra.Histories Next.Foundations RG16 RG16.Literal Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Pert.Asymptotics
open WilsonPositionProgramReporterBand WilsonIndependentCapturedPages
open WilsonOlderFreshGraphSlate WilsonRegisteredPairUnaryWallet WilsonOriginalMixedBlockRows
open WilsonRootedKioskOccupiedSlip WilsonThermometerUnitFilingCoarse WilsonThermometerUnitFilingFlatTelescope
open WilsonOriginalTwoFlatIRHalo WilsonOriginalTwoFlatTelescope WilsonOriginalTwoFlatGridScaling
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G)
local notation "C" => R.family
local notation "Tchr" => R.family.path.levels
local notation "Sec" => R.family.localSection 0
local notation "par" => R.family.params


set_option linter.unusedVariables false in
def Quote (N per u v c P depth:ℕ)(uc:u≤c)(vc:v≤c):Prop:=
    let rep:=(C).path.rep N per c
    let g:=regulatorRun C N per c
    let site:=((C).side c per)
    ∀{V I:Type}[Fintype V][DecidableEq V][Fintype I]{π:Passport site V}
      (B:I→Earn.Binder π (Stock.census V))(t:V→ℕ){q ord seats shelf ext:ℕ}{σ U ξ K:ℝ}
      (T:∀i:I,Copy G (∑v∈(B i).mode.val,t v) q σ)(hs:0 ≤ σ)(dep:q ≤ ord)(oc:1 ≤ seats)
      (slots:Fintype.card V ≤ seats)(fit:(∑v,t v) ≤ shelf)
      (fund:Invoice.Supports rep.p U (rep.p.supportExponent+2) g σ ξ)
      (fare:Invoice.price rep.p U (ord+shelf+1) seats (rep.p.supportExponent+2) ξ G ≤
        (2:ℝ)^(ord+shelf+1)*(3*g⁻¹)^2)
      (incoming:(∑i:I,Real.exp (σ*(B i).length)*WilsonIndependentCollarSlateIntensity.amount (T i) (B i).center) ≤ K*(3*g⁻¹)^ext)
      (s:(Stock.census V).Mode)(Z:Support site)(center:0∈Z)(reside:∀a∈s.val,π.origin a∈Z)
      (rad:ℕ)(near:∀a∈s.val,separation (π.origin a) 0 ≤ rad)(inside:rad ≤ rep.p.B)
      (housed:Z⊆halo rep.p.B {0}){α:ℝ}(strip:rep.p.supportExponent ≤ α)
      (ou:Opened C 0 u per)(ov:Opened C 0 v per)
      (reach:4*(P+(power s.val.card ((∑v,t v)+1+2+ext)+0+2)) ≤ depth),
      let K₀:=((2:ℝ)^(ord+shelf+1))^2*max 1 K
      let e:=power s.val.card ((∑v,t v)+1+2+ext)+0+2
      let toll:=WilsonOriginalTwoFlatIRFiled.reserve (roof (Stock.census V) s (Sec) (par) α K₀) 1*3^e
      ∀(x:Wallet (room V))(F:Config G site→ℂ),
      (∀U,((rep.eval U:ℂ)⁻¹)*F U=(WilsonOriginalTwoFlatIRMounted.value B t T g x U).part s)→
      ‖reading R (N:=N) F u uc-reading R (N:=N) F v vc‖≤toll*g^P

set_option linter.unusedVariables false in
theorem original (simple:G.Simple)(slow:∀m,((C).S.block m).val ≤ Real.log (Lambda (Tchr) m))
    (ready:WilsonReportLampForecast.Ready (Tchr))(D₀:XSpace.Run){stage u d:ℕ}
    (band:Band R D₀ stage)(v:WilsonIndependentCapturedPages.Stop R D₀ band u d)(cu:(C).ref 0 ≤ u)(P:ℕ):
    ∀ᶠ h:ℕ in atTop,let c:=band.reporter+h
    ∀N per:ℕ,∀hc:c<N,
    ∀uc:u≤c,Quote R N per u (v.date h) c P d uc (v.upper h):=by
  filter_upwards [WilsonOriginalTwoFlatIRStopped.original R simple slow ready D₀ band v cu P] with h bridge
  intro c N per hc uc
  unfold Quote
  intro rep g site V I _ _ _ π B t q ord seats shelf ext σ U ξ K T hs dep oc slots fit
    fund fare incoming s Z center reside rad near inside housed α strip ou ov reach K₀ e toll x F filed
  obtain ⟨whole,C₀,C₁,cp,hp,cost₀,cost₁,he,hg⟩:=WilsonOriginalTwoFlatIRMounted.original B t T hs dep oc slots fit rep.p fund fare incoming
  let L:=rendered (mounted B (fun i:I=>(T i).rows (WilsonOlderFreshGraphPointWallet.point (B i).center) disk)) rep.p g
  have compiled:F=fun U=>(rep.eval U:ℂ)*(Poly.pass (bare L x U)).part s:=by
    funext U
    have pos:((rep.eval U):ℂ)≠0:=Complex.ofReal_ne_zero.mpr (Multi.AxisShift.chosen_positive R.makes.wilson hc.le U).ne'
    rw [whole x U,←filed U,←mul_assoc,mul_inv_cancel₀ pos,one_mul]
  have one:1≤K₀:=one_le_mul_of_one_le_of_one_le (one_le_pow₀ (one_le_pow₀ (by norm_num))) (le_max_left _ _)
  have wage:(Poly.toll (fun _:V=>(1:ℝ)) s)⁻¹≤1*(3*g⁻¹)^0:=by simp [Poly.toll]
  have earned:=bridge N per hc L rfl s Z center reside rad near inside housed strip (fun _:V=>(1:ℝ))
    (fun _=>zero_lt_one) ((∑v,t v)+1+2+ext) 0 one (by norm_num) wage cp hp cost₀ cost₁ he hg ou ov reach x uc
  rw [compiled];exact earned

end YM.Integration.WilsonOriginalTwoFlatIRCapturedCross
