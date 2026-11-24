import YM.Integration.WilsonOriginalTwoFlatIRStopped
import YM.Integration.WilsonOriginalTwoFlatIRMounted

import YM.Integration.WilsonMovingForkCapturedFee

/-! Purchase the actual change of positive receiver for the complete
independent capture on its rooted, mounted copy portfolio. -/
set_option autoImplicit false
set_option warningAsError true
set_option quotPrecheck false
set_option maxHeartbeats 1000000
noncomputable section
namespace YM.Integration.WilsonMovingForkMountedVote
open Function Filter Finset MeasureTheory Lattice Wilson RG Source Labels Marker Multi Gauge
open Push Push.AbsoluteSums QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Affinity QuadraticLocal.Poetry
open Planned.GuardedAtom Extra.Histories Next.Foundations RG16 RG16.Literal Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Pert.Asymptotics
open WilsonPositionProgramReporterBand WilsonIndependentCapturedPages
open WilsonOlderFreshGraphSlate WilsonRegisteredPairUnaryWallet WilsonOriginalMixedBlockRows
open WilsonRootedKioskOccupiedSlip WilsonThermometerUnitFilingCoarse WilsonThermometerUnitFilingFlatTelescope
open WilsonOriginalTwoFlatIRHalo WilsonOriginalTwoFlatTelescope WilsonOriginalTwoFlatGridScaling
open scoped Classical BigOperators Topology
open WilsonMovingForkHeterogeneousCut (Filed)
open WilsonMovingForkFiniteCell (Later)
open WilsonThermometerUnitFilingFourSquare (Arm)
open WilsonMovingForkCapturedFee (word)
open OPE Trace.Pilot
variable {G:Gauge}(R:Run G)
local notation "C" => R.family
local notation "Tchr" => R.family.path.levels
local notation "Sec" => R.family.localSection 0
local notation "par" => R.family.params

set_option linter.unusedVariables false in
theorem original (simple:G.Simple)(slow:∀m,((C).S.block m).val ≤ Real.log (Lambda (Tchr) m))
    (ready:WilsonReportLampForecast.Ready (Tchr))(D₀:XSpace.Run){stage u d:ℕ}
    (band:Band R D₀ stage)(v:WilsonIndependentCapturedPages.Stop R D₀ band u d)(cu:(C).ref 0 ≤ u)(P:ℕ):
    ∀ᶠ h:ℕ in atTop,let c:=band.reporter+h
    ∃uv:u ≤ v.date h,∀N per:ℕ,∀hc:c<N,
    let rep:=(C).path.rep N per c
    let g:=regulatorRun C N per c
    let site:=((C).side c per)
    ∀{V I:Type}[Fintype V][DecidableEq V][Fintype I]{π:Passport site V}
      (B:I → Earn.Binder π (Stock.census V))(t:V → ℕ){q ord seats shelf ext:ℕ}{σ U ξ K:ℝ}
      (T:∀i:I,Copy G (∑v∈(B i).mode.val,t v) q σ)(hs:0 ≤ σ)(dep:q ≤ ord)(oc:1 ≤ seats)
      (slots:Fintype.card V ≤ seats)(fit:(∑v,t v) ≤ shelf)
      (fund:Invoice.Supports rep.p U (rep.p.supportExponent+2) g σ ξ)
      (fare:Invoice.price rep.p U (ord+shelf+1) seats (rep.p.supportExponent+2) ξ G ≤ 
        (2:ℝ)^(ord+shelf+1)*(3*g⁻¹)^2)
      (incoming:(∑i:I,Real.exp (σ*(B i).length)*WilsonIndependentCollarSlateIntensity.amount (T i) (B i).center) ≤ K*(3*g⁻¹)^ext)
      (s:(Stock.census V).Mode)(Z:Support site)(center:0∈Z)(reside:∀a∈s.val,π.origin a∈Z)
      (rad:ℕ)(near:∀a∈s.val,separation (π.origin a) 0 ≤ rad)(inside:rad ≤ rep.p.B)
      (housed:Z⊆halo rep.p.B {0}){α:ℝ}(strip:rep.p.supportExponent ≤ α)
      (ou:Opened C 0 u per)(ov:Opened C 0 (v.date h) per)
      (reach:4*(P+(power s.val.card ((∑v,t v)+1+2+ext)+0+2)) ≤ d),
      let K₀:=((2:ℝ)^(ord+shelf+1))^2*max 1 K
      let e:=power s.val.card ((∑v,t v)+1+2+ext)+0+2
      let toll:=WilsonOriginalTwoFlatIRFiled.reserve (roof (Stock.census V) s (Sec) (par) α K₀) 1*3^e
      ∀(x:Wallet (room V)){n j k:ℕ}{grade:Fin n → ℕ}{S:Table R.family.book}
        {ℓ:Ultrafilter (ℕ×ℕ)}{field:∀i,S.Field (grade i)}(file:Filed R grade k)
        (arms:∀i,Arm R.family S (ℓ:Filter _) (grade i) (field i))(jk:j ≤ k)(pose:Fin n → Cover),
      let M:=word file arms jk pose (N,per)
      ∀(I:ℂ)(bill:WilsonMovingForkHeterogeneousCut.Invoice),
        (∀U,M c U=(WilsonOriginalTwoFlatIRMounted.value B t T g x U).part s) → 
        (∀i,v.date h ≤ i → i ≤ k → Integrable (numerator R N per i (M i)) (prior G _)) → 
        (∀i∈Finset.Ico c k,‖feeAt R N per u M i‖ ≤ bill.fine i) → 
        (∀i∈Finset.Ico (v.date h) c,‖feeAt R N per (v.date h) M i‖ ≤ bill.coarse i) → 
        ‖reading R (N:=N) (numerator R N per (v.date h) (M (v.date h))) (v.date h) le_rfl - I‖ ≤ bill.terminal → 
        toll*g^P ≤ bill.across → Later file arms jk uv (v.upper h) pose (N,per) I bill:=by
  filter_upwards [v.heard,WilsonOriginalTwoFlatIRStopped.original R simple slow ready D₀ band v cu P] with h live bridge
  refine ⟨live.1,?_⟩
  intro N per hc rep g site V I _ _ _ π B t q ord seats shelf ext σ U ξ K T hs dep oc slots fit
    fund fare incoming s Z center reside rad near inside housed α strip ou ov reach K₀ e toll x n j k grade S ℓ
    field file arms jk pose M result bill named hired fine coarse bottom allowed
  obtain ⟨whole,C₀,C₁,cp,hp,cost₀,cost₁,he,hg⟩:=WilsonOriginalTwoFlatIRMounted.original B t T hs dep oc slots fit rep.p fund fare incoming
  let L:=rendered (mounted B (fun i:I=>(T i).rows (WilsonOlderFreshGraphPointWallet.point (B i).center) disk)) rep.p g
  have compiled:numerator R N per (band.reporter+h) (M (band.reporter+h))=
      fun W=>(rep.eval W:ℂ)*(Poly.pass (bare L x W)).part s:=by
    funext W
    dsimp [numerator]
    rw [whole x W,named W]
  have one:1 ≤ K₀:=by
    apply one_le_mul_of_one_le_of_one_le
    · exact one_le_pow₀ (one_le_pow₀ (by norm_num))
    · exact le_max_left _ _
  have w:(Poly.toll (fun _:V=>(1:ℝ)) s)⁻¹ ≤ 1*(3*g⁻¹)^0:=by simp [Poly.toll]
  have purchase:=bridge N per hc L rfl s Z center reside rad near inside housed strip (fun _:V=>(1:ℝ))
    (fun _=>zero_lt_one) ((∑a,t a)+1+2+ext) 0 one (by norm_num) w cp hp cost₀ cost₁ he hg
    ou ov reach x (live.1.trans (v.upper h))
  refine ⟨hired,fine,?_,coarse,bottom⟩
  change ‖reading R (N:=N) (numerator R N per (band.reporter+h) (M (band.reporter+h))) u _-
    reading R (N:=N) (numerator R N per (band.reporter+h) (M (band.reporter+h))) (v.date h) _‖ ≤ _
  rw [compiled]
  exact purchase.trans allowed

end YM.Integration.WilsonMovingForkMountedVote
