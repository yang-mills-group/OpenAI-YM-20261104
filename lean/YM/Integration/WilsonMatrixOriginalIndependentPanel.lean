import YM.Integration.WilsonMatrixOriginalParentPurchase
import YM.Integration.WilsonMatrixOriginalIndependentCoupon
import YM.Integration.WilsonMatrixOriginalIndependentWallet
import YM.Integration.WilsonMatrixOriginalGermPeriod

/-! One before-period measurement of the signed positive-grade.  All independent forest
coefficients below use the exact budget, reporting date and labels of the selected Wilson panel. -/
noncomputable section
universe u
namespace YM.Integration.WilsonMatrixOriginalIndependentPanel
open Filter Function Set Finset MeasureTheory Lattice Wilson RG Tree Precision RG17 Source Marker Extraction Spec
open FullVolume Table Climb Maxwell Maxwell.Free Trace.Pilot Trace.Over Spin PhysMS OPE OPE.Therm
open Next.UVStress Next.Rank.Price PhysicalNext.Repeat.Legato SharpGram.Lenses FVA2 FVA2.Register
open Trace.Sundial WilsonInvariantActionSpectatorPrices WilsonLimitConstruction WilsonPositionHomogeneousFrame WilsonMatrixTicketLanesSmearedPivot WilsonMatrixTicketLanesSmearedRows
open WilsonInvariantActionPairProbe WilsonInvariantActionCalibratedColumn WilsonMatrixOriginalEarlierPanel
open WilsonInvariantActionCapturedProfile WilsonMatrixOriginalReportingMargin
open WilsonMatrixOriginalParentPurchase WilsonMatrixTicketLanesNativePrices
open WilsonMatrixOriginalIndependentColumns WilsonMatrixOriginalIndependentForest WilsonMatrixOriginalIndependentLimit
open MS.Local.Physical MS.Menus RGComparison.Core16.Astage
open private Covered at_inputs from YM.Integration.WilsonMatrixOriginalParentPurchase
open scoped Classical BigOperators Topology

variable {G:Gauge} {R:Run G} {f:Extraction.Order} {S:Table R.family.book} (F:Final R.family f S)
    (J:ℝ→tower S) (Z:WilsonPrescription G) {H:(Bel R.family.book).Hierarchy}
    (L:Layout F) {U:Filter (ℕ×ℕ)}
local notation "β" => R.family.path.levels.clock.hatBeta

/-- The same independent array gives the full germ, the finite raw MS expansion and the physical master. -/
def Columns (e:ℕ) (g:ℝ→ℝ) (a b:ℝ→R.family.label 4) (φ:Test 2):Prop:=
  ∀(B:Deck G)(U:Ultrafilter (ℕ×ℕ)),(U:Filter (ℕ×ℕ))≤L.lens→
    ∃(τ:ℕ→ℝ)(A:Axle.TransferLimit R.family R.makes U),Climate R U τ ∧
      (∀(r:ℝ)(w:R.family.label 4),R.family.ref 4≤L.level r→
        Tendsto (fun z:ℕ×ℕ=>(↑(R.family.S.a (L.level r)^4):ℂ)⁻¹ •
          Trace.Physical.GermGraph.page 4 z.2 (L.level r) (WilsonMatrixOriginalGermPeriod.captured R F L r w z))
          (U:Filter _) (𝓝 (L.shift 4 r w)) ∧
        Tendsto (fun z:ℕ×ℕ=>coefficient R B (L.level r) z.1 z.2 (atRef L 4 r z w))
          (U:Filter _) (𝓝 (fixed R B F L τ r w)) ∧
        (∑q:Glyph B 4,fixed R B F L τ r w q • Axle.full F 4 A (L.level r) (column (warehouse R) B 4 q))=
          master L 4 r w) ∧
      (∀ᶠr in trail,∀i:Fin 2, let w:=Fin.cons (α:=fun _:Fin 2=>R.family.label 4) (a r) (fun _=>b r) i
        ∑j:Glyph B 4,‖fixed R B F L τ r w j‖ ≤
          16*(R.family.path.levels.clock.hatBeta (L.level r))^e*fare (warehouse R) B 4) ∧
      WilsonMatrixOriginalIndependentCoupon.Filed F L (U:=(U:Filter (ℕ×ℕ))) B τ e g a b φ

theorem filed (simple:G.Simple) (paid:WilsonMatrixTicketLanesReportedPrepaid.Paid G R.kit)
    (grow:Tendsto L.level trail atTop) (e:ℕ) (g:ℝ→ℝ) (positive:∀ᶠr in trail,0<g r)
    (a b:ℝ→R.family.label 4) (φ:Test 2) (covered:Covered F L e a b)
    (issued:WilsonMatrixOriginalMatchedForest.Signed (U:=L.lens) F L e g a b φ) :
    Columns F L e g a b φ:=by
  intro B U cut
  obtain ⟨τ,A,clim,data⟩:=WilsonMatrixOriginalIndependentLimit.measured R B F L simple U cut
  refine ⟨τ,A,clim,fun r w age=>⟨WilsonMatrixOriginalGermPeriod.at_date R F L U cut r w age,
    data r w age⟩,?_,WilsonMatrixOriginalIndependentCoupon.cleared F L B simple paid U cut grow τ
      (fun r w age=>(data r w age).1) e g positive a b φ issued⟩
  filter_upwards [covered,grow.eventually_ge_atTop (R.family.ref 4)] with r store age
  intro i
  let w:=Fin.cons (α:=fun _:Fin 2=>R.family.label 4) (a r) (fun _=>b r) i
  exact WilsonMatrixOriginalIndependentWallet.cleared R B F L U cut τ r w age (data r w age).1
    ((R.family.path.levels.clock.hatBeta (L.level r))^e) (store i)

def Measured (δ g:ℝ→ℝ) : Prop :=
  ∃(D:Profiles R 4)(j:D.probes.index)(v₀:(standard R.family.labels).Ref 4)
    (hs:D.probes.shell j=WilsonMatrixTicketLanesTwoSites.shell R.family.labels 4 v₀)
    (e:ℕ)(deposit:ℝ→RG17.Free R.family 4→R.family.label 4)(χ:ℂ→L[ℝ]ℝ)(σ:ℝ),
    let φ:=WilsonInvariantActionCalibratedColumn.packet v₀ hs (test D j)
    let v:=(Bel R.family.book).project 4 v₀
    let a:=fun r=>deposit r (stepField R.family)
    let b:=fun r=>deposit r (freeInput F J Z 4 r v)
    let c:=tree (D.probes.shell j) (test D j) H 4 (stepField R.family)
    Row (H:=H) (U:=U) F J Z L δ g D j v₀ hs e deposit χ σ ∧
    LeadingRow (U:=U) F L a b φ c χ σ ∧ Detected (U:=U) F L g a b φ c χ σ ∧
    WilsonMatrixOriginalMatchedForest.Signed (U:=U) F L (e+1) g a b φ ∧ Columns F L (e+1) g a b φ

theorem on_run (simple:G.Simple) {ρ:ℝ} {T:Campaign R} (W:Campaign.Pillars R T)
    (funded:FundedOriginalProperties.{u} simple ρ W) (subsidy:WilsonReportColumnSubsidy.Eligible R.kit)
    (fund:WilsonMatrixTicketLanesReportedPrepaid.Paid G R.kit) (pace:WilsonWindowReportingPace.Slow R.kit)
    (Z:WilsonPrescription G) {B:ℕ} (large:17≤B) (v:Extraction.Order):
    ∃(w:Extraction.Order)(S:Table R.family.book)(F:Final R.family (v.refine w) S)
      (H:(Bel R.family.book).Hierarchy)(J:ℝ→tower S)(A:ℝ→Spin.change S 4)(δ:ℝ→ℝ)(L:Layout F),
      Leading F J ∧ (∀d:ℕ,∀ᶠr in trail,Frame.obedient F H (J r) d) ∧
      (∀ᶠr in trail,J r 4=A r) ∧ TendC F A δ ∧ Coupling G (glo A) ∧
      L.level=WilsonMeasuredWindow.stop R.family.path.levels simple B ∧ L.lens≤(v.refine w).fuse ∧
      Measured (H:=H) (U:=L.lens) F J Z L δ (glo A):=by
  obtain ⟨w,S,F,H,J,A,δ,L,lead,paid,same,cal,coupling,level,lens,old⟩:=
    WilsonMatrixOriginalParentPurchase.on_run simple W funded subsidy fund pace Z large v
  obtain ⟨D,j,v₀,hs,e,deposit,χ,σ,row,lower,high,issued⟩:=old
  let input:=(Bel R.family.book).project 4 v₀
  have measured₀:=row
  obtain ⟨_,_,_,_,_,_,_,market,_⟩:=measured₀
  have cover:=at_inputs F J Z L lead paid simple (by omega:0<B) level e deposit input market
  have grow:Tendsto L.level trail atTop:=by
    rw [level];exact WilsonMeasuredWindow.stop_tendsto _ simple _ (by omega)
  exact ⟨w,S,F,H,J,A,δ,L,lead,paid,same,cal,coupling,level,lens,D,j,v₀,hs,e,deposit,χ,σ,
    row,lower,high,issued,filed F L simple fund grow _ _ coupling.positive _ _ _ cover issued⟩

end YM.Integration.WilsonMatrixOriginalIndependentPanel
