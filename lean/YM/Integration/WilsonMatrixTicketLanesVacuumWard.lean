import YM.Integration.WilsonMatrixTicketLanesVacuumCourse
import YM.Integration.WilsonMatrixTicketLanesVacuumElection
import YM.Integration.WilsonMatrixTicketLanesRegisteredWard
import YM.Integration.WilsonMatrixTicketLanesRegisteredTilt

/-! The measured nonzero Ward row and its true previous occupied vacuum on the same submitted fields. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
universe u
namespace YM.Integration.WilsonMatrixTicketLanesVacuumWard
open Filter Function Set Finset MeasureTheory Lattice Wilson RG Tree Precision RG17 Source Marker Extraction Extraction.Order Spec
open Table Climb Maxwell Maxwell.Free Trace.Pilot Trace.Over Spin PhysMS OPE OPE.Therm Next.UVStress
open PhysicalNext.Repeat.Legato SharpGram.Lenses FVA2 FVA2.Register Pert.Asymptotics
open WilsonPositionHomogeneousFrame WilsonMatrixTicketLanesSmearedPivot WilsonMatrixTicketLanesSmearedRows
open WilsonInvariantActionPairProbe WilsonInvariantActionSpectatorPrices WilsonInvariantActionCalibratedColumn
open Trace.Sundial WilsonLimitConstruction WilsonMatrixOriginalEarlierPanel WilsonInvariantActionPairCovariance
open WilsonMatrixTicketLanesRegulatorColumn WilsonMatrixTicketLanesRegisteredCovariance
open private at_inputs on_two from YM.Integration.WilsonMatrixOriginalParentPurchase
open scoped Classical Topology BigOperators
variable {G:Gauge} (R:Run G) {f:Extraction.Order} {S:Table R.family.book} (F:Final R.family f S)
  (J:ℝ→tower S) (Z:WilsonPrescription G) {H:(Bel R.family.book).Hierarchy} (L:Layout F)
  {U:Filter (ℕ×ℕ)}
open WilsonInvariantActionPriorHearing WilsonMatrixTicketLanesVacuumPanel
local notation "β" => R.family.path.levels.clock.hatBeta

open IterationFour IterationFour.Vacuum WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic OriginalMarkedRunAction

def OnPair (d a K load q:ℕ) (v w:ℝ→R.family.label 4) (φ:Test 2) (χ:ℂ→L[ℝ]ℝ) (g:ℝ→ℝ) (ε radiusFee:ℝ):Prop:=
  ∃credit:Credit,∃δ>0,∀ᶠr in trail,∃k,L.level r=k+1 ∧ ∃width>0,
    width⁻¹≤zz R.family.path.levels (k+1) ∧ ∃P:(N:ℕ)→k+1<N→SeriesA G,
    (∀N (live:k+1<N),WilsonMatrixTicketLanesVacuumCourse.Filed R d a K load δ radiusFee credit k N live width (P N live)) ∧
    ∀hr:0<r,∀ᶠz:ℕ×ℕ in U,∃live:k+1<z.1,∃birth:R.family.ref 4≤k+1,
      let marks:=Fin.cons (α:=fun _:Fin 2=>R.family.label 4) (atRef L 4 r z (v r)) (fun _=>atRef L 4 r z (w r))
      let V:=R.family.path.levels
      let C:=credit.buy (zz V (k+1))+zz V (k+1)*V.clock.loopCap (k+1)
      ∀o:(Fin 2→Site (R.family.side z.1 z.2))→Site (R.family.side (k+1) z.2),
      ∃h:(Fin 2→Site (R.family.side z.1 z.2))→ readings
        (Config G (R.family.side k z.2)×Config G (R.family.side (k+1) z.2)),
      (∀x V U,(h x).val (V,U)=WilsonMatrixTicketLanesVacuumSpring.difference R (N:=z.1) (P z.1 live) width C (2+a) (o x) U) ∧
      HasDerivAt (WilsonMatrixTicketLanesRegisteredTilt.full R live birth marks (dilate hr φ) χ h)
        (signed R .all live.le birth marks (dilate hr φ) χ h) 0 ∧
      ∀kind:Kind,|signed R kind live.le birth marks (dilate hr φ) χ h|≤ε*(g r)^q

theorem on_row (simple:G.Simple) (heat:Poetry R.family.path.levels) (v:ℕ→Gear G→ℝ)
    (early:WilsonMatrixTicketLanesVacuumElection.Earlier v R.kit)
    (lead:Leading F J) (obey:∀d:ℕ,∀ᶠr in trail,Frame.obedient F H (J r) d)
    (chosen:U≤L.lens) {B:ℕ} (wide:17≤B) (level:L.level=WilsonMeasuredWindow.stop R.family.path.levels simple B)
    {δ g:ℝ→ℝ} (coupling:Coupling G g) (D:Profiles R 4) (j:D.probes.index) (v₀:(standard R.family.labels).Ref 4)
    (site:D.probes.shell j=WilsonMatrixTicketLanesTwoSites.shell R.family.labels 4 v₀) (e:ℕ)
    (deposit:ℝ→RG17.Free R.family 4→R.family.label 4) (χ:ℂ→L[ℝ]ℝ) (sgn:ℝ)
    (record:Row (H:=H) (U:=U) F J Z L δ g D j v₀ site e deposit χ sgn):
    let φ:=WilsonInvariantActionCalibratedColumn.packet v₀ site (test D j)
    let b:=(Bel R.family.book).project 4 v₀
    let first:=fun r=>deposit r (stepField R.family)
    let second:=fun r=>deposit r (freeInput F J Z 4 r b)
    ∀d a K load q:ℕ,∀ε>0,∀η>0,OnPair (U:=U) R F L d a K load q first second φ χ g ε η:=by
  let φ:=WilsonInvariantActionCalibratedColumn.packet v₀ site (test D j)
  let b:=(Bel R.family.book).project 4 v₀
  let first:=fun r=>deposit r (stepField R.family)
  let second:=fun r=>deposit r (freeInput F J Z 4 r b)
  have cover:=at_inputs F J Z L lead obey simple (by omega:0<B) level e deposit b record.2.2.2.2.2.2.2.1
  obtain ⟨held,pace,rows,paths,old,cov⟩:=early
  obtain ⟨mark,check⟩:=WilsonOldActionForecast.issued R old
  dsimp only []
  intro d a K load q ε ep η hp
  obtain ⟨credit,ρ,rpos,course⟩:=WilsonMatrixTicketLanesVacuumCourse.purchased R F L simple pace held heat
    mark check cov v rows paths wide level chosen coupling d a K load (e+1) q φ ep hp
  refine ⟨credit,ρ,rpos,?_⟩
  filter_upwards [course,cover] with r purchase input
  obtain ⟨k,date,width,wp,time,P,chart,capital⟩:=purchase
  refine ⟨k,date,width,wp,time,P,chart,?_⟩
  intro hr
  filter_upwards [capital hr] with z sale
  obtain ⟨live,birth,payment⟩:=sale
  refine ⟨live,birth,?_⟩
  let marks:=Fin.cons (α:=fun _:Fin 2=>R.family.label 4) (atRef L 4 r z (first r)) (fun _=>atRef L 4 r z (second r))
  have charged (i:Fin 2):quota R.family 4 (k+1) z.1 z.2 (marks i)≤R.family.S.a (k+1)^4*β (k+1)^(e+1):=by
    rw [←date];dsimp only [marks];rw [on_two]
    exact input i z.1 z.2 (date.trans_le live.le)
  dsimp only []
  intro o
  obtain ⟨h,values,prices⟩:=payment marks charged χ record.1 o
  exact ⟨h,values,(WilsonMatrixTicketLanesRegisteredTilt.measured R live birth marks (dilate hr φ) χ h).2,prices⟩

end YM.Integration.WilsonMatrixTicketLanesVacuumWard
