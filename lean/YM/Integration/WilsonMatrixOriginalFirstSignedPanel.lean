import YM.Integration.WilsonMatrixOriginalSignedPanel
import YM.Integration.WilsonInvariantActionSubmittedRegular

/-! A fixed nonzero signed Ward detector and its original two funded regular tails. -/
set_option autoImplicit false
noncomputable section
universe u
namespace YM.Integration.WilsonMatrixOriginalFirstSignedPanel
open Filter Function Set MeasureTheory Lattice Wilson RG RG17 Source Marker Extraction Extraction.Order
open Table Spec Climb Maxwell Maxwell.Free Trace.Pilot Trace.Over Spin PhysMS OPE OPE.Therm
open Next.UVStress Next.Rank.Price PhysicalNext.Repeat.Legato SharpGram.Lenses FVA2 FVA2.Register
open WilsonPositionHomogeneousFrame WilsonMatrixTicketLanesSmearedPivot WilsonMatrixTicketLanesSmearedRows
open WilsonInvariantActionPairProbe WilsonInvariantActionIntegratedPair WilsonInvariantActionSpectatorPrices
open WilsonLimitConstruction WilsonMatrixOriginalSignedPanel WilsonInvariantActionCalibratedColumn
open scoped Classical Topology BigOperators
variable {G:Gauge} {R:Run G} {f:Extraction.Order} {S:Table R.family.book}
    (F:Final R.family f S) (J:ℝ→tower S) (Z:WilsonPrescription G)
    {H:(Bel R.family.book).Hierarchy} (lead:Leading F J)
    (paid:∀d:ℕ,∀ᶠr in trail,Frame.obedient F H (J r) d) (simple:G.Simple)
    {ρ:ℝ} {T:Campaign R} {P:Campaign.Pillars R T} (funded:FundedOriginalProperties.{u} simple ρ P)
    (pace:WilsonWindowReportingPace.Slow R.kit) (L:Layout F)
    {B:ℕ} (hB:0<B) (level:L.level=WilsonMeasuredWindow.stop R.family.path.levels simple B)
    {U:Filter (ℕ×ℕ)} [U.NeBot] (chosen:U ≤ L.lens)
    {u₀:Filter (ℕ×ℕ)} (bank:Mantle F u₀) (E:Services R.family f S) (pegs:Pegs bank L)
local notation "β" => R.family.path.levels.clock.hatBeta


private theorem packet_real {e : Exterior (standard R.family.labels)} (w : (standard R.family.labels).Ref 4)
    (same : e = WilsonMatrixTicketLanesTwoSites.shell R.family.labels 4 w) (t : Test (e.n+1))
    (real_test : ∀ x, t x = ((t x).re : ℂ)) :
    ∀ x, packet w same t x = (((packet w same t x).re : ℝ) : ℂ) := by
  subst e
  exact real_test

include lead paid simple funded pace hB level chosen E pegs in
theorem original {A:ℝ→Spin.change S 4} {δ g:ℝ→ℝ} (same:∀ᶠr in trail,J r 4=A r)
    (cent:∀ᶠr in trail,AlignV F.room.kernel F.sector H (A r)) (cal:TendC F A δ) (coupling:Coupling G g) :
    ∃ (D:Profiles R 4) (j:D.probes.index) (v₀:(standard R.family.labels).Ref 4)
      (hs:D.probes.shell j=WilsonMatrixTicketLanesTwoSites.shell R.family.labels 4 v₀)
      (e:ℕ) (deposit:ℝ→RG17.Free R.family 4→R.family.label 4) (χ:ℂ→L[ℝ]ℝ),
      let φ:=WilsonInvariantActionCalibratedColumn.packet v₀ hs (test D j)
      let v:=(Bel R.family.book).project 4 v₀
      let b:=fun r=>homogeneous F J Z r 4 v
      let y:=fun r=>J r 4 (stepField R.family)
      let c:=tree (D.probes.shell j) (test D j) H 4 (stepField R.family)
      Lower (f:=f) J b φ c χ ∧
      (∀ᶠr in trail,∀u:RG17.Free R.family 4,master L 4 r (deposit r u)=J r 4 u ∧
        ∀N n,L.level r ≤ N→quota R.family 4 (L.level r) N n (atRef L 4 r (N,n) (deposit r u)) ≤
          R.family.S.a (L.level r)^4*(β (L.level r)^e*‖u‖)) ∧
      ∀q:ℕ,∀ε>0,∀ᶠr in trail,
      let s:=2*1+q+1+25;let k:=WilsonInvariantActionPosition.berth R s (L.level r)
      let ev:=(s+2)*5+e
      let a:=deposit r (stepField R.family);let w:=deposit r (freeInput F J Z 4 r v)
      master L 4 r a=y r ∧ master L 4 r w=b r ∧
      ∀(hr:0<r)(t:ℕ),t+1=k → ∀cut:(N p:ℕ)→Fin (N+1),
      ∀ᶠ z:ℕ×ℕ in U,∀live:t<z.1,
      let claim:=atRef L 4 r z a;let probe:=atRef L 4 r z w
      ‖WilsonInvariantActionPromotedPair.tested R (p:=z.2) live claim probe (dilate hr φ)-
        profile R cut (S.representative 4 (y r)) (S.representative 4 (b r)) (dilate hr φ) z.1 z.2‖ ≤ ε*(g r)^q ∧
      ‖WilsonInvariantActionPromotedRegular.response R (per:=z.2) live claim probe
        (WilsonDegreeFourInheritedRange.height R (q+2*(ev+1)+2*ev) k) Complex.reCLM χ (dilate hr φ)‖
        ≤ ε*(g r)^q*(‖Complex.reCLM‖*‖χ‖) := by
  obtain ⟨D,sites,K,_hK,decode⟩ := WilsonMatrixTicketLanesSmearedPair.fixed F J Z lead paid simple 4
  obtain ⟨j,v₀,hs,e,deposit,earned⟩ := WilsonInvariantActionSubmittedRegular.original
    F J Z lead paid simple funded pace L hB level chosen bank E pegs D sites K decode same cent cal coupling
  let φ := packet v₀ hs (test D j)
  let v := (Bel R.family.book).project 4 v₀
  let b := fun r => homogeneous F J Z r 4 v
  let c := tree (D.probes.shell j) (test D j) H 4 (stepField R.family)
  have real_test : ∀ x, φ x = ((φ x).re : ℂ) :=
    packet_real v₀ hs (test D j) (fun _ => rfl)
  obtain ⟨χ,detected⟩ := WilsonMatrixOriginalSignedPanel.on_column F J simple same cal coupling
    b φ real_test c earned.1 earned.2.1
  refine ⟨D,j,v₀,hs,e,deposit,χ,detected,earned.2.2.2.2.1,?_⟩
  intro q ε he
  filter_upwards [earned.2.2.2.2.2 q ε he] with r h
  refine ⟨h.1,h.2.1,?_⟩
  intro hr t ht cut
  filter_upwards [h.2.2 hr t ht cut] with z priced live
  exact ⟨(priced live).1,(priced live).2 Complex.reCLM χ⟩

end YM.Integration.WilsonMatrixOriginalFirstSignedPanel
