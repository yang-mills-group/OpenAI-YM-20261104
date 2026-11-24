import YM.Integration.WilsonThermometerWeakSupported
import YM.Integration.WilsonThermometerMarchChambers

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakIssuedSites
open Function Filter Set MeasureTheory Lattice Wilson RG Source Extraction Table Spec
open PhysicalNext.Repeat.Legato RG17 FullVolume Climb Next.UVStress Trace.Pilot PhysMS XSpace XSpace.Normalize XSpace.Rose
open WilsonPositionThermometerCapStation WilsonPositionCapTransport WilsonPositionThermometerGradedSource
open WilsonPositionThermometerGradedReading WilsonPositionCorrectedCap WilsonSeparatedOriginalThermometerCells
open RG12 RG05Readout.Address WilsonThermometerOffsetTrajectory RG05Readout
open Labels Bid Push Extra.Histories Next.Extract PhysicalNext.Repeat Legato Bandage MergeProof Cells
open WilsonThermometerMarchProduct (field)
open WilsonThermometerMarchSource (reduce)
open Marker MergeProof.Accent Extra.Multi Menu Extra.Trajectories Push.GridApprox.Nil
open scoped Topology BigOperators Classical
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
variable {H : (Bel R.family.book).Hierarchy} {Y : Ultrafilter (ℕ×ℕ)}
variable (F : Final R.family f S) (J : ℝ→PhysMS.tower S) (V : Store G) (A : ℝ→Group R.family 6)
local notation "d" => WilsonThermometerFundedWeakCells.degree
local notation "slots" => (Stock.census (Fin 3))
local notation "levels" => R.family.path.levels

theorem original (simple:G.Simple) (shop:RG05Preconstruction.ReadoutPurchase R.b)
    (book:Book (f:=f) (l:=Y) (H:=H) A J) (lead:Leading F J)
    (E:∀ n,SectionData (R.family.labels.level n)) (W:Mark.Weave G)
    (P:∀ n,(ℕ×ℕ)→R.family.label n ≃ₗ[ℂ] R.family.label n) (b:Presentation R.family)
    (portfolio:∀ n,Mark.Portfolio R.family.params (E n) (W n))
    (house:Hearthside R.family E W P b (Bandage.fly R.alloy.B.a))
    (φ:Test 3) (legal:tsupport φ⊆conf 3) :
    ∃ t≥9, ∃ start:ℕ, ∀ᶠ r in trail, let Z:=adjusted F J V A r
       ∀ w≥start,R.family.S.a w*(RG16.Lambda levels w)^5≤r →
       ∃ M:Badge→ℝ,(∀ s,0≤M s) ∧ ∀ᶠ z:ℕ×ℕ in f.fuse,∃ h:w≤z.1,
       ∀ o : Fin 3→Site (R.family.side z.1 z.2),WilsonSeparatedOriginalThermometerCells.weight φ (positions (R:=R) r z) o≠0 →
       ∃ (X:(i:Fin 3)→Sight R.family (d i) z.2) (Q:(i:Fin 3)→Emblems R.family (d i)),
         (∀i,Enrolled R.makes R.doors (WilsonThermometerOffsetLedger.cash R) w z.1 z.2 (d i)
           (WilsonThermometerOffsetResidue.digits R z.1 z.2 (o i)) (X i) (Q i)) ∧
         (∀ j≥w,∀s:(slots).Mode,WilsonThermometerMarchFaces.inverse R t w j s ≤
           (levels).clock.hatBeta j ^ (3*(t+1)*(j-w+1))) ∧
         ∀ y:(i:Fin 3)→Palette R.family (d i),
           WilsonThermometerIntrinsicRoster.filed R d o (fun i=>reduce (y i)) X Q slots h t ∧
           (∀ j (hj:j≤z.1) s U,(WilsonThermometerIntrinsicRoster.density R d o (fun i=>reduce (y i))
              Q slots h hj U).part s = (R.family.path.rep z.1 z.2 j).eval U •
              actualTransport R.family (N:=z.1) (fun S₀=>∏ i∈s.val,
                WilsonThermometerWeakPublication.weight R w i (y i) *
                R.family.O z.1 z.2 (WilsonThermometerWeakEquationCost.column R (p:=z.2) (Q i) h (y i)) (o i) S₀) hj U) ∧
           ∀s:Badge,(∀i∈s,b.step (d i) z (field Z z.1 z.2 Finset.univ i)=
             b.step (d i) z (WilsonThermometerWeakEquationCost.column R (p:=z.2) (Q i) h (y i))) →
             ‖Wilson.moment (R.family.beta z.1 z.2) (fun U=>∏i∈s,R.family.O z.1 z.2
                (WilsonThermometerWeakEquationCost.column R (p:=z.2) (Q i) h (y i)) (o i) U) - row Z z o s‖ ≤
               7*(Real.exp (-(1/64:ℝ)*R.family.S.scale z.1)*(M s+WilsonThermometerFundedWeakCells.extra y)^3) := by
  obtain ⟨t,load,funded⟩:=WilsonThermometerWeakPublication.original R simple shop
  obtain ⟨w₀,valid⟩:=eventually_atTop.mp funded
  obtain ⟨p₀,support⟩:=WilsonThermometerMarchChambers.original R simple φ legal
  obtain ⟨w₁,apart⟩:=eventually_atTop.mp support
  obtain ⟨w₂,heard⟩:=WilsonThermometerWeakSupported.original F J V A simple book lead E W P b portfolio house φ legal
  refine ⟨t,load,max (max w₀ w₁) w₂,?_⟩
  filter_upwards [heard,show ∀ᶠ r:ℝ in trail,0<r from self_mem_nhdsWithin,
    show ∀ᶠ r:ℝ in trail,r<1 from mem_nhdsWithin_of_mem_nhds (gt_mem_nhds zero_lt_one)] with r signed rp small
  dsimp only
  intro w eligible room
  obtain ⟨left,right⟩:=max_le_iff.mp eligible
  obtain ⟨paid,scope⟩:=max_le_iff.mp left
  obtain ⟨M,pos,visits⟩:=signed w right
  refine ⟨M,pos,?_⟩
  filter_upwards [visits,(WilsonThermometerMarchSupported.period f).eventually_ge_atTop p₀] with z scores hp
  obtain ⟨h,hears⟩:=scores
  refine ⟨h,?_⟩
  intro o nonzero
  have inside:=WilsonOriginalThermometerFineCells.occupied φ (positions (R:=R) r z) o nonzero
  have geometry:=apart w scope z.2 hp z.1 h r rp small.le room o nonzero
  obtain ⟨X,Q,registered,prices,whole⟩:=valid w paid z.2 z.1 h o geometry
  refine ⟨X,Q,registered,prices,?_⟩
  intro y
  obtain ⟨filed,placed⟩:=whole y
  exact ⟨filed,placed,fun s=>hears s o inside (WilsonThermometerOffsetLedger.cash R) X Q registered y⟩

end YM.Integration.WilsonThermometerWeakIssuedSites
end

