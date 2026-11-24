import YM.Integration.WilsonOriginalTwoFlatPublicMovingSelection
import YM.Integration.WilsonOriginalTwoFlatPublicLimit

/-! On the elected extraction each original cutoff numerator approaches the
public moment. All proper faces keep their parent mesh, public books and
measured hard and soft bills at both actual stops. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatPublicObserved
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Motion
open Extraction Table Spec Trace.Pilot Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat.Legato Work.G08 Next.Rank Marker MergeProof Accent Extra.Multi
open RG05Readout RG05Readout.Address RG05Readout.Records Menu Extra.Trajectories Push.GridApprox.Nil
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetCylinder WilsonThermometerOffsetResidue
open WilsonThermometerOwnOffsetField WilsonThermometerMarchSource WilsonAddressedAlignedColumn
open WilsonAddressedPublicPool WilsonAddressedPublicCrown WilsonThermometerReflectedTrajectory
open scoped Classical Topology BigOperators
open WilsonReflectedPublicOrientedFaces
open Climb Maxwell Maxwell.Free MS.Land Next.Rank.Station MergeProof.East Next.UVStress Trace.Terrace Trace.Pilot GapsContact GapsContact.Seams
open GapsContact.Stamps Trace GapsContact.Ascent
open WilsonMeasuredPublicBank WilsonPositionProgramPublicStations WilsonReflectedPublicStationFare

open RG16 RG16.Literal OPE Overlay Bid Push.GridApprox PhysicalNext.Repeat.Mallow Bandage
open WilsonReflectedPublicStationFare

open WilsonOriginalTwoFlatPublicFare (charge)
open WilsonOriginalTwoFlatGridCapture (word)
open WilsonOriginalTwoFlatGridScaling (gap)

variable {G:Gauge}{R:Run G}{order:Extraction.Order}{S:Table R.family.book}
  (F:Final R.family order S){l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}
  {z:Trace.Terrace.Arch R.family}
  {I:Type}[Fintype I][DecidableEq I][Nonempty I]
local notation "C" => R.family
local notation "P" => R.family.path.levels
local notation "a" => R.family.S.a
local notation "β" => (P).clock.hatBeta


open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonOriginalTwoFlatPublicHeard (Heard)
open WilsonThermometerUnitFilingFourPoolClock (outer longer)
open WilsonInvariantActionPosition (berth)
open PhysMS

open WilsonOriginalTwoFlatPublicMovingSelection (Measured)
open WilsonThermometerUnitFilingCoarse WilsonThermometerUnitFilingFourSquare

def Observed (simple:G.Simple)(D T q h u:ℕ)(d:I→Fin (D+1))(E:Finset I)
    {δ:ℝ}(books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)(M η r:ℝ):Prop:=
  ∀(ρ:I→{s:ℝ // 0<s ∧ s<δ}), (∀i,r ≤ (ρ i).val ∧ (ρ i).val ≤ outer z h r) → (∃i,(ρ i).val=r) →
    let m:=univ.sup fun i=>max (books (ρ i)).stock.j (books (ρ i)).W.k
    let j:=berth R 5 m
    ∃uj:u ≤ j,∀{n:ℕ}(idx:Fin n ≃ E)(o:E → Cover),(∀i,‖(C).S.gridPoint j (o i)‖ ≤ M*outer z h r) →
    (Pairwise fun i i'=>η*r ≤ ‖(C).S.gridPoint j (o i)-(C).S.gridPoint j (o i')‖) →
    tag (a j) (fun i=>o (idx i))∈generic n → tag (a j) (fun i=>o (idx i))∈conf n →
    ∀weak:E→Bool,∀v:∀i:E,S.Field (d i).val,∀ε:ℝ,0<ε → ∀ᶠ p:ℕ×ℕ in l,∃top:j<p.1,
    let A(i:E):=(books (ρ i)).rows (d i)
    let Y:=word R (fun i:E=>(d i).val) j p.1 p.2 top.le o (fun i=>((A i).arm (weak i) (v i)).source p)
    let amount:=(∏i:E,charge F (A i) j (weak i) (v i))*((β j)^q)⁻¹
    let exact:=S.classMoment S (fun i=>(d (idx i)).val) (tag (a j) (fun i=>o (idx i))) (fun i=>v (idx i))
    ‖exact-(C).omega p.1 p.2 Y‖ ≤ ε ∧
      ‖exact-reading R (N:=p.1) (credit C p.1 p.2 0 Y u (uj.trans top.le)) u le_rfl‖ ≤ ε+amount ∧
      Heard R simple p.1 p.2 u Y amount

omit [DecidableEq I] [Nonempty I] in
theorem at_face (simple:G.Simple)(orderly:l ≤ order.fuse){D T q h u:ℕ}(d:I→Fin (D+1))(E:Finset I)
    {δ:ℝ}(books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val){M η r:ℝ}
    (full:Measured F simple D T q h u d E books M η r):
    Observed F simple D T q h u d E books M η r:=by
  intro ρ span anchor
  let m:=univ.sup fun i=>max (books (ρ i)).stock.j (books (ρ i)).W.k
  let j:=berth R 5 m
  obtain ⟨uj,fixed⟩:=full ρ span anchor
  refine ⟨uj,?_⟩
  intro n idx o inside apart gen sep weak v ε ep
  let arms(i:E):=((books (ρ i)).rows (d i)).arm (weak i) (v i)
  let physical:=S.classMoment S (fun i=>(d (idx i)).val) (tag (a j) (fun i=>o (idx i))) (fun i=>v (idx i))
  have approach:=WilsonReflectedPublicAlignedPoints.aligned F orderly j (fun i=>o (idx i)) gen sep (fun i=>arms (idx i))
  have late:∀ᶠ p:ℕ×ℕ in order.fuse,j<p.1:=by
    rw [Order.fused]
    exact Eventually.of_forall fun _=>order.mesh.cofinal.eventually_gt_atTop j
  filter_upwards [late.filter_mono orderly,(Metric.tendsto_nhds.mp approach) ε ep] with p top close
  simp only [dif_pos top.le] at close
  let Y:=word R (fun i:E=>(d i).val) j p.1 p.2 top.le o (fun i=>(arms i).source p)
  have same:word R (fun i=>(d (idx i)).val) j p.1 p.2 top.le (fun i=>o (idx i)) (fun i=>(arms (idx i)).source p)=Y:=by
    funext U
    exact Equiv.prod_comp idx (fun i:E=>(C).O p.1 p.2 ((arms i).source p)
      (((C).S.toDepth top.le p.2).embed (snap C j p.2 o i)) U)
  change dist ((C).omega p.1 p.2 (word R _ j _ _ top.le _ _)) physical < ε at close
  rw [same] at close
  have near:‖physical-(C).omega p.1 p.2 Y‖ ≤ ε:=by
    simpa only [dist_eq_norm,norm_sub_rev physical] using close.le
  obtain ⟨first,second⟩:=fixed p.1 p.2 top o inside apart weak v
  refine ⟨top,near,?_,second⟩
  exact (norm_sub_le_norm_sub_add_norm_sub _ ((C).omega p.1 p.2 Y) _).trans (add_le_add near first)

theorem original (fac:Facilities C order S)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    (D q h:ℕ)(d:I→Fin (D+1)){M η:ℝ}(one:1 ≤ M)(ep:0<η):
    ∃J u T:ℕ,∃δ:ℝ,∃books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val,
      0<δ ∧ Stop C 0 J u ∧ ∀ᶠ r in trail,0<r ∧ r ≤ outer z h r ∧ outer z h r<δ ∧
      ∀E:Finset I,E.Nonempty →
        Measured F fac.simpleGate D T q h u d E books M η r ∧ Observed F fac.simpleGate D T q h u d E books M η r:=by
  obtain ⟨J,u,T,δ,books,dp,stop,all⟩:=WilsonOriginalTwoFlatPublicMovingSelection.original F fac bliss slow D q h d one ep
  refine ⟨J,u,T,δ,books,dp,stop,?_⟩
  filter_upwards [all] with r h
  refine ⟨h.1,h.2.1,h.2.2.1,?_⟩
  intro E ne
  let both:=h.2.2.2 E ne
  exact ⟨both,at_face F fac.simpleGate bliss.lies d E books both⟩

end YM.Integration.WilsonOriginalTwoFlatPublicObserved
end
