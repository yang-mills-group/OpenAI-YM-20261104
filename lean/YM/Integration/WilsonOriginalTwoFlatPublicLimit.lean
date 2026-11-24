import YM.Integration.WilsonOriginalTwoFlatPublicSelection
import YM.Integration.WilsonReflectedPublicAlignedPoints

/-! The measured unselected limit and the fixed-flat report of exactly its
original numerator have the reflected error at aligned public sites. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatPublicLimit
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
  {z:Trace.Terrace.Arch R.family}{lo wid teach}(L:Package R.family wid lo teach)
  {I:Type}[Fintype I][DecidableEq I][Nonempty I]
local notation "C" => R.family
local notation "P" => R.family.path.levels
local notation "a" => R.family.S.a
local notation "β" => (P).clock.hatBeta

open WilsonThermometerUnitFilingCoarse WilsonReflectedPublicAlignedPoints
open WilsonThermometerUnitFilingFourSquare RG16.Literal

include F in
theorem at_nodes {n j u:ℕ}(orderly:l ≤ order.fuse)(uj:u ≤ j)(d:Fin n→ℕ)(v:∀i,S.Field (d i))
    (o:Fin n → Cover)(gen:tag (a j) o∈generic n)(sep:tag (a j) o∈conf n)
    (arms:∀i,Arm C S l (d i) (v i))(B:ℝ)
    (finite:∀N p:ℕ,∀top:j<N,
      ‖gap R N p u (uj.trans top.le) (word R d j N p top.le o (fun i=>(arms i).source (N,p)))‖ ≤ B):
    ∀ε:ℝ,0<ε → ∀ᶠ p:ℕ×ℕ in l,∃top:j<p.1,
      let Y:=word R d j p.1 p.2 top.le o (fun i=>(arms i).source p)
      ‖S.classMoment S d (tag (a j) o) v-reading R (N:=p.1) (credit C p.1 p.2 0 Y u (uj.trans top.le)) u le_rfl‖  ≤  ε+B:=by
  intro ε ep
  have approach:=WilsonReflectedPublicAlignedPoints.aligned F orderly j o gen sep arms
  have late:∀ᶠ p:ℕ×ℕ in order.fuse,j<p.1:=by
    rw [Order.fused]
    exact Eventually.of_forall fun _=>order.mesh.cofinal.eventually_gt_atTop j
  filter_upwards [late.filter_mono orderly,(Metric.tendsto_nhds.mp approach) ε ep] with p top near
  refine ⟨top,?_⟩
  simp only [dif_pos top.le] at near
  let Y:=word R d j p.1 p.2 top.le o (fun i=>(arms i).source p)
  change dist ((C).omega p.1 p.2 Y) _ < ε at near
  have e:‖S.classMoment S d (tag (a j) o) v-(C).omega p.1 p.2 Y‖  ≤  ε:=by
    simpa [dist_eq_norm,norm_sub_rev (S.classMoment S d (tag (a j) o) v)] using near.le
  exact (norm_sub_le_norm_sub_add_norm_sub _ ((C).omega p.1 p.2 Y) _).trans (add_le_add e (finite _ _ top))

include L in
theorem original (simple:G.Simple)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    (D q:ℕ){n:ℕ}[Nonempty (Fin n)](d:Fin n→Fin (D+1)){M η:ℝ}(one:1 ≤ M)(ep:0<η):
    ∃J u T:ℕ,Stop C 0 J u ∧ ∀ᶠ r in trail,∃k:ℕ,
    ∃stock:Bank F l D (WilsonThermometerUnitFilingFourPoolShell.radius z T r)
        (dock (WilsonThermometerUnitFilingFourPoolShell.radius z T r)^T),
    ∃ (W:Vane R.family k) (fits:D ≤ k) (V:∀e:Fin (D+1),Spin.change S e.val)
      (A:∀e:Fin (D+1),Pair F stock (Nat.le_of_lt_succ e.isLt) W fits (V e) r),
      W.checked order H k ∧ W.wheel.r=r ∧
      let m:=max stock.j W.k
      let j:=WilsonInvariantActionPosition.berth R 5 m
      ∃uj:u ≤ j,∀o:Fin n → Cover,(∀i,‖(C).S.gridPoint j (o i)‖ ≤ M*r) →
      (Pairwise fun i i'=>η*r ≤ ‖(C).S.gridPoint j (o i)-(C).S.gridPoint j (o i')‖) →
      tag (a j) o∈generic n → tag (a j) o∈conf n →
      ∀weak:Fin n→Bool,∀v:∀i,S.Field (d i).val,∀ε:ℝ,0<ε → ∀ᶠ p:ℕ×ℕ in l,∃top:j<p.1,
      let Y:=word R (fun i=>(d i).val) j p.1 p.2 top.le o (fun i=>((A (d i)).arm (weak i) (v i)).source p)
      ‖S.classMoment S (fun i=>(d i).val) (tag (a j) o) v-
        reading R (N:=p.1) (credit C p.1 p.2 0 Y u (uj.trans top.le)) u le_rfl‖  ≤ 
        ε+(∏i,charge F (A (d i)) j (weak i) (v i))*((β j)^q)⁻¹:=by
  obtain ⟨J,u,T,stop,stocks⟩:=WilsonOriginalTwoFlatPublicSelection.original F L simple bliss slow D q d one ep
  refine ⟨J,u,T,stop,?_⟩
  filter_upwards [stocks] with r bought
  obtain ⟨k,stock,W,fits,V,A,checked,active,uj,fixed⟩:=bought
  refine ⟨k,stock,W,fits,V,A,checked,active,uj,?_⟩
  intro o inside apart gen sep weak v
  apply at_nodes F bliss.lies uj _ v o gen sep (fun i=>(A (d i)).arm (weak i) (v i))
  exact fun N p hN=>fixed N p hN o inside apart weak v

end YM.Integration.WilsonOriginalTwoFlatPublicLimit
end
