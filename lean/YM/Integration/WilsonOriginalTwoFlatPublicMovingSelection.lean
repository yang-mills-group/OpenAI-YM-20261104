import YM.Integration.WilsonOriginalTwoFlatPublicBooks
import YM.Integration.WilsonOriginalTwoFlatPublicHeard
import YM.Integration.WilsonOriginalTwoFlatPublicMixedRadius
import YM.Integration.WilsonOriginalTwoFlatPublicOuter

/-! On one physical field book for each real radius, all proper ordinary
faces use the same full optical date, even if that face omits a near or far
mark. Both flat reports belong to the original Wilson numerator. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatPublicMovingSelection
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

def Measured (simple:G.Simple)(D T q h u:ℕ)(d:I→Fin (D+1))(E:Finset I)
    {δ:ℝ}(books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)(M η r:ℝ):Prop:=
  ∀(ρ:I→{s:ℝ // 0<s ∧ s<δ}), (∀i,r ≤ (ρ i).val ∧ (ρ i).val ≤ outer z h r) → (∃i,(ρ i).val=r) →
    let m:=univ.sup fun i=>max (books (ρ i)).stock.j (books (ρ i)).W.k
    let j:=berth R 5 m
    ∃uj:u ≤ j,∀N p:ℕ,∀hN:j<N,∀o:E → Cover,(∀i,‖(C).S.gridPoint j (o i)‖ ≤ M*outer z h r) →
    (Pairwise fun i i'=>η*r ≤ ‖(C).S.gridPoint j (o i)-(C).S.gridPoint j (o i')‖) →
    ∀weak:E→Bool,∀v:∀i:E,S.Field (d i).val,
    let A(i:E):=(books (ρ i)).rows (d i)
    let Y:=word R (fun i:E=>(d i).val) j N p hN.le o (fun i=>((A i).arm (weak i) (v i)).source (N,p))
    let amount:=(∏i:E,charge F (A i) j (weak i) (v i))*((β j)^q)⁻¹
    ‖gap R N p u (uj.trans hN.le) Y‖ ≤ amount ∧ Heard R simple N p u Y amount

theorem original (fac:Facilities C order S)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    (D q h:ℕ)(d:I→Fin (D+1)){M η:ℝ}(one:1 ≤ M)(ep:0<η):
    ∃J u T:ℕ,∃δ:ℝ,∃books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val,
      0<δ ∧ Stop C 0 J u ∧ ∀ᶠ r in trail,0<r ∧ r ≤ outer z h r ∧ outer z h r<δ ∧
        ∀E:Finset I,E.Nonempty → Measured F fac.simpleGate D T q h u d E books M η r:=by
  obtain ⟨_,_,_,L⟩:=fac.costlier
  obtain ⟨J,u,all⟩:=(RG16.Literal.forStop C fac.simpleGate L.toPackage 0).exists
  let stop:=all 0 le_rfl
  obtain ⟨T,δ,dp,⟨books⟩⟩:=WilsonOriginalTwoFlatPublicBooks.original F fac.simpleGate bliss D
  refine ⟨J,u,T,δ,books,dp,stop,?_⟩
  have ending:=WilsonOriginalTwoFlatPublicOuter.original F fac.simpleGate bliss h
  have later:=longer F fac.simpleGate bliss h
  have faces:∀ᶠ r in trail,∀E:Finset I,E.Nonempty → Measured F fac.simpleGate D T q h u d E books M η r:=by
    apply eventually_all.mpr
    intro E
    by_cases ne:E.Nonempty
    · haveI : Nonempty E:=ne.to_subtype
      have grants:=WilsonOriginalTwoFlatPublicMixedRadius.selected F L.toPackage (fun i:E=>i.val)
        fac.simpleGate bliss slow stop (fun i=>(d i).val) D T (2*h) q (fun i=>Nat.le_of_lt_succ (d i).isLt) one ep
      filter_upwards [later.eventually grants,ending] with r paid rate
      intro _ ρ span anchor
      let m:=univ.sup fun i=>max (books (ρ i)).stock.j (books (ρ i)).W.k
      let j:=berth R 5 m
      obtain ⟨i₀,near⟩:=anchor
      have iM:(books (ρ i₀)).W.k ≤ m:=(le_max_right ..).trans (Finset.le_sup (f:=fun i=>max (books (ρ i)).stock.j (books (ρ i)).W.k) (mem_univ i₀))
      have capture:a j ≤ r:=by
        have mj:m ≤ j:=(WilsonInvariantActionPosition.arrival R 5 m).1.le
        exact ((C).S.strictAnti.antitone (iM.trans mj)).trans
          (((WilsonReflectedPublicBulbBerth.mesh R _ (books (ρ i₀)).checked).trans (books (ρ i₀)).active.le).trans near.le)
      have bill:=paid r (fun i=>(ρ i).val) rate.1 span ⟨i₀,near⟩
        (fun i=>(books (ρ i)).rows (d i)) (fun i=>(books (ρ i)).checked) (fun i=>(books (ρ i)).active) (rate.2.2 j capture)
      obtain ⟨uj,fixed⟩:=bill
      refine ⟨uj,?_⟩
      intro N p hN o inside apart weak v
      have phase:=fixed N p hN o inside apart weak v
      refine ⟨phase,WilsonOriginalTwoFlatPublicHeard.earned R fac.simpleGate (uj.trans hN.le) _ ?_ phase⟩
      exact continuous_finsetProd _ fun i _=>(C).continuousO _ _ _ _ _
    · exact Eventually.of_forall fun _ proof=>False.elim (ne proof)
  filter_upwards [faces,ending,later.eventually ((gt_mem_nhds dp).filter_mono nhdsWithin_le_nhds)] with r hearing rate small
  exact ⟨rate.1,rate.2.1,small,hearing⟩

end YM.Integration.WilsonOriginalTwoFlatPublicMovingSelection
end
