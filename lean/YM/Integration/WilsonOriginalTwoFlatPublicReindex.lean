import YM.Integration.WilsonOriginalTwoFlatPublicSameField

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatPublicReindex
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
  {I:Type}[Fintype I]
local notation "C" => R.family
local notation "P" => R.family.path.levels
local notation "a" => R.family.S.a
local notation "β" => (P).clock.hatBeta


open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonOriginalTwoFlatPublicHeard (Heard)
open WilsonThermometerUnitFilingFourPoolClock (outer longer)
open WilsonInvariantActionPosition (berth)
open PhysMS
open MS MS.Land FVA2 FVA2.Register


open WilsonPositionHomogeneousFrame (homogeneous)
open WilsonThermometerUnitFilingFourSquare WilsonThermometerUnitFilingCoarse
variable (Jr:ℝ→tower S)(Z:WilsonPrescription G)

theorem sampled (simple:G.Simple)(D T h:ℕ)(d:I → Fin (D+1))(x:∀i,RG17.Free C (d i).val)
    (M η δ:ℝ)(books:(s:{s:ℝ // 0<s ∧ s<δ}) → Book F (l:=l) H z D T s.val)(u:ℕ)
    (sale:WilsonOriginalTwoFlatPublicSameField.Sampled F Jr Z simple D T h d x M η δ books u)
    (p₀:ℕ)(E:Finset I)(inh:E.Nonempty){n:ℕ}(e:Fin n ≃ ↥E):
  ∃C₀:ℝ,0<C₀ ∧
      ∀ᶠ r in trail,0<r ∧ outer z h r<δ ∧
      ∀ρ:I→{s:ℝ // 0<s ∧ s<δ},(∀i,r ≤ (ρ i).val ∧ (ρ i).val ≤ outer z h r) →
      (∃i,(ρ i).val=r) →
      let m:=univ.sup fun i=>max (books (ρ i)).stock.j (books (ρ i)).W.k
      let j:=berth R 5 m
      ∃uj:u ≤ j,∀N p:ℕ,∀top:j<N,∀o:Fin n → Cover,(∀i,‖(C).S.gridPoint j (o i)‖ ≤ M*outer z h r) →
      (Pairwise fun i i'=>η*r ≤ ‖(C).S.gridPoint j (o i)-(C).S.gridPoint j (o i')‖) →
      ∀weak:Fin n→Bool,
      let v(k:Fin n):=homogeneous F Jr Z (ρ (e k)).val (d (e k)).val (x (e k))
      let Y:=word R (fun k:Fin n=>(d (e k)).val) j N p top.le o (fun k=>((books (ρ (e k))).rows (d (e k))).arm (weak k) (v k) |>.source (N,p))
      let amount:=C₀*(wilson z r)^p₀
      ‖gap R N p u (uj.trans top.le) Y‖ ≤ amount ∧ Heard R simple N p u Y amount :=by
  obtain ⟨C₀,pos,quotes⟩:=sale p₀ E inh
  refine ⟨C₀,pos,?_⟩
  filter_upwards [quotes] with r all
  refine ⟨all.1,all.2.1,?_⟩
  intro ρ span anchor m j
  obtain ⟨uj,read⟩:=all.2.2 ρ span anchor
  refine ⟨uj,?_⟩
  intro N p top o room apart weak v Y amount
  let O(i:E):Cover:=o (e.symm i)
  let forE(i:E):=homogeneous F Jr Z (ρ i).val (d i).val (x i)
  let row(i:E):=(((books (ρ i)).rows (d i)).arm (weak (e.symm i)) (forE i)).source (N,p)
  let entire:=word R (fun i:E=>(d i).val) j N p top.le O row
  have onE:Pairwise (fun i i':E=>η*r≤‖(C).S.gridPoint j (O i)-(C).S.gridPoint j (O i')‖):=
    fun i k ne=>apart (fun q=>ne (e.symm.injective q))
  have one:=read N p top O (fun i=>room (e.symm i)) onE (fun i=>weak (e.symm i))
  have eq:Y=entire:=by
    funext U
    apply Fintype.prod_equiv e
    intro k
    simp only [row,forE,v,RG16.Literal.snap,O,e.symm_apply_apply]
  change ‖gap R N p u (uj.trans top.le) Y‖ ≤ amount ∧ Heard R simple N p u Y amount
  rw [eq]
  exact one

end YM.Integration.WilsonOriginalTwoFlatPublicReindex
end
