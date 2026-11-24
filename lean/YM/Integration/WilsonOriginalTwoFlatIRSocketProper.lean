import YM.Integration.WilsonOriginalTwoFlatIRSocketMeshField
import YM.Integration.WilsonOriginalTwoFlatRoseProperSalary
import YM.Integration.WilsonOriginalTwoFlatPublicMixedMesh

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatIRSocketProper
open Filter Finset Set MeasureTheory Lattice Wilson RG Source Extraction Table Spec
open OPE OPE.Orbits RG12 RG17 PhysMS PhysicalNext.Repeat.Legato WilsonThermometerUnitFilingFourSquare
open XSpace XSpace.Rose
open scoped Topology Classical BigOperators
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
variable (Jr:ℝ → tower S)(Z:WilsonPrescription G)

open WilsonPositionThermometerGradedSource
local notation "heads" => source (C) (Finset.univ:Finset (Fin 3))

open WilsonOriginalTwoFlatRoseObserved (observed)
open WilsonOriginalTwoFlatRoseBook (group)
open WilsonOriginalTwoFlatRoseFaceLimits (result)

open WilsonOriginalTwoFlatRoseFaceLimits (names loc raw)
open WilsonOriginalTwoFlatRoseNominated (face)
open WilsonThermometerAlignedCells (mass placedAt atOrigin)
open scoped ContDiff
local notation "faceSet" => Finset (Fin 3)

theorem leading (simple:G.Simple)(lead:Leading F Jr)
    (paid:∀d:ℕ,∀ᶠr in trail,Frame.obedient F H (Jr r) d){W:Set (Points 3)}(compact:IsCompact W)(separated:W⊆conf 3)(s:faceSet):
    ∃A:ℝ,0≤A ∧ ∀ᶠr in trail,∀x∈W,
      ‖result R r (fun i=>homogeneous F Jr Z r (grade i) (heads i)) x s‖ ≤ A:=by
  let d(i):=(grade (names s i).val).val
  let g(i):RG17.Free C (d i):=heads (names s i).val
  let near:=loc s '' W
  have small:IsCompact near:=compact.image (WilsonOriginalTwoFlatRoseFaceLimits.continuous_loc s)
  have sep:near⊆conf (Fintype.card ↥s):=by
    rintro _ ⟨x,hx,rfl⟩
    exact WilsonOriginalTwoFlatRoseFaceLimits.separate s (separated hx)
  let free:=fun x=>(Bel (C).book).classMoment (Bel (C).book) d x g
  have smooth:ContinuousOn free (conf _):=
    ((Bel (C).book).class_smooth (Bel (C).book) (Maxwell.table_smooth (C).labels)
      (fun i=>⟨d i,g i⟩)).continuousOn
  obtain ⟨A,cap⟩:=(small.image_of_continuousOn (smooth.mono sep)).isBounded.exists_norm_le
  refine ⟨1+max 0 A,by positivity,?_⟩
  filter_upwards [WilsonPositionHomogeneousLeading.jets F Jr Z lead paid simple d g 0 small sep zero_lt_one] with r sale
  intro x hx
  let X:=loc s x
  have hit:X∈near:=⟨x,hx,rfl⟩
  let printed:=fun y=>S.classMoment S d (r • y) (fun i=>homogeneous F Jr Z r (d i) (g i))
  have upper:‖iteratedFDeriv ℝ 0 printed X‖ ≤
      ‖iteratedFDeriv ℝ 0 printed X-iteratedFDeriv ℝ 0 free X‖+‖iteratedFDeriv ℝ 0 free X‖:=
    norm_le_norm_sub_add .. 
  rw [norm_iteratedFDeriv_zero,norm_iteratedFDeriv_zero] at upper
  exact upper.trans (add_le_add (sale X hit) ((cap _ ⟨X,hit,rfl⟩).trans (le_max_right _ _)))

/-- A single original salary applies to every charged absolute reporting cell,
on the elected physical extraction, including unit and proper faces. -/
theorem original (simple:G.Simple)(lead:Leading F Jr)(bliss:Bliss F l z H)
    (slow:WilsonWindowReportingPace.Slow R.kit)
    (obedient:∀d:ℕ,∀ᶠr in trail,Frame.obedient F H (Jr r) d)(hl:(l:Filter _)≤order.fuse)
    {T:ℕ}{δ:ℝ}(dp:0<δ)(books:(r:{s:ℝ // 0<s ∧ s<δ}) → Book F (l:=l) H z 6 T r.val)
    (φ:Test 3):
    ∃T₀:ℝ,1≤T₀ ∧ ∀ᶠr in trail,∃inside:0<r ∧ r<δ,
      let f:=berth R 5 (univ.sup (fun _i:Fin 3=>max (books ⟨r,inside⟩).stock.j (books ⟨r,inside⟩).W.k))
      ∀lift:Next.UVStress.Lifts C (books ⟨r,inside⟩).k,let A:=group F Jr Z (books ⟨r,inside⟩) lift
      ∀ᶠp:UVIndex in (l:Filter _),∀live:f≤p.1,∀cell:WilsonReceivedChronologicalFixedRoseVariation.cells R φ r (f,p.2),
        ∀s:faceSet,‖WilsonOriginalTwoFlatRoseCentered.ordinary R A p.1 p.2
          (fun i=>((C).S.toDepth live p.2).embed (cell.val i)) s‖≤T₀:=by
  obtain ⟨τ,positive,confined⟩:=φ.hasCompactSupport.exists_cthickening_subset_open (conf_open _) φ.tsupport_subset
  let W:=Metric.cthickening τ (tsupport (φ:Points 3→ℂ))
  have compact:IsCompact W:=φ.hasCompactSupport.cthickening
  choose B nonneg funded using leading F Jr Z simple lead obedient compact confined
  have clock:=wilson_link F simple bliss.budgets bliss.keen bliss.lies
  have unit:(0:ℝ)^2<τ/12:=by simpa using div_pos positive (by norm_num:(0:ℝ)<12)
  have small:=((clock.conforms simple).pow 2).eventually (ge_mem_nhds unit)
  have grid:=WilsonOriginalTwoFlatPublicMixedMesh.original F simple bliss slow 6 T 0 (fun i:Fin 3=>grade i) books
  refine ⟨1+∑s,B s,by linarith [Finset.sum_nonneg (fun s (_:s∈(univ:Finset faceSet))=>nonneg s)],?_⟩
  filter_upwards [Filter.eventually_all.mpr funded,small,grid,
    (show ∀ᶠr:ℝ in trail,0<r from self_mem_nhdsWithin),(gt_mem_nhds dp).filter_mono nhdsWithin_le_nhds]
    with r known thin mesh rp narrow
  let station:=books ⟨r,rp,narrow⟩
  let f:=berth R 5 (univ.sup (fun _i:Fin 3=>max station.stock.j station.W.k))
  have price:(C).S.a f/r≤(wilson z r)^2:=(mesh (fun _=>⟨r,rp,narrow⟩) (fun _=>⟨le_rfl,by simp [outer]⟩) ⟨0,rfl⟩).1
  have width:4*(3:ℝ)*(C).S.a f≤τ*r:=by
    have debt:=(div_le_iff₀ rp).mp (price.trans thin)
    linarith only [debt]
  refine ⟨⟨rp,narrow⟩,?_⟩
  intro _reported lift A
  let v(i:Fin 3):=homogeneous F Jr Z r (grade i) (heads i)
  let arms(i:Fin 3):=(station.rows (grade i)).arm true (v i)
  have same(p:UVIndex)(i:Fin 3):(arms i).source p=WilsonNeutralOffsetCutoff.named R A p.1 p.2 i:=
    WilsonOriginalTwoFlatRoseBook.same F Jr Z books ⟨r,rp,narrow⟩ lift p.1 p.2 i
  filter_upwards [WilsonOriginalTwoFlatRoseFaceLimits.original R F A simple hl r rp v arms same
    compact confined (show (0:ℝ)<1 from zero_lt_one)] with p heard
  intro live cell s
  obtain ⟨x,placed,exactRow⟩:=WilsonOriginalTwoFlatIRSocketMeshField.original R φ rp live width cell
  rw [exactRow A s]
  have step:=heard s x placed
  rw [dist_eq_norm] at step
  exact (norm_le_norm_sub_add (WilsonOriginalTwoFlatRoseFaceLimits.raw R A r p x s) (result R r v x s)).trans
    (add_le_add step.le ((known s x placed).trans (single_le_sum (fun j _=>nonneg j) (mem_univ s))))

end YM.Integration.WilsonOriginalTwoFlatIRSocketProper
end
