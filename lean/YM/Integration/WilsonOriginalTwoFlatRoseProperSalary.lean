import YM.Integration.WilsonOriginalTwoFlatRoseBookedLimit
import YM.Integration.WilsonOriginalTwoFlatRoseVariation
import YM.Integration.WilsonPositionHomogeneousLeading

/-! The true proper ordinary readings on every occupied Rose cell have a uniform
cost after the physical regulator limits. The source of this cost is the
actual Book and its signed leading hierarchy on the compact test support. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatRoseProperSalary
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

private theorem leading (simple:G.Simple)(lead:Leading F Jr)
    (paid:∀d:ℕ,∀ᶠr in trail,Frame.obedient F H (Jr r) d)(φ:Test 3)(s:faceSet):
    ∃A:ℝ,0≤A ∧ ∀ᶠr in trail,∀x∈tsupport φ,
      ‖result R r (fun i=>homogeneous F Jr Z r (grade i) (heads i)) x s‖ ≤ A:=by
  let d(i):=(grade (names s i).val).val
  let g(i):RG17.Free C (d i):=heads (names s i).val
  let near:=loc s '' tsupport φ
  have small:IsCompact near:=φ.hasCompactSupport.image (WilsonOriginalTwoFlatRoseFaceLimits.continuous_loc s)
  have sep:near⊆conf (Fintype.card ↥s):=by
    rintro _ ⟨x,hx,rfl⟩
    exact WilsonOriginalTwoFlatRoseFaceLimits.separate s (φ.tsupport_subset hx)
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

theorem original (simple:G.Simple)(lead:Leading F Jr)
    (obedient:∀d:ℕ,∀ᶠr in trail,Frame.obedient F H (Jr r) d)(hl:(l:Filter _)≤order.fuse)
    {T:ℕ}{δ:ℝ}(dp:0<δ)(books:(r:{s:ℝ // 0<s ∧ s<δ}) → Book F (l:=l) H z 6 T r.val)
    (φ:Test 3):
    ∃T₀:ℝ,1≤T₀ ∧ ∀ᶠr in trail,∃inside:0<r ∧ r<δ,∀lift:Next.UVStress.Lifts C (books ⟨r,inside⟩).k,
      let A:=group F Jr Z (books ⟨r,inside⟩) lift
      ∀ᶠp:UVIndex in (l:Filter _),∀y, mass (R:=R) r p φ y≠0 →
        ∀s:faceSet,‖(C).omega p.1 p.2 (face R A y s)‖≤T₀:=by
  choose B positive earned using leading F Jr Z simple lead obedient φ
  refine ⟨1+∑s,B s,by linarith [Finset.sum_nonneg (fun s (_:s∈(univ:Finset faceSet))=>positive s)],?_⟩
  filter_upwards [Filter.eventually_all.mpr earned,
    (show ∀ᶠr:ℝ in trail,0<r from self_mem_nhdsWithin),
    (gt_mem_nhds dp).filter_mono nhdsWithin_le_nhds] with r known rp narrow
  let station:=books ⟨r,rp,narrow⟩
  refine ⟨⟨rp,narrow⟩,?_⟩
  intro lift A
  let v(i:Fin 3):=homogeneous F Jr Z r (grade i) (heads i)
  let arms(i:Fin 3):= (station.rows (grade i)).arm true (v i)
  have same(p:UVIndex)(i:Fin 3):(arms i).source p=WilsonNeutralOffsetCutoff.named R A p.1 p.2 i:=
    WilsonOriginalTwoFlatRoseBook.same F Jr Z books ⟨r,rp,narrow⟩ lift p.1 p.2 i
  have ready:∀ᶠp:UVIndex in (l:Filter _),∀i:Fin 3,(C).ref (grade i).val≤p.1:=
    Filter.eventually_all.mpr (fun i=>(large_mesh order ((C).ref (grade i).val)).filter_mono hl)
  filter_upwards [WilsonOriginalTwoFlatRoseFaceLimits.original R F A simple hl r rp v arms same
    φ.hasCompactSupport φ.tsupport_subset (show (0:ℝ)<1 from zero_lt_one),ready] with p near live
  intro y nonzero s
  obtain ⟨c,x,xhits,addressed⟩:=WilsonThermometerAlignedCells.supported (R:=R) r p φ nonzero
  have active:x∈tsupport φ:=subset_tsupport _ xhits
  have transport:=WilsonOriginalTwoFlatRoseCentered.translated R A p.1 p.2 live (atOrigin y) c s
  have original:(C).omega p.1 p.2 (face R A y s)=raw R A r p x s:=by
    change _=WilsonOriginalTwoFlatRoseCentered.ordinary R A p.1 p.2
      (WilsonSeparatedOriginalThermometerCells.positions (R:=R) r p x) s
    rw [addressed]
    exact transport.symm
  rw [original]
  have step:=near s x active
  rw [dist_eq_norm] at step
  exact (norm_le_norm_sub_add (raw R A r p x s) (result R r v x s)).trans
    (add_le_add step.le ((known s x active).trans (single_le_sum (fun j _=>positive j) (mem_univ s))))

end YM.Integration.WilsonOriginalTwoFlatRoseProperSalary
end
