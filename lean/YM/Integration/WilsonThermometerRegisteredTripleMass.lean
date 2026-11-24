import YM.Integration.WilsonThermometerRegisteredPlantedFaces
import YM.Integration.WilsonThermometerRegisteredCells
import YM.Integration.WilsonThermometerLiteralCredit

/-! A genuine compact three-site Wilson measurement after subtracting a table fixed
at each relative displacement. This equality retains all seven proper and full
original moments and the same independently chosen inverse for each placement. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerRegisteredTripleMass
open Finset MeasureTheory Table Spec Lattice Wilson RG Source Marker Extraction Climb Trace.Pilot
open Next.UVStress Next.Rank RG12 RG17 PhysMS PhysicalNext.Repeat.Legato MergeProof MergeProof.Accent MergeProof.East
open FVA1 OriginalForcedAddresses XSpace XSpace.Normalize XSpace.Rose Cells Push.GridApprox OPE.Therm
open WilsonPositionThermometerGradedReading WilsonPositionThermometerGradedSource WilsonPositionThermometerCapStation
open WilsonThermometerCenteredAlgebra WilsonThermometerAlignedCells
open scoped Classical BigOperators Topology
variable {G:Gauge} (R:Run G) (A:Group R.family 6) {i per:ℕ}
local notation "J" => Stock.census (Fin 3)
local notation "T" => Site (R.family.side (i+2) per)
local notation "cut" => (Nat.le_succ i).trans (Nat.le_succ (i+1))
local notation "z₀" => ((i+2,per):UVIndex)
local notation "χ" r:max => WilsonSeparatedOriginalThermometerCells.positions (R:=R) r (z₀)
local notation "posted" y:max => WilsonThermometerRegisteredCells.placement (R:=R) (z₀) y
local notation "ν" => OPE.Therm.scene R.family.path (i+2) per i

def sites (x:Fin 3 → T):Positions (Fin 3) (R.family.side (i+2) per) where
  origin:=x
  stub v:={x v}
  mem _:=mem_singleton_self _

local notation "observable" x:max s:max => WilsonThermometerCourseHot.bare R A (sites R x) s
local notation "returned" y:max s:max => actualTransport R.family (N:=i+2) (observable (atOrigin y) s) (cut)
local notation "row₁" x:max s:max => R.family.omega (i+2) per (observable x s)

theorem invariant (refs:∀v:Fin 3,R.family.ref (grade v).val ≤ i+2) (s:(J).Mode) (y:T×T) (c:T) :
    row₁ (placedAt y c) s = row₁ (atOrigin y) s:=by
  let e:=s.val.equivFin.symm
  let fields (v:Fin s.val.card):R.family.book.Token:=⟨(grade (e v).val).val,
    A.station.wheel.atCut (z₀) (index A (grade (e v).val)) (vector A univ (e v).val)⟩
  have same (x:Fin 3→T):R.family.numeric (i+2) per fields (fun v=>x (e v).val)=row₁ x s:=by
    apply congrArg (R.family.omega (i+2) per);funext U
    let d(v:Fin 3):ℂ:=R.family.O (i+2) per (A.station.wheel.atCut (z₀) (index A (grade v))
      (vector A univ v)) (x v) U
    change (∏v:Fin s.val.card,d (e v).val)=∏ v∈s.val,d v
    exact (e.prod_comp (fun v=> d v.val)).trans (Finset.prod_attach s.val d)
  rw [←same,←same]
  exact R.family.anchored R.makes fields (fun v=>refs (e v).val) c (fun v=>atOrigin y (e v).val)

def sensor (table:T×T→Poly J) (r:ℝ) (test:Test 3):ℂ:=
  test.applyTo (fun x=>∑s:(J).Mode,weight (table (offsets ((χ r) x))) s*(row₁ ((χ r) x) s))

open private sum_triples from YM.Integration.WilsonThermometerAlignedCells

theorem grouped (refs:∀v:Fin 3,R.family.ref (grade v).val ≤ i+2) (table:T×T→Poly J) (r:ℝ) (test:Test 3):
  sensor R A table r test = ∑y:T×T,mass (R:=R) r (z₀) test y*(∑s:(J).Mode,weight (table y) s*(row₁ (atOrigin y) s)) :=by
  let read (x:Fin 3→T):ℂ:=∑s:(J).Mode,weight (table (offsets x)) s*(row₁ x s)
  have moved (y:T×T)(c:T):read (placedAt y c)=∑s:(J).Mode,weight (table y) s*(row₁ (atOrigin y) s):=by
    unfold read
    have off:offsets (placedAt y c)=y:=by cases y;simp [placedAt,offsets,atOrigin]
    rw [off];apply sum_congr rfl;intro s _;rw [invariant R A refs s y c]
  change test.applyTo (fun x=>read ((χ r) x))=_
  rw [WilsonSeparatedOriginalThermometerCells.tested test (χ r) (WilsonSeparatedOriginalThermometerCells.placed (R:=R) r (z₀)) read]
  rw [sum_triples];apply sum_congr rfl;intro y _
  rw [WilsonThermometerAlignedCells.mass,sum_mul];apply sum_congr rfl;intro c _;rw [moved]

theorem rent (y:T×T) (s:(J).Mode): Integrable (returned y s) (ν):=by
  have con:=WilsonThermometerLiteralCredit.continuous_face R A (sites R (atOrigin y)) s
  have weighted:Integrable (fun U=>(R.family.path.rep (i+2) per (i+2)).eval U • (observable (atOrigin y) s) U) (prior G _):=by
    simpa only [Complex.real_smul] using (RG05Readout.Harvest.dye_grow («C»:=R.family) (N:=i+2) (p:=per) R.makes con)
  exact actualScene_integrable_of_weighted R.family R.makes (cut)
    (actualTransport_weighted_integrable_of_integrable R.family R.makes (le_refl (i+2)) weighted (cut))

theorem proper (y:T×T) (d:Poly J) :
    Integrable (WilsonThermometerRegisteredPlantedFaces.physical R A (posted y) d) (ν):=by
  change Integrable (fun U =>∑s:(J).Mode,weight d s*(returned y s) U) _
  exact integrable_finsetSum _ (fun s _=>(rent R A y s).const_mul _)

theorem original (refs:∀v:Fin 3,R.family.ref (grade v).val ≤ i+2) (table:T×T→Poly J) (r:ℝ) (test:Test 3):
  sensor R A table r test = ∫U,∑y:T×T,mass (R:=R) r (z₀) test y*
    WilsonThermometerRegisteredPlantedFaces.physical R A (posted y) (table y) U ∂ν:=by
  have lawEq:OPE.Therm.scene R.family.path (i+2) per (i+2)=law G (R.family.side (i+2) per) (R.family.beta (i+2) per):=by
    have actual:R.family.Makes:=R.makes
    unfold OPE.Therm.scene law dose Wilson.weight
    rw [(actual.wilson.starts (i+2) per).2]
  rw [grouped R A refs,integral_finsetSum _ (fun y _=>(proper R A y (table y)).const_mul _)]
  apply sum_congr rfl;intro y _
  rw [integral_const_mul];congr 1
  change _ = ∫U,∑s:(J).Mode,weight (table y) s *(returned y s) U ∂ν
  rw [integral_finsetSum _ (fun s _=>(rent R A y s).const_mul _)]
  apply sum_congr rfl;intro s _
  have con:=WilsonThermometerLiteralCredit.continuous_face R A (sites R (atOrigin y)) s
  have weighted:Integrable (fun U=>(R.family.path.rep (i+2) per (i+2)).eval U • (observable (atOrigin y) s) U) (prior G _):=by
    simpa only [Complex.real_smul] using (RG05Readout.Harvest.dye_grow («C»:=R.family) (N:=i+2) (p:=per) R.makes con)
  rw [integral_const_mul,actualScene_transport R.family R.makes (le_refl (i+2)) weighted (cut),lawEq]
  rfl

end YM.Integration.WilsonThermometerRegisteredTripleMass
