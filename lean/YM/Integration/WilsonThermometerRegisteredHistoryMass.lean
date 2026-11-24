import YM.Integration.WilsonThermometerRegisteredTripleMass

/-! At any admitted moving cutoff and every older original report, the literal
integrated three-point scalar is the integral of the same normalized incoming
seven faces with relative placements and the identical compensated table. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerRegisteredHistoryMass
open Finset MeasureTheory Table Spec Lattice Wilson RG Source Marker Extraction Climb Trace.Pilot
open Next.UVStress Next.Rank RG12 RG17 PhysMS PhysicalNext.Repeat.Legato MergeProof MergeProof.Accent MergeProof.East
open FVA1 OriginalForcedAddresses XSpace XSpace.Normalize XSpace.Rose Cells Push.GridApprox OPE.Therm
open WilsonPositionThermometerGradedReading WilsonPositionThermometerGradedSource WilsonPositionThermometerCapStation
open WilsonThermometerCenteredAlgebra WilsonThermometerAlignedCells
open scoped Classical BigOperators Topology
variable {G:Gauge} (R:Run G) (A:Group R.family 6) {N i per:ℕ} (live:i≤N)
local notation "J" => Stock.census (Fin 3)
local notation "T" => Site (R.family.side N per)
local notation "z₀" => ((N,per):UVIndex)
local notation "χ" r:max => WilsonSeparatedOriginalThermometerCells.positions (R:=R) r (z₀)
local notation "posted" y:max => WilsonThermometerRegisteredCells.placement (R:=R) (z₀) y
local notation "ν" j:max => OPE.Therm.scene R.family.path N per j

def sites (x:Fin 3 → T):Positions (Fin 3) (R.family.side N per) where
  origin:=x
  stub v:={x v}
  mem _:=mem_singleton_self _

local notation "observable" x:max s:max => WilsonThermometerCourseHot.bare R A (sites R x) s
local notation "returned" y:max s:max => actualTransport R.family (N:=N) (observable (atOrigin y) s) live
local notation "row₁" x:max s:max => R.family.omega N per (observable x s)

def physical (o:Positions (Fin 3) (R.family.side N per)) (Q₀:Poly J) (U:Config G (R.family.side i per)):ℂ:=
  ∑s:(J).Mode,weight Q₀ s*actualTransport R.family (N:=N) (WilsonThermometerCourseHot.bare R A o s) live U

def normalized (simple:G.Simple) (o:Positions (Fin 3) (R.family.side N per)) (Q₀:Poly J)
    (U:Config G (R.family.side i per)):ℂ :=
  ((R.family.path.rep N per i).eval U:ℂ)⁻¹*
    (total (WilsonThermometerCourseIntake.incoming R A simple live o U) Q₀).part full

theorem planted (simple:G.Simple) (o:Positions (Fin 3) (R.family.side N per)) (d:Poly J)
    (refs:∀v:Fin 3,R.family.ref (grade v).val ≤ N):
    physical R A live o d=normalized R A live simple o d:=by
  funext U
  rw [physical,normalized,affine,mul_sum]
  apply sum_congr rfl
  intro s _
  have same:=WilsonThermometerCourseResidual.observed R A simple live o refs U s
  change ((R.family.path.rep N per i).eval U:ℂ)⁻¹*(WilsonThermometerCourseIntake.incoming R A simple live o U).part s
    = actualTransport R.family (N:=N) (WilsonThermometerCourseHot.bare R A o s) live U at same
  rw [←same]
  ring

theorem invariant (refs:∀v:Fin 3,R.family.ref (grade v).val ≤ N) (s:(J).Mode) (y:T×T) (c:T) :
    row₁ (placedAt y c) s = row₁ (atOrigin y) s:=by
  let e:=s.val.equivFin.symm
  let fields (v:Fin s.val.card):R.family.book.Token:=⟨(grade (e v).val).val,
    A.station.wheel.atCut (z₀) (index A (grade (e v).val)) (vector A univ (e v).val)⟩
  have same (x:Fin 3→T):R.family.numeric N per fields (fun v=>x (e v).val)=row₁ x s:=by
    apply congrArg (R.family.omega N per);funext U
    let d(v:Fin 3):ℂ:=R.family.O N per (A.station.wheel.atCut (z₀) (index A (grade v))
      (vector A univ v)) (x v) U
    change (∏v:Fin s.val.card,d (e v).val)=∏ v∈s.val,d v
    exact (e.prod_comp (fun v=> d v.val)).trans (Finset.prod_attach s.val d)
  rw [←same,←same]
  exact R.family.anchored R.makes fields (fun v=>refs (e v).val) c (fun v=>atOrigin y (e v).val)

def sensor (table:T×T→Poly J) (r:ℝ) (test:Test 3):ℂ:=
  test.applyTo (fun x=>∑s:(J).Mode,weight (table (offsets ((χ r) x))) s*(row₁ ((χ r) x) s))

open private sum_triples from YM.Integration.WilsonThermometerAlignedCells

theorem grouped (refs:∀v:Fin 3,R.family.ref (grade v).val ≤ N) (table:T×T→Poly J) (r:ℝ) (test:Test 3):
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

theorem rent (y:T×T) (s:(J).Mode): Integrable (returned y s) (ν i):=by
  have con:=WilsonThermometerLiteralCredit.continuous_face R A (sites R (atOrigin y)) s
  have weighted:Integrable (fun U=>(R.family.path.rep N per N).eval U • (observable (atOrigin y) s) U) (prior G _):=by
    simpa only [Complex.real_smul] using (RG05Readout.Harvest.dye_grow («C»:=R.family) (N:=N) (p:=per) R.makes con)
  exact actualScene_integrable_of_weighted R.family R.makes live
    (actualTransport_weighted_integrable_of_integrable R.family R.makes (le_refl N) weighted live)

theorem proper (y:T×T) (d:Poly J) :
    Integrable (physical R A live (posted y) d) (ν i):=by
  change Integrable (fun U =>∑s:(J).Mode,weight d s*(returned y s) U) _
  exact integrable_finsetSum _ (fun s _=>(rent R A live y s).const_mul _)

theorem measured (refs:∀v:Fin 3,R.family.ref (grade v).val ≤ N) (table:T×T→Poly J) (r:ℝ) (test:Test 3):
  sensor R A table r test = ∫U,∑y:T×T,mass (R:=R) r (z₀) test y*
    physical R A live (posted y) (table y) U ∂ν i:=by
  have lawEq:OPE.Therm.scene R.family.path N per N=law G (R.family.side N per) (R.family.beta N per):=by
    have actual:R.family.Makes:=R.makes
    unfold OPE.Therm.scene law dose Wilson.weight
    rw [(actual.wilson.starts N per).2]
  rw [grouped R A refs,integral_finsetSum _ (fun y _=>(proper R A live y (table y)).const_mul _)]
  apply sum_congr rfl;intro y _
  rw [integral_const_mul];congr 1
  change _ = ∫U,∑s:(J).Mode,weight (table y) s *(returned y s) U ∂ν i
  rw [integral_finsetSum _ (fun s _=>(rent R A live y s).const_mul _)]
  apply sum_congr rfl;intro s _
  have con:=WilsonThermometerLiteralCredit.continuous_face R A (sites R (atOrigin y)) s
  have weighted:Integrable (fun U=>(R.family.path.rep N per N).eval U • (observable (atOrigin y) s) U) (prior G _):=by
    simpa only [Complex.real_smul] using (RG05Readout.Harvest.dye_grow («C»:=R.family) (N:=N) (p:=per) R.makes con)
  rw [integral_const_mul,actualScene_transport R.family R.makes (le_refl N) weighted live,lawEq]
  rfl

theorem original (simple:G.Simple) (refs:∀v:Fin 3,R.family.ref (grade v).val ≤ N)
    (table:T×T→Poly J) (r:ℝ) (test:Test 3):
    sensor R A table r test = ∫U,∑y:T×T,mass (R:=R) r (z₀) test y*
      normalized R A live simple (posted y) (table y) U ∂ν i:=by
  simpa only [←planted R A live simple _ _ refs] using measured R A live refs table r test

end YM.Integration.WilsonThermometerRegisteredHistoryMass
