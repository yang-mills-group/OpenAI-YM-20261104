import YM.Integration.WilsonThermometerAlignedCells
import YM.Integration.WilsonPositionSeparatedProfileFiniteMean
import YM.FVA1.Film

/-! The actual pair detector on the older Wilson law, with the true microscopic cell mass. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerRegisteredCells

open Function Filter Set Finset MeasureTheory Lattice Wilson RG Source Extraction Table Spec
open OPE OPE.Orbits OPE.Therm Climb Trace.Pilot RG12 RG17 PhysicalNext.Repeat.Legato
open XSpace XSpace.Rose Cells Push.GridApprox FVA1 WilsonThermometerAlignedCells
open WilsonPositionThermometerCapStation WilsonPositionThermometerGradedSource
open WilsonPositionThermometerGradedReading
open scoped Topology Classical BigOperators

variable {G:Gauge} {R:Run G} (A:Group R.family 6) (z:UVIndex)
local notation "C" => R.family
local notation "T" => Site (R.family.side z.1 z.2)

def raw (a b:Fin 3) (x:Fin 3→T) := fun U =>
  (C).O z.1 z.2 (A.station.wheel.atCut z (index A (grade a)) (vector A univ a)) (x a) U *
  (C).O z.1 z.2 (A.station.wheel.atCut z (index A (grade b)) (vector A univ b)) (x b) U

def reduced {j:ℕ} (live:j ≤ z.1) (r:ℝ) (φ:Test 3) (a b:Fin 3)
    (U:Config G (R.family.side j z.2)) : ℂ :=
  ∑ y:T×T, mass (R:=R) r z φ y *
    actualTransport (C) (N:=z.1) (raw A z a b (atOrigin y)) live U

private theorem shifted (a b:Fin 3) (ready:∀ v:Fin 3,(C).ref (grade v).val ≤ z.1) (y:T×T) (c:T) :
    (C).omega z.1 z.2 (raw A z a b (placedAt y c))=(C).omega z.1 z.2 (raw A z a b (atOrigin y)) := by
  let use:Fin 2→Fin 3:=![a,b]
  let field (j:Fin 2):(C).book.Token:=
    ⟨(grade (use j)).val,A.station.wheel.atCut z (index A (grade (use j))) (vector A univ (use j))⟩
  have same (x:Fin 3→T) : (C).numeric z.1 z.2 field (fun j=>x (use j))=(C).omega z.1 z.2 (raw A z a b x) := by
    apply congrArg ((C).omega z.1 z.2)
    funext U
    simp [field,use,Fin.prod_univ_two,raw]
    rfl
  rw [←same,←same]
  exact (C).anchored R.makes field (fun j=>ready (use j)) c (fun j=>atOrigin y (use j))

/-- The laboratory integral of the two literal fields equals the compact pair against the true
older vacuum. The translation is made on the integrated fine law before disintegrating at j. -/
theorem original (a b:Fin 3) (ready:∀ v:Fin 3,(C).ref (grade v).val ≤ z.1)
    {j:ℕ} (live:j ≤ z.1) (r:ℝ) (φ:Test 3) :
    φ.applyTo (fun x=>(C).omega z.1 z.2
      (raw A z a b (WilsonSeparatedOriginalThermometerCells.positions (R:=R) r z x))) =
      ∫ U,reduced A z live r φ a b U ∂scene (C).path z.1 z.2 j := by
  let cut (y:T×T):=raw A z a b (atOrigin y)
  let obs (x:Fin 3→T):=(C).omega z.1 z.2 (raw A z a b x)
  have grouped:=weighted_read (I:=Unit) A r z ready φ (fun _=>obs) (fun _ _=>1)
  simp only [Fintype.sum_unique,mul_one] at grouped
  rw [grouped]
  unfold reduced
  have weighted (y:T×T) : Integrable (fun U=>((C).path.rep z.1 z.2 z.1).eval U • cut y U) (prior G _) := by
    have continuous:Continuous (cut y):=((C).continuousO ..).mul ((C).continuousO ..)
    simpa only [Complex.real_smul] using
      (RG05Readout.Harvest.dye_grow («C»:=R.family) (N:=z.1) (p:=z.2) R.makes continuous)
  have lawEq : scene (C).path z.1 z.2 z.1=law G ((C).side z.1 z.2) ((C).beta z.1 z.2) := by
    have originalLaw : (C).Makes := R.makes
    unfold scene law dose Wilson.weight
    rw [(originalLaw.wilson.starts z.1 z.2).2]
  rw [integral_finsetSum]
  · apply sum_congr rfl
    intro y _
    rw [integral_const_mul,actualScene_transport (C) R.makes (le_refl z.1) (weighted y) live,lawEq]
    unfold YM.Integration.WilsonThermometerAlignedCells.weighted WilsonThermometerAlignedCells.mass
    rw [sum_mul]
    exact sum_congr rfl fun c _=>congrArg _ (shifted A z a b ready y c)
  · intro y _
    exact (actualScene_integrable_of_weighted (C) R.makes live
      (actualTransport_weighted_integrable_of_integrable (C) R.makes (le_refl z.1) (weighted y) live)).const_mul _

/-- Center positions are assigned their actual cell indices on both programs. The marked
material itself carries the full path footprints of the original stencils. -/
def placement (y:T×T) : Positions (Fin 3) ((C).side z.1 z.2) where
  origin:=atOrigin y
  stub v:={atOrigin y v}
  mem _:=mem_singleton_self _

end YM.Integration.WilsonThermometerRegisteredCells
