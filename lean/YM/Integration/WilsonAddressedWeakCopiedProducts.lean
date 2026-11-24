import YM.Integration.WilsonAddressedWeakTilingCourse
import YM.Integration.WilsonAddressedWeakPackedCertificate
import YM.Push.CORRECTED_COLUMNS.Infuse

/-! Complete cutoff coefficients of the independently displaced physical fields on the authentic reflection array. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonAddressedWeakCopiedProducts
open Function Set Filter MeasureTheory Lattice Wilson RG Source RG12 Extra.Histories
open RG05Readout Native Address Many Records Harvest Push.GridApprox Cells Extraction
open PhysicalNext.Repeat.Legato MergeProof Accent Motion Bandage Extra.Multi Menu
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetResidue Marker Push.Corrected Marks
open scoped Classical BigOperators

private theorem components {J:Type*} [Fintype J] [DecidableEq J] (A:Finset (J × Fin 2)) (v:J × Fin 2 → ℂ) :
    ∏ j,∏ i∈Marks.fibre A j,v (j,i) = ∏ b∈A,v b := by
  calc
    _ = ∏ j,∏ b∈A with b.1=j,v b := by
      refine Finset.prod_congr rfl fun j _ => Finset.prod_bij (fun i _=>(j,i)) ?_ ?_ ?_ (fun _ _=>rfl)
      · intro i hi; exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hi).2,rfl⟩
      · intro i _ l _ h; exact congrArg Prod.snd h
      · rintro ⟨m,i⟩ hi
        have h : m=j := (Finset.mem_filter.mp hi).2
        subst j
        exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hi).1⟩,rfl⟩
    _ = _ := Finset.prod_fiberwise_of_maps_to (fun _ _=>Finset.mem_univ _) v

variable {G:Gauge} (R:Run G) {χ k N p:ℕ} (gr:χ≤k) (live:k≤N)
variable (d:Fin 2→ℕ) (z:Fin 2→Site (R.family.side N p))
  (y:(i:Fin 2)→Palette R.family (d i)) (r:(i:Fin 2)→Emblems R.family (d i))
local notation "T" => Cells.center R.family.S p (gr.trans live) 0
local notation "J" => Site (R.family.side χ p)
local notation "F" => WilsonThermometerIntrinsicRoster.source R d z y r live
def field (b:J × Fin 2) :=  WilsonThermometerReflectedRoster.source R (fun b:J × Fin 2=>d b.2)
  (fun b=>z b.2) (fun b=>((T).omega b.1,decide ((T).hand b.1))) (fun b=>(R.family.S.toDepth gr p).embed b.1)
  (fun b:J × Fin 2=>y b.2) (fun b=>r b.2) live b
local notation "C" => field R gr live d z y r

theorem ordinary (A:Finset (J × Fin 2)) (U:Config G (R.family.side N p)) :
    Marks.part (replicate T (fun W=>Marks.ordinary (fun i=>F i W)) U) A = ∏ b∈A,C b U := by
  have eqcopy (j:J) (i:Fin 2) (W:Config G (R.family.side N p)) : (T).copy j (F i) W=C (j,i) W :=
    WilsonAddressedWeakTilingCourse.copied R gr live d z y r j i W
  rw [divides]
  calc
    _ = ∏ j,∏ i∈Marks.fibre A j,C (j,i) U := by
      refine Finset.prod_congr rfl fun j _ => ?_
      simp_rw [selects,← eqcopy j]
      by_cases h:(T).hand j <;> simp [Tiling.copy,h] <;> rfl
    _ = _ := components A (fun b=>C b U)

/-- All modes share the original unmarked density, including the empty subset. -/
theorem original (A:(Stock.census (J × Fin 2)).Mode) (U:Config G (R.family.side N p)) :
    (Accent.birth (Stock.census (J × Fin 2)) (R.family.path.rep N p N) C U).part A =
    (bare (R.family.beta N p) U:ℂ)*
      Marks.part (replicate T (fun W=>Marks.ordinary (fun i=>F i W)) U) A.val := by
  rw [ordinary R gr live d z y r A.val U]
  simp only [Accent.birth,Poly.part_smul,Mach,Extra.Trajectories.pass_fire]
  have h : (R.family.path.rep N p N).eval=bare (R.family.beta N p) := (R.makes.wilson.starts N p).2
  rw [h]

end YM.Integration.WilsonAddressedWeakCopiedProducts
