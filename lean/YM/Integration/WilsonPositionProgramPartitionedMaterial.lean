import YM.Integration.WilsonPositionProgramWholeDeposit

/-! The entire ordinary face of an independently deposited finite material can be
filed as a single source on its own older action. The finite power compensates
the poles of each set partition. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPositionProgramPartitionedMaterial
open Function Filter Finset MeasureTheory RG Precision Lattice Wilson Exterior Tree
open Next.SectorChange PertExtension.Series Multi Marker Comparison.RG02
open Comparison.RG02.Cumulants Comparison.RG02.Laplace
open scoped Topology BigOperators Classical ContDiff

variable {G : Gauge} {f : Side} {V : Type} [Fintype V] [DecidableEq V]
    {R : Census V} (W : Bulk.Colors R G f) (s : R.Mode)

def degrees (t : (parts R).Mode) := ∑ i∈t.val, W.power i
def pole := (shards R s).sup (degrees W)
def material (g : ℝ) (U : Config G f) : ℂ :=
  ∑ t∈shards R s, g^(pole W s-degrees W t) • ∏ i∈t.val, W.mark i g U

/-- Single recorded group source on exactly the original quiet action. -/
def grouped (C : Census Unit) : Bulk.Colors C G f :=
  ⟨W.vac,fun _ => material W s,fun _ => pole W s⟩

omit [Fintype V] in
private lemma product_grade (hw : Bulk.Well W) (t : Finset (Hot R)) :
    Assembly.GradeAt (∑ i∈t,W.power i)
      (fun x : ℝ × fieldDir G f 1 => ∏ i∈t, Bulk.projected (W.mark i) x) := by
  induction t using Finset.induction with
  | empty => simp only [Finset.sum_empty,Finset.prod_empty]; exact Assembly.GradeAt.unchecked contDiffAt_const
  | insert i t hi ih =>
    simp only [Finset.sum_insert hi,Finset.prod_insert hi]
    exact (hw.suppose_mark i).mul ih

omit [Fintype V] in
theorem admitted (C : Census Unit) (hw : Bulk.Well W) : Bulk.Well (grouped W s C) := by
  refine ⟨hw.suppose_vac,?_,hw.natural,?_,hw.envelope,?_⟩
  · intro i
    apply Assembly.GradeAt.list_sum
    intro t ht
    have hp : degrees W t ≤ pole W s := Finset.le_sup (f:=degrees W) ht
    change Assembly.GradeAt (pole W s) _
    have q :=
      Assembly.GradeAt.scale (Assembly.GradeAt.shifts (Prod.fst : ℝ × fieldDir G f 1 → ℝ)
        contDiffAt_fst rfl (pole W s-degrees W t)) (product_grade W hw t.val)
    change Assembly.GradeAt ((pole W s-degrees W t)+degrees W t) _ at q
    simpa only [Nat.sub_add_cancel hp,Bulk.projected] using q
  · intro _ g b U
    apply Finset.sum_congr rfl
    intro t _
    congr 1
    exact Finset.prod_congr rfl (fun i _ => hw.gauges i g b U)
  · intro _ g
    apply Envelope.sumC
    intro t _
    simp only [Complex.real_smul]
    exact (Envelope.constC _).mulC (Envelope.prodC _ _ (fun i _ => hw.prices i g))

theorem rolled (g : ℝ) (hg : g ≠ 0) (U : Config G f) :
    (g^(pole W s))⁻¹ • material W s g U =
      (Poly.pass (Integral.markedLog g U W)).part s := by
  rw [Cumulants.pass_partition (Integral.markedLog g U W) (Multi.part_lit_quiet _) s,material, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  have hp : degrees W t ≤ pole W s := Finset.le_sup (f:=degrees W) ht
  simp_rw [Integral.markedLog, Multi.part_lit,Complex.real_smul]
  rw [Finset.prod_mul_distrib]
  push_cast
  rw [Finset.prod_inv_distrib, Finset.prod_pow_eq_pow_sum,← mul_assoc]
  congr 1
  change ((g:ℂ)^pole W s)⁻¹*(g:ℂ)^(pole W s-degrees W t) = ((g:ℂ)^degrees W t)⁻¹
  rw [show (g:ℂ)^pole W s=(g:ℂ)^(pole W s-degrees W t)*(g:ℂ)^degrees W t by
    rw [← pow_add,Nat.sub_add_cancel hp]]
  have hn : (g:ℂ) ≠ 0 := by exact_mod_cast hg
  field_simp

end YM.Integration.WilsonPositionProgramPartitionedMaterial
