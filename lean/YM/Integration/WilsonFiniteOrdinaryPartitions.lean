import YM.Integration.WilsonIndependentOrdinaryPairGrade
import YM.Comparison.RG02.Cumulants.Partition

/-! The normalized finite ordinary moment in each mask, with all proper connected faces. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonFiniteOrdinaryPartitions
open Finset Marker Multi Extra.Trajectories Comparison.RG02 Comparison.RG02.Order Comparison.RG02.Cumulants
open WilsonIndependentOrdinaryPairGrade
open scoped Classical BigOperators
variable {V : Type} [DecidableEq V] [Fintype V] {R : Census V} {r : ℕ}

/-- The polynomial before truncating the joint coupling degree. Only disjoint blocks that
cover the particular mask enter this polynomial. -/
def ordinary (W : Grade R r) (s : R.Mode) : Polynomial ℂ :=
  ∑ q ∈ shards R s, ∏ t ∈ q.val, slot t.val (render (logMarked W))

private def expansion (b : ℕ) (C : Truncated R) : Truncated R :=
  ∑ j ∈ range (b+1), Polynomial.C (algebraMap ℂ (Poly R) (j.factorial:ℂ)⁻¹) * C^j

private theorem quiet (W : Grade R r) (unit : UnitLeading W) (z : ℂ) :
    (value z (logMarked W)).part R.quiet=0 := by
  have h : Poly.bead R ((value z (logMarked W)).part R.quiet)=0 := by
    rw [←value_denom,denominator,log_marked unit]
    exact (valueL R r z).map_zero
  simpa using congrArg (Poly.part · R.quiet) (show Poly.send R.quiet _=0 from h)

/-- The numerical, untruncated partition sum is the squarefree exponential of the
independently filed connected response at the same coupling. -/
theorem evaluated (W : Grade R r) (unit : UnitLeading W) (z : ℂ) (s : R.Mode) :
    (ordinary W s).eval z = (Poly.pass (value z (logMarked W))).part s := by
  rw [pass_partition _ (quiet W unit z),ordinary,Polynomial.eval_finsetSum]
  apply sum_congr rfl
  intro q _
  rw [Polynomial.eval_prod]
  exact prod_congr rfl (fun t _ => (read_slot t.val _ z).trans
    (congrArg (fun P : Poly R => P.part t.val) (value_render z (logMarked W)).symm))

private theorem enough (a : Poly R) (ha : a.part R.quiet=0) (k : ℕ) :
    (∑ i ∈ range (Fintype.card V+k+1),(i.factorial:ℂ)⁻¹ • a^i) = Poly.pass a := by
  symm
  unfold Poly.pass
  apply sum_subset (range_mono (by omega))
  intro i _ missed
  rw [Poly.stops a ha i (by rw [mem_range] at missed; omega),smul_zero]

/-- Pure-vacuum normalization is performed on the complete series before the marked
logarithm. This is exact at every retained coupling grade. -/
theorem normalized (W : Grade R r) (unit : UnitLeading W) (sym : Symmetric W) (z : ℂ) (s : R.Mode) :
    (value z (ratio W)).part s=partialValue r z (ordinary W s) := by
  let C := render (logMarked W)
  let E := expansion (Fintype.card V+r) C
  have restore : stamp R r C=logMarked W := rerender (sym_logMarked unit sym)
  have file : stamp R r E=ratio W := by
    have h := pass_connected (ratio_quiet unit)
    change Poly.pass (logMarked W)=ratio W at h
    rw [←h]
    simp only [E,expansion,Poly.pass,Fintype.card_sum,Fintype.card_fin,map_sum,stamp_scalar,map_pow,restore]
  have eval (y : ℂ) : formula y E=Poly.pass (value y (logMarked W)) := by
    simp only [E,expansion,map_sum,map_mul,map_pow,formula_const,C,←value_render]
    simpa only [Algebra.smul_def] using enough (value y (logMarked W)) (quiet W unit y) r
  have equal : slot s E=ordinary W s := by
    apply Polynomial.funext
    intro y
    rw [read_slot,eval,evaluated W unit]
  rw [← file, stamped,equal]

end YM.Integration.WilsonFiniteOrdinaryPartitions
