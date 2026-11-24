import YM.Integration.WilsonIndependentCollarDatedProbeSalary
import YM.Integration.WilsonIndependentCollarOrbitalReception

/-! Predeclare the shape of the actual finite front family while leaving its
common deck translation, the cofinal boards and all earlier deposits free. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentCollarOrbitShapes
open Function Finset Lattice RG Wilson Multi QuadraticLocal QuadraticLocal.Earn Next.Foundations
open WilsonCoeffUV.Mer WilsonCoeffUV.Wheel.Mark PhysicalNext.Repeat.Legato
open WilsonCoeffUV.Wheel WilsonCoeffUV.Embroider
open WilsonIndependentCollarOrbitalReception (relative)
open WilsonNeutralTwoPrintPathBoxHome (radius breadth)
open scoped Classical BigOperators

theorem sub (x y:Cover):radius (x-y) ≤ radius x+radius y:=by
  apply Finset.sup_le
  intro j _
  change (x j-y j).natAbs≤_
  calc
    _ ≤ (x j).natAbs+(-(y j)).natAbs:=by rw [sub_eq_add_neg];exact Int.natAbs_add_le ..
    _ ≤ _:=by
      rw [Int.natAbs_neg]
      exact Nat.add_le_add (le_sup (s:=univ) (f:=fun i:Axis=>(x i).natAbs) (mem_univ j))
        (le_sup (s:=univ) (f:=fun i:Axis=>(y i).natAbs) (mem_univ j))

theorem prepaid {I:Type}[DecidableEq I](points:Finset Cover)(J:Finset I)(o:J)(place:I→ Cover)
    (shift:Cover)(actual:∀i∈J,place i-shift∈points):
    breadth J o.val 0 (relative J o.val place)≤2*points.sup radius:=by
  apply max_le
  · simp [radius]
  · apply Finset.sup_le;intro i _
    have take (j:I)(h:j∈J):radius (place j-shift) ≤ points.sup radius:=
      le_sup (f:=radius) (actual j h)
    have eqn :relative J o.val place i = (place i.val-shift)-(place o.val-shift):=by
      dsimp [relative];abel
    rw [eqn]
    exact (sub _ _).trans (by rw [two_mul];exact Nat.add_le_add (take i.val (mem_of_mem_erase i.prop)) (take o.val o.prop))

theorem table {G:Gauge}{I:Type}[Fintype I][DecidableEq I]{n:ℕ}{side:Side}
    {R:Run G}{N i q:ℕ}{k:Fin n→ℕ}{σ:ℝ}{P:Passport side (Fin n)}{B:I→Binder P (Stock.census (Fin n))}
    (H:WilsonOriginalCensusDatedMaterial.Material R N i q k σ B)(y:Fin n→ Cover)(c:I→Fin n)
    (actual:H.root=y ∘ c)(J:Finset I)(o:J)(shift:Cover):
    breadth J o.val 0 (relative J o.val (fun z=>shift+H.root z)) ≤
      2*((Finset.univ:Finset (Fin n)).image y).sup radius:=by
  apply prepaid _ J o _ shift
  intro z _
  rw [add_sub_cancel_left,actual]
  exact mem_image_of_mem _ (mem_univ (c z))

end YM.Integration.WilsonIndependentCollarOrbitShapes
end
