import YM.Integration.WilsonIndependentConditionedLocatedMesh
import YM.Integration.WilsonIndependentConditionedFolioStations

/-! Passing to the wrapped physical register only groups the actual signed
coefficients of the two separately addressed finite Mer sums. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedLocatedFold
open Function Set MeasureTheory Lattice
open WilsonIndependentConditionedFolioStations (ports)
open scoped BigOperators Classical Topology

def film (L R:Finset Cover):Finset (Fin 2 → Cover):=(L ×ˢ R).image (fun t=>ports t.1 t.2)

theorem two (L R:Finset Cover)(w:(Fin 2→ Cover)→ℝ):∑o∈film L R,w o=∑x∈L,∑y∈R,w (ports x y):=by
  rw [film,Finset.sum_image]
  · exact Finset.sum_product _ _ _
  · intro p _ q _ h
    exact Prod.ext (congrFun h 0) (congrFun h 1)

def folded {X Y:Type*}[DecidableEq Y](F:Finset X)(π:X→Y)(w:X→ℂ)(y:Y):ℂ:=
  ∑x∈F,if π x=y then w x else 0

theorem variation {X Y:Type*}[DecidableEq Y][Fintype Y](F:Finset X)(π:X→Y)(w:X→ℂ):
    ∑y,‖folded F π w y‖ ≤ ∑x∈F,‖w x‖:=by
  calc
    _ ≤ ∑y,∑x∈F,‖if π x=y then w x else 0‖:=by
      apply Finset.sum_le_sum
      intro y _
      exact norm_sum_le .. 
    _ = _:=by rw [Finset.sum_comm];simp [apply_ite]

theorem paid {Y:Type*}[DecidableEq Y][Fintype Y](L R:Finset Cover)(π:(Fin 2→ Cover)→Y)
    (w:(Fin 2→ Cover)→ℂ):∑y,‖folded (film L R) π w y‖ ≤ ∑u∈L,∑v∈R,‖w (ports u v)‖:=
  (variation ..).trans_eq (two ..)
end YM.Integration.WilsonIndependentConditionedLocatedFold
end
