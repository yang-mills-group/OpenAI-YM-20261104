import YM.Integration.WilsonLongContactFrozenTest
import YM.Integration.WilsonLongContactForest
import YM.QCDVacuum.Stall.Town

/-! A single original physical marked address with its entire signed fine field
and a genuine Townsend housing at every held coarse field. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonLongContactTown
open Function Lattice Wilson Pressure RG Tree Precision MeasureTheory Marker
open PhysicalNext.Repeat PhysicalNext.Repeat.Lotus
open Next.Fluctuations Next.Fluctuations.Sector
open scoped Classical BigOperators
variable {G : Gauge} {c f : Side} {S : StepData c f} {Q : Rep G f}

def address (M : Leaf Q) : Fin 1 ↪ Wing :=
  ⟨fun _=>M.turn,fun _ _ _=>Subsingleton.elim _ _⟩

def town (T : Tube G S) (M : Leaf Q) : Township (address M) Q T where
  chorus _ := ⟨fun _=>WilsonLongContactForest.blade S M,fun _=>rfl⟩
  there _ := M.borel.comp measurable_snd
  fixes _ _ _ := fun _ _ _=>rfl

theorem frozen (T : Tube G S) (M : Leaf Q) (V : Config G c) :
    (∏ j∈({0}:Finset (Fin 1)),(((town T M).tune V).has j).ingredient)=M.ingredient := by
  rw [Finset.prod_singleton]
  rfl

theorem registered (T : Tube G S) (N : Leaf Q) (j : ℕ) (hr : N.turn=.logKey j) :
    ((address N) 0).support Q=(Q.activities.reg j).support ∧
    (∀ (V : Config G c) (U : Config G f),
       Q.eval U*((((town T N).tune V).has 0).ingredient U)=N.cicada U) := by
  refine ⟨?_,?_⟩
  · change N.turn.support Q=_
    rw [hr];rfl
  · intro V U
    change Q.eval U*N.ingredient U=_
    rw [WilsonLongContactAddress.density N j hr U,mul_comm]

theorem guards (T : Tube G S) (M : Leaf Q) (V : Config G c)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {I : Type*}
    (U : I → Config G f) (p : E) (k : ℕ) :
    ∀ i, ConnectedActivityE6.Blaze.Brush k M.weight 1
      (fun _ : E=> (∏ j∈({0}:Finset (Fin 1)),(((town T M).tune V).has j).ingredient) (U i)) p := by
  rw [frozen]
  exact fun i=>WilsonLongContactFrozenTest.current M k p (U i)

end YM.Integration.WilsonLongContactTown
