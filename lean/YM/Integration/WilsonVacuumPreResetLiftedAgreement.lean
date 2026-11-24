import YM.Integration.WilsonVacuumPreResetLiftedSeries
import YM.Further.CORRECTED_LIFT_COEFFICIENTS.PathCost

/-! Direct matching of the retained original covering atoms across actual tori.
The quadratic atom includes its true plaquette-clover subtraction. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetLiftedAgreement
open Function Finset Set Lattice RG Wilson Comparison.Density Comparison.Density.Render
open StressFlux AnalyticBridge VerifiedReset Collection Further.CorrectedLift
open scoped Classical BigOperators
variable {G:Gauge}{n m:Side}

theorem reaches (q:ℕ)(a:Slot)(width:a.length≤q): (a.stencil:Set Cover)⊆Lattice.box q:=by
  have center:(0:Cover)∈Lattice.box 0:=by simp [box_test]
  have run:=PathCost.passages 0 a.walk center
  have stop':a.offset∈Lattice.box a.walk.length:=by simpa [Slot.offset] using PathCost.limit 0 a.walk center
  intro z hz
  rcases Finset.mem_union.mp hz with hw|hw
  · apply PathCost.borrow (0+a.walk.length) q _
    · exact run z (List.mem_toFinset.mp hw)
    · dsimp [Slot.length] at width
      omega
  · apply PathCost.borrow (a.walk.length+(square a.plaq.val.1 a.plaq.val.2).length) q _
    · exact PathCost.passages _ _ stop' z (List.mem_toFinset.mp hw)
    · simpa [square,Slot.length] using width

theorem unmasked {k:ℕ}(a:Atom G k)(q:ℕ)(width:a.length≤q)
    (x:Site n)(y:Site m)(U:Config G n)(V:Config G m)
    (agree:Agrees (Lattice.box q) (expandAt x U) (expandAt y V)):
    a.unmasked U x=a.unmasked V y:=by
  apply congrArg a.poly
  funext i
  apply (a.leg i).covered
  have leg:(a.leg i).length≤q:=(Finset.single_le_sum (f:=fun t=>(a.leg t).length)
    (fun t _=>Nat.zero_le _) (Finset.mem_univ i)).trans width
  intro e he hf
  exact agree e (reaches q (a.leg i) leg he) (reaches q (a.leg i) leg hf)

private theorem travelled (w:Walk)(q:ℕ)(width:w.length≤q)
    (x:Site n)(y:Site m)(U:Config G n)(V:Config G m)
    (agree:Agrees (Lattice.box q) (expandAt x U) (expandAt y V)):
    travel U x w=travel V y w:=by
  have center:(0:Cover)∈Lattice.box 0:=by simp [box_test]
  have source (z:Cover)(hz:z∈visits 0 w):z∈Lattice.box q:=by
    apply PathCost.borrow (0+w.length) q (by simpa using width)
    exact PathCost.passages 0 w center z hz
  have same:travel (expandAt x U) (0:Cover) w=travel (expandAt y V) (0:Cover) w:=by
    apply travel_local
    intro e he hf
    exact agree e (source _ he) (source _ hf)
  simpa only [travel_at,map_zero,zero_add] using same

theorem clover (q:ℕ)(width:4≤q)(x:Site n)(y:Site m)(U:Config G n)(V:Config G m)
    (agree:Agrees (Lattice.box q) (expandAt x U) (expandAt y V)):
    petals U x=petals V y:=by
  have loop (a b:Lattice.Step):travel U x (Lattice.oriented a b)=travel V y (Lattice.oriented a b):=
    travelled (Lattice.oriented a b) q (by simpa [Lattice.oriented] using width) x y U V agree
  have plates (a b:Lattice.Step):plate U x a b=plate V y a b:=congrArg G.curvature (loop a b)
  funext b
  simp only [petals,StressFlux.clover,stencil,plates]

theorem corrected (a:Atom G 2)(q:ℕ)(width:a.length≤q)(room:4≤q)
    (x:Site n)(y:Site m)(U:Config G n)(V:Config G m)
    (agree:Agrees (Lattice.box q) (expandAt x U) (expandAt y V)):
    baseLine x a U-pollen x a U=baseLine y a V-pollen y a V:=by
  unfold baseLine pollen
  rw [unmasked a q width x y U V agree,clover q room x y U V agree]

end YM.Integration.WilsonVacuumPreResetLiftedAgreement
