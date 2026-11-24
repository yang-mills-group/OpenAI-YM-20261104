import YM.Integration.WilsonIndependentMovingRosterNormalizedCourse

/-! The own-home scale and complete lane of an actual seated occurrence on the
appointed normalized course, with its exact incoming dose. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentMovingRosterNormalizedSeats
open Filter Function Finset Lattice RG RG.Supply Wilson PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open XSpace XSpace.Rose XSpace.Cirrus Source Source.Drops Labels Precision Next.Foundations
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Bank.Mosaic
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Bank.PathCost
open WilsonCoeffUV.Embroider WilsonCoeffUV.Shard WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.AuxPlates
open WilsonIndependentMatchedNamedPair (sectionAt)
open WilsonIndependentFittedExteriorRung (Seated)
open WilsonIndependentMovingRosterLaneFilm (Licensed)
variable {G:Gauge}(R:Run G)(W:Initialize G){d h D k e u:ℕ}
    (survey target:Bool)(hd:d ≤ h)(p:h<D)(H:Hol G)(v:Rails h k u e)(E A K U:Credit)
local notation "T" => sectionAt R W target h

theorem original {L:Levels G}{F:Alma (R.family.labels.level d)→ℝ}{C V:Credit}{B:Torch H T p v E A K}
    {t m N:ℕ}{ε reach:ℝ}{c:Verse (R.family.labels.level d)}
    (same:B.L.V.draws=L)(ruler:L.S.a N/L.S.a m=ε)(top:t ≤ N)
    (seat:Seated R W survey target hd p H v E A K U F C V B t N c
      (ε/(L.S.a t/L.S.a m)) ((reach/(L.S.a t/L.S.a m))^h))(price:Credit)
    (issued:WilsonIndependentMovingRosterLaneSeated.Certified R W survey target hd p H v E A K U seat price):
    let X:=seat.choose
    let δ:=paceT B.L.V.draws.S t N
    let fee:=(reach/(L.S.a t/L.S.a m))^h*WilsonIndependentMatchedFiledIncome.charge e c F
    X.vesselsC=B.L.V ∧ X.m=t ∧ X.N=N ∧ X.m+X.i=N ∧
      Licensed X B.L.V t N (δ^(h-d))⁻¹ δ (price.buy X.Age*fee):=by
  intro X δ fee
  have eqn:ε/(L.S.a t/L.S.a m)=δ:=by
    dsimp only [δ,paceT]
    rw [same,←ruler]
    field_simp [ne_of_gt (L.S.a_pos m),ne_of_gt (L.S.a_pos t)]
  obtain ⟨_,home,span,finish,_⟩:=seat.choose_spec
  refine ⟨issued.1,home,finish,?_,?_⟩
  · change seat.choose.m+seat.choose.i=N
    rw [home,span]
    omega
  · exact (congrArg (fun x:ℝ=>Licensed X B.L.V t N (x^(h-d))⁻¹ x (price.buy X.Age*fee)) eqn).mp issued.2

end YM.Integration.WilsonIndependentMovingRosterNormalizedSeats

