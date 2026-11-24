import YM.Integration.WilsonIndependentMovingRosterLaneFilm

/-! Both dated lanes on the particular `CutsP` chosen by the original
seating receipt. Its fitted belt and complete intake are still given by
that very receipt's witness. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentMovingRosterLaneSeated
open Finset Lattice RG Wilson Source Labels PhysicalNext.Repeat.Legato XSpace XSpace.Rose XSpace.Cirrus
open WilsonCoeffUV WilsonCoeffUV.Cosmos WilsonCoeffUV.Soil WilsonCoeffUV.Blue WilsonCoeffUV.Embroider
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Shard WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open WilsonCoeffUV.Bank WilsonCoeffUV.Power PowerSeries PertExtension Orb.SlotEvaluation FVA2
open Function Matrix Laurent Bloch Metric FreeResolvent Work.F08 Tree
open Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source.Drops Planned.PrimaryIntegral295 Place Carrier WardBin Bulb Realm PathCost Ore
open WilsonIndependentMatchedNamedPair (sectionAt)
open WilsonIndependentFittedExteriorRung (Seated)
open WilsonIndependentMovingRosterLaneFilm (Licensed)
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G)(W:Initialize G){d h D k e u:ℕ}
    (survey target:Bool)(hd:d ≤ h)(p:h<D)(H:Hol G)(v:Rails h k u e)(E A K U:Credit)
local notation "T" => sectionAt R W target h

def Certified {F:Alma (R.family.labels.level d)→ℝ}{C V:Credit}{B:Torch H T p v E A K}
    {t N:ℕ}{c:Verse (R.family.labels.level d)}{δ boost:ℝ}
    (seat:Seated R W survey target hd p H v E A K U F C V B t N c δ boost)(rate:Credit):Prop:=
  let X:=seat.choose
  X.vesselsC=B.L.V ∧ Licensed X B.L.V t N (δ^(h-d))⁻¹ δ
    (rate.buy X.Age*(boost*WilsonIndependentMatchedFiledIncome.charge e c F))

theorem original:
    ∃rate:Credit,∀(F:Alma (R.family.labels.level d)→ℝ)(C V:Credit)(B:Torch H T p v E A K)
      (t N:ℕ)(c:Verse (R.family.labels.level d))(δ boost:ℝ),
      paceT B.L.V.draws.S t N=δ →
      ∀seat:Seated R W survey target hd p H v E A K U F C V B t N c δ boost,
        Certified R W survey target hd p H v E A K U seat rate:=by
  obtain ⟨rate,sold⟩:=WilsonIndependentMovingRosterLaneFilm.original H T p v E A K U
  refine ⟨rate,?_⟩
  intro F C V B t N c δ boost mesh seat
  let X:=seat.choose
  obtain ⟨book,home,_,last,ceil,_,fund,_,_,_,_⟩:=seat.choose_spec
  change X.L=B at book
  have same:X.vesselsC=B.L.V:=congrArg (fun Y=>Y.L.V) book
  have rung:paceT X.ax.S X.m X.N=δ:=by
    change paceT X.vesselsC.draws.S X.m X.N=δ
    rw [same,home,last,mesh]
  have pos:0 < δ:=mesh ▸ pace_pos _ _ _
  have paid:=sold X ceil (δ^(h-d)) (boost*WilsonIndependentMatchedFiledIncome.charge e c F)
    (pow_pos pos _) fund
  rw [rung,same,home,last] at paid
  exact ⟨same,paid⟩

end YM.Integration.WilsonIndependentMovingRosterLaneSeated

