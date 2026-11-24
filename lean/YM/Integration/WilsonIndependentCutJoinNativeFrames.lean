import YM.Integration.WilsonIndependentMovingRosterAllFineSeats

/-! The compensated Wick inversion and the ordinary passport are issued
by the same theatre at each named horizon. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentCutJoinNativeFrames
open Filter Function Finset Lattice RG RG.Supply Wilson PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open XSpace XSpace.Rose XSpace.Cirrus Source Source.Drops Labels Precision Next.Foundations
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Bank.Mosaic
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Bank.PathCost
open WilsonCoeffUV.Embroider WilsonCoeffUV.Shard WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.AuxPlates
open WilsonIndependentCutJoinPassport (All)
open WilsonIndependentMovingRosterAllFineSeats (Named)
open scoped BigOperators Topology Classical
local notation "C" => Credit.leanC
variable {G:Gauge}{H:Hol G}{e n height seats:ℕ}

def Funded (M:Master H)(R:Realm G (e+1) C)(height seats:ℕ):Prop:=
  ∀Q:SealR G,Named M height seats Q → Nonempty (AheadT H R C C Q C)

theorem original (M:Master H)(A:Levels G)(chart:ChartRatio G)(y:ℕ→ℝ)(s:ℕ)
    (grant:All M A chart y e s height seats)(R:Realm G (e+1) C)
    (draw:R.draws=A)(quiet:R.paid=chart)(tariff:R.y=y)(anchor:R.anchor=s):
    Funded M R height seats:=by
  intro Q word
  obtain ⟨W,source,clock,price,home,west,_⟩:=grant Q.h Q.D Q.path word.1 word.2.1
  have ticket:Nonempty (AheadT H R C C (BayV M Q.h Q.D Q.path) C):=
    ⟨⟨⟨W,source.trans draw.symm,clock.trans quiet.symm,price.trans tariff.symm,home.trans anchor.symm⟩,west⟩⟩
  rwa [word.2.2] at ticket

theorem roster {M:Master H}{R:Realm G (e+1) C}(cash:Funded M R height seats)
    (Q:Fin (n+1)→SealR G)(named:∀s,Named M height seats (Q s)):
    FramesR H R C C Q C ∧ HorizonP H R C C Q:=by
  refine ⟨fun s=>cash _ (named s),?_⟩
  intro s
  obtain ⟨paid⟩:=cash _ (named s)
  exact ⟨paid.p⟩

end YM.Integration.WilsonIndependentCutJoinNativeFrames

