import YM.Integration.WilsonIndependentConditionedBankCorner
import YM.Integration.WilsonIndependentConditionedPairTrialCost

/-! One finite table and two source-independent inverse fees for all original ordered pairs. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 450000
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedBankFour
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open RG.Supply Next.Foundations WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza
open WilsonCoeffUV.Bank.Mosaic PhysicalNext.Repeat.Legato XSpace.Rose XSpace.Cirrus XSpace
open WilsonMarkedIndependentNormalizedElection (deck)
open WilsonIndependentConditionedPairProbeSemester (Home)
open WilsonIndependentConditionedPairProbes (Prices)
open WilsonIndependentConditionedPairFiledSemester (Tested)
open WilsonIndependentMatchedFiledIncome (plate charge)
open WilsonIndependentMatchedNamedPair (sectionAt)
open scoped BigOperators Topology Classical
variable {G:Gauge}{h D e k u u₀:ℕ}
local notation "J" => Fin 2
local notation "C" => Credit.leanC

open WilsonIndependentConditionedBankCorner (Bill input)
open WilsonIndependentConditionedPairFour (Assigned)
open WilsonIndependentConditionedPairProbes (Prices charge)
open WilsonIndependentConditionedPairTrialCost (roof)
open WilsonIndependentFittedPivotCash (view)
open WilsonIndependentMatchedFittedSeat (receiving)
open WilsonIndependentConditionedBankPublicGram (response)
open WilsonPositionProgramTrialHomeDose (publicDose)

def Enrolled {R:Run G}{Q:J→SealR G}{own:∀s,Rails (Q s).h k u₀ e}
    {V:Realm G (e+1) C}{coins:Prices}{j:ℕ}{port:∀s,Home R (Q s) (own s) j}
    {ι:J→Type*}{P:(s:J)→ι s→TowerS G (Q s).D}{A:(s:J)→ι s→ℝ}{u b host m K N:ℕ}
    (T:Assigned R Q own V coins j port ι P A u b host m K N)(L M:Credit):Prop:=
  ∀(pick:(s:J)→ι s)(ζ:ℝ)(a B:J→ℝ)(t z:ℝ),ζ ≤ 1/4 → ((∑s,(Q s).h:ℕ):ℝ)+ζ < b → 0<t →
    let X:=fun s=>T.cuts s (pick s)
    let f:=charge Q own C C C C V X coins u b host m K ζ a B t z
    ∀(φ:(s:J)→Rarity (Q s).D)(y:ℝ)(o:CellR),
      (∀s s',s≠s'→ClearDay (φ s) (φ s') t) → (∀s,radiusH (φ s) 1 y ≤ z) → (∀s,Amplitude (φ s) (B s)) →
      ∀(q:ℕ),q ≤ e → ∀(g:ℝ),|g| ≤ 1 → ∀w,
      Bill Q own C C C C V X host m K N q g (roof f) L M a φ y o w

theorem appointed (Q:J→SealR G)(own:∀s,Rails (Q s).h k u₀ e):∃L M:Credit,
    ∀{R:Run G}{V:Realm G (e+1) C}{coins:Prices}{j:ℕ}{port:∀s,Home R (Q s) (own s) j}
    {ι:J→Type*}{P:(s:J)→ι s→TowerS G (Q s).D}{A:(s:J)→ι s→ℝ}{u b host m K N:ℕ}
    (T:Assigned R Q own V coins j port ι P A u b host m K N),host ≤ m → Enrolled T L M:=by
  obtain ⟨L,M,priced⟩:=WilsonIndependentConditionedBankRelative.original (H:=hol G) (Q₁:=Q 0) (Q₂:=Q 1)
    (v₁:=own 0) (v₂:=own 1) (E:=C) (W:=C) (K:=C) (U:=C) C
  refine ⟨L,M,?_⟩
  intro R V coins j port ι P A u b host m K N T older pick ζ a B t z gain room ht X f φ y o apart sizes bounds q order g small w
  obtain ⟨nonneg,issued⟩:=WilsonIndependentConditionedPairTrialCost.original T pick ζ a B t z gain room ht
  obtain ⟨both,first,second⟩:=issued φ y o apart sizes bounds
  let files:=fun s=>T.levels s (pick s)
  let reset:=fun s=>T.reset s (pick s)
  let homes:=fun s=>T.home s (pick s)
  let births:=fun s=>T.birth s (pick s)
  let vac:=fun s=>T.vacuum s (pick s)
  have low:=priced (X 0) (X 1) (T.ahead 0 (pick 0)) (T.ahead 1 (pick 1)) ((files 1).trans (files 0).symm)
    ((reset 1).trans (reset 0).symm) ((vac 1).trans (vac 0).symm) ((homes 1).trans (homes 0).symm)
    ((births 1).trans (births 0).symm) host ((homes 0) ▸ older) (a 0) (a 1) (φ 0) (φ 1) y o q order g small w u
    (roof f) nonneg both first second
  have gram:=WilsonIndependentConditionedBankPublicGram.original V (X 0) (X 1) m K N host older
    (files 0) (reset 0) (homes 0) (births 0) (vac 0) (files 1) (reset 1) (homes 1) (births 1) (vac 1)
    (a 0) (a 1) (φ 0) (φ 1) y o 0 w q g small
  let actual:=view (X 0) host q g (input Q own C C C C X 0 (a 0) (φ 0) y o)
    (input Q own C C C C X 1 (a 1) (φ 1) y o) w
  let fitted:=view (X 0) host q g (receiving (X 0) (a 0) (φ 0) y o (X 0).i)
    (receiving (X 1) (a 1) (φ 1) y o (X 1).i) w
  let pane:=response V (Q 0) (Q 1) k host m K N (φ 0) (φ 1) y o 0 w q g
    (publicDose (Q 0) (X 0) (a 0)) (publicDose (Q 1) (X 1) (a 1))
  have edge:‖actual-pane‖≤‖actual-fitted‖+‖fitted-pane‖:=by
    simpa only [dist_eq_norm] using dist_triangle actual fitted pane
  exact edge.trans (add_le_add low gram)

end YM.Integration.WilsonIndependentConditionedBankFour
