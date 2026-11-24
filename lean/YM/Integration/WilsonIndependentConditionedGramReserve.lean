import YM.Integration.WilsonIndependentConditionedGramCampus
import YM.Integration.WilsonIndependentConditionedBankPublicGram

/-! The two earned stopped coordinate reserves pay the entire public Gram
convolution tail on the original appointed four-corner board. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 360000
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedGramReserve
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open Filter Function Finset Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open RG.Supply Next.Foundations WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza
open WilsonCoeffUV.Bank.Mosaic PhysicalNext.Repeat.Legato
open WilsonIndependentConditionedPairProbeSemester (Home)
open WilsonIndependentConditionedPairProbes (Prices)
open WilsonIndependentConditionedPairFour (Assigned)
open WilsonIndependentConditionedBankPublicGram (residual internal pivots)
open WilsonIndependentConditionedBankTable (measure)
open WilsonIndependentConditionedBankCash (reserve)
open WilsonIndependentMatchedFittedSeat (dose)
open WilsonPositionProgramTrialHomeDose (publicDose)
open WilsonIndependentConditionedGramPrices (profile)
open WilsonSeparatedPrefixMovingCalendar (epoch)
open WilsonPhysicalMarkedDefect.RawProduct (belt positive)
open WilsonIndependentFittedMixedCash (embed)
open scoped BigOperators Topology Classical
variable {G:Gauge}{e k u u₀:ℕ}
local notation "J" => Fin 2
local notation "C" => Credit.leanC

theorem original {R:Run G}{Q:J→SealR G}{own:∀s,Rails (Q s).h k u₀ e}
    {V:Realm G (e+1) C}{coins:Prices}{j:ℕ}{port:∀s,Home R (Q s) (own s) j}
    {ι:J→Type*}{P:(s:J)→ι s→TowerS G (Q s).D}{w:(s:J)→ι s→ℝ}{b host m K N:ℕ}
    (rate:Credit)(paid:WilsonIndependentConditionedGramCampus.Paid V (Q 0) (Q 1) k rate)
    (T:Assigned R Q own V coins j port ι P w u b host m K N)
    (live:V.anchor ≤ host)(older:host ≤ m)(cut:m ≤ K)(vac:K ≤ N)
    (pick:(s:J)→ι s)(a:J→ℝ)(φ:(s:J)→Rarity (Q s).D)(B:J→ℝ)(y:ℝ)(o:CellR)
    (test:∀s,Amplitude (φ s) (B s))(ω:Fin 0→YForest G)(q:ℕ)(order:q ≤ e):
    let X:=fun s=>T.cuts s (pick s)
    let x:=paceT V.draws.S m K
    let A:=rate.buy (epoch V host K)*(x^((Q 0).h+(Q 1).h))⁻¹*
      (coinMat ((Q 0).h+(Q 1).h) e*profile (φ 0) y (B 0)*profile (φ 1) y (B 1))
    residual V (Q 0) (Q 1) k host m K N (φ 0) (φ 1) y o 0 ω q
      (publicDose (Q 0) (X 0) (a 0)) (publicDose (Q 1) (X 1) (a 1)) ≤
      (((q+1:ℕ):ℝ)*A)*reserve (X 0) host q (dose (X 0) (a 0))*reserve (X 1) host q (dose (X 1) (a 1)):=by
  classical
  intro X x A
  let Y:=(fun (s:J)(v:Alma (Q s).F)=>
    belt q (embed (WilsonIndependentConditionedBankGram.weights (X s) host (dose (X s) (a s)) v)))
  have h (s:J):WilsonIndependentConditionedBankGram.weights (X s) host (dose (X s) (a s))=
      internal V (Q s) host m N (publicDose (Q s) (X s) (a s)) :=
    pivots (X s) V host m N (T.levels s _) (T.reset s _) (T.home s _) (T.vacuum s _) (a s)
  have pp (s:J)(v:Alma (Q s).F):0 ≤ Y s v:=positive q _
  have sum_r (s:J):reserve (X s) host q (dose (X s) (a s))=∑i,Y s i:=rfl
  unfold WilsonIndependentConditionedBankPublicGram.residual
  rw [←h 0,←h 1,sum_r 0,sum_r 1]
  calc
    _ ≤ ∑i,∑j,(Y 0 i*Y 1 j)*(((q+1:ℕ):ℝ)*A):=by
      apply sum_le_sum
      intro i _
      apply sum_le_sum
      intro n _
      exact mul_le_mul_of_nonneg_left ((paid host m K N live older cut vac (φ 0) (φ 1)
        (B 0) (B 1) y o (test 0) (test 1) i n ω).2 q order) (mul_nonneg (pp 0 i) (pp 1 n))
    _=_:=by
      simp only [sum_mul,mul_sum]
      rw [Finset.sum_comm]
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro n _
      ring

end YM.Integration.WilsonIndependentConditionedGramReserve
