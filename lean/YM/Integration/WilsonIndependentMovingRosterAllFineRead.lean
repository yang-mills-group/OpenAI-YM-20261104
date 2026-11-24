import YM.Integration.WilsonIndependentMovingRosterSigned
import YM.Integration.WilsonSeparatedPrefixMovingHighGrades

/-! Price the whole signed fine-cut scalar and its complete finite thermal
evaluation on the two actual sums on the same original Mer history. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentMovingRosterAllFineRead
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMovingRosterCut (residual)
open WilsonIndependentMovingRosterRejoin (crossed)
open WilsonSeparatedPrefixMovingUnformedSector (fresh)
open Finset
open scoped BigOperators Topology Classical

variable {G:Gauge}{n e:ℕ}{E:Credit}

/-- All printed scalar grades and their signed thermal evaluation at the same
receiver, including the unit and the part strictly above every fixed order. -/
def Heard (e target:ℕ)(T price:ℝ)(f:ℕ→ℝ):Prop:=
  (∀q ≤ e,‖f q‖ ≤ (T^target)⁻¹*price) ∧
  ∀g:ℝ,0 ≤ g → g ≤ 1 →
    ‖∑q∈range (e+1),g^q*f q‖ ≤ (∑q∈range (e+1),g^q)*((T^target)⁻¹*price) ∧
    ∀J:ℕ,‖WilsonSeparatedPrefixMovingHighGrades.above J e g f‖ ≤ (e+1:ℕ)*(g^(J+1)*((T^target)⁻¹*price))

theorem original {H:Hol G}{W V:Credit}(R:Realm G (e+1) E)(Q:Fin (n+1)→SealR G)(F:SealR G)
    (roster:HorizonP H R W V Q)(far:PassportC H R F W V)(φ:Wilt Q)(ψ:Rarity F.D)
    (X:Herit Q)(Y:F.Rider)(o:CellR)(y:ℝ)(t m older N target:ℕ)(ω:Fin 0→YForest G)
    (live:R.anchor ≤ t)(start:t ≤ m)(ear:older ≤ m)(top:m ≤ N)(A B:ℝ)
    (unformed:∀q ≤ e,‖∑d∈range (N-m),fresh R Q F φ ψ X Y o y t m older N q ω (m+d)‖ ≤
      ((paceT R.draws.S m t)^target)⁻¹*A)
    (formed:∀q ≤ e,‖∑d∈range (N-m),∑j∈(range (N-m)).filter (fun j=>d ≤ j),
        crossed R Q F φ ψ X Y o y t m older N q ω (m+d) (m+j)‖ ≤
      ((paceT R.draws.S m t)^target)⁻¹*B):
    Heard e target (paceT R.draws.S m t) (A+B) (fun q=>(residual R Q F φ ψ X Y o y t m older N).2 q 0 ω):=by
  let T:=paceT R.draws.S m t
  let f q:=(residual R Q F φ ψ X Y o y t m older N).2 q 0 ω
  have all (q:ℕ)(hq:q ≤ e):‖f q‖ ≤ (T^target)⁻¹*(A+B):=by
    dsimp only [f]
    rw [WilsonIndependentMovingRosterSigned.original R Q F roster far φ ψ X Y o y t m older N q ω live start ear top]
    exact (norm_add_le ..).trans ((add_le_add (unformed q hq) (formed q hq)).trans_eq (mul_add ..).symm)
  have paid:0 ≤ A+B:=nonneg_of_mul_nonneg_right ((norm_nonneg _).trans (all 0 (Nat.zero_le _)))
    (inv_pos.mpr (pow_pos (pace_pos ..) _))
  refine ⟨all,fun g pos small=>⟨?_,fun J=>?_⟩⟩
  · apply (norm_sum_le ..).trans
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro q hq
    rw [norm_mul,Real.norm_of_nonneg (pow_nonneg pos _)]
    exact mul_le_mul_of_nonneg_left (all q (by have:=mem_range.mp hq;omega)) (pow_nonneg pos _)
  · exact WilsonSeparatedPrefixMovingHighGrades.original J e target g T (A+B) f pos small (pace_pos ..)
      paid (fun q _ hq=>all q hq)

end YM.Integration.WilsonIndependentMovingRosterAllFineRead
