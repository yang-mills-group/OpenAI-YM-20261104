import YM.Integration.WilsonMeasuredPointTopCoin
import YM.Integration.WilsonOlderFreshGraphChildDensity

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMeasuredPointPhaseDebit
open Function Filter Finset Lattice Wilson RG Source Labels PhysicalNext.Repeat.Legato Next.Foundations
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G)(N per:ℕ)
local notation "F" => R.family.labels.level 4
local notation "I" => (F).Index
variable (station:WilsonPositionThermometerCapStation.Group R.family 6)(leg:Fin 2)
    (phase:ℂ→ₗ[ℝ]ℝ)
local notation "named" => WilsonNeutralOffsetCutoff.named R station N per leg.succ
local notation "coin" => (fun v:I=> ((WilsonNeutralCopiedProgram.fee R N per named phase
  (ConnectedActivityE6.Coat.gStep (R.family.beta N per)) v):ℂ))
local notation "topSize" => (F).coeffSize (Next.Rank.Price.awake R.family 4 N N per named)

theorem original (simple:G.Simple)(ready:R.family.ref 4≤ N)
    {n:Side} {o:Site n}{P:Rep G n}{κ σ C Λ δ w:ℝ}
    (law:P.Lawful σ C Λ δ w)(positive:0<κ) (upper lower:I → Config G n → ℂ)
    (amount:ℝ)(nonnegative:0≤amount)
    (cols:∀v:I,∃(Z:Coefficient (F) n)(b:ℝ),Z.Format o R.family.params P ∧
      Z.remBound o P κ b ∧ (∀U,Z.density o (R.family.localSection 4) P U=
        upper v U-(P.eval U:ℂ)*lower v U) ∧ b+(F).coeffSize Z.x≤amount):
    ∃(E:Coefficient (F) n)(b:ℝ),E.Format o R.family.params P ∧ E.remBound o P κ b ∧
      (∀U,E.density o (R.family.localSection 4) P U=
        (∑v:I,coin v*upper v U)-(P.eval U:ℂ)*(∑v:I,coin v*lower v U)) ∧
      b+(F).coeffSize E.x≤2*‖phase.toContinuousLinearMap‖*topSize*amount:=by
  classical
  choose Z b₁ fmt rem read wage using cols
  obtain ⟨fmt₁,rem₁,_,primary,density⟩:=WilsonOlderFreshGraphChildDensity.represented
    law positive coin Z b₁ fmt rem upper lower read
  refine ⟨WilsonOlderFreshGraphChildDensity.collected coin Z,∑v:I,‖coin v‖*b₁ v,
    fmt₁,rem₁,density,?_⟩
  have cost:(∑v:I,‖coin v‖)≤2*‖phase.toContinuousLinearMap‖*topSize:=by
    have bill:=WilsonMeasuredPointTopCoin.funded R N per simple ready named phase
    simp only [Complex.norm_real,Real.norm_eq_abs]
    convert bill using 1
    congr 2
  calc
    _ ≤ (∑v:I,‖coin v‖*b₁ v)+∑v:I,‖coin v‖*(F).coeffSize (Z v).x:=
      add_le_add_right primary _
    _ = ∑v:I,‖coin v‖*(b₁ v+(F).coeffSize (Z v).x):=by
      simp only [mul_add,Finset.sum_add_distrib]
    _ ≤ ∑v:I,‖coin v‖*amount:=Finset.sum_le_sum fun v _=>
      mul_le_mul_of_nonneg_left (wage v) (norm_nonneg _)
    _ = (∑v:I,‖coin v‖)*amount:=by rw [Finset.sum_mul]
    _ ≤ _:=mul_le_mul_of_nonneg_right cost nonnegative

end YM.Integration.WilsonMeasuredPointPhaseDebit
end
