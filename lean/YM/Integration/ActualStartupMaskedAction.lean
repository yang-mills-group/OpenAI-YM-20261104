import YM.Integration.ActualRunStartupInput
import YM.IterationFour.Shore.Rose
import YM.Pert.Asymptotics.RawAxis

/-! Exact global masked startup decomposition on the original Run.
The finite album and the complete chip remainder retain every native mask.
No smallness, Invoice, calibration cap, or alternate representation is assumed. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualStartupMaskedAction

open Function Finset Lattice Wilson RG
open PhysicalNext.Repeat.Legato
open WilsonStartup WilsonStartup.Start WilsonStartup.IterationFour
open YM.IterationFour YM.IterationFour.Vacuum Progress.DirectedRecipe
open AnalyticBridge VerifiedReset Collection
open scoped Classical BigOperators

variable {G : Gauge}

theorem raw_split {n : Side} (P : BudgetPoint) (S : Stage)
    (r : ℕ) (hr : 2 ≤ r) (β : ℝ) (hβ : 0 < β) (U : Config G n) :
    (raw G n S.clip P β).additive P U =
      Render.renders (Render.prefactor (Currency.gain β)) P U
        (album G n P S r) +
      (slate G n (Start.weight S.clip β) (chip G r)).amount P U := by
  let Y := ∑ i : Key n, masked P.threshold i.skin
    (element G (chip G r) i.positive) U
  let T := ∑ j ∈ Finset.range (r - 2), ∑ i : Key n,
    masked P.threshold i.skin (element G (terms G (5 + j)) i.positive) U
  have hV : Y + T = ∑ i : Key n, masked P.threshold i.skin i.accrual U := by
    unfold Y T
    rw [Finset.sum_comm (s := Finset.range (r - 2)) (t := Finset.univ),
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : Healthy P.threshold i.skin U
    · simp_rw [masked_eq P.threshold i.skin _ U hi, Key.accrual_def]
      unfold element
      rw [chip_sum G r hr, Quad.surplus_actual]
      rfl
    · simp_rw [masked_ne P.threshold i.skin _ U hi,
        Finset.sum_const_zero, zero_add]
  change (raw G n S.clip P β).additive P U =
    Render.renders (Render.prefactor (Currency.gain β)) P U
      ((List.range (r - 2)).map (top_terms G n P S)) + _
  rw [Start.written_sum, pages (r - 2) U hβ, tally]
  change Start.weight S.clip β *
      (∑ i : Key n, masked P.threshold i.skin i.accrual U) =
    Start.weight S.clip β * T + Start.weight S.clip β * Y
  rw [← hV]
  ring

/-- The original full chip payload, with its original scalar and supports. -/
def remainder (R : Run G) (N p r : ℕ) :
    Payload G (R.family.side N p) :=
  slate G (R.family.side N p)
    (Start.weight (R.family.path.levels.params N).clip
      (R.family.path.β N p N)) (chip G r)

/-- The actual top exponent is the masked finite album plus its literal
chip remainder. This is an identity at every field, not only near identity. -/
theorem exponent (R : Run G) (T : Campaign R) (N p r : ℕ) (hr : 2 ≤ r)
    (U : Config G (R.family.side N p)) :
    let X := R.family.path.rep N p N
    X.exponent U = X.scalar -
      (X.path.inChannels X.clip X.p X.beta U +
        Render.renders
          (Render.prefactor (Pert.Asymptotics.regulatorRun R.family N p N))
          X.p U (album G (R.family.side N p) X.p
            (R.family.path.levels.params N) r)) -
      (remainder R N p r).amount X.p U := by
  dsimp only
  have hstart : R.family.path.rep N p N =
      PhysicalNext.Repeat.Tent.launch (A := R.alloy) N p
        (R.family.path.β N p N) :=
    (T.center N p).startStory T.gains
  have hp : (R.family.path.rep N p N).p =
      R.family.path.levels.budget N :=
    (R.makes.wilson.represents N p N le_rfl).vac
  have hβ : 0 < R.family.path.β N p N :=
    lt_of_lt_of_le (half_pos (WardBin.hot _ _))
      (R.makes.wilson.represents N p N le_rfl).band.1
  have hraw : (R.family.path.rep N p N).exponent U =
      (R.family.path.rep N p N).scalar -
        (R.family.path.rep N p N).path.inChannels
          (R.family.path.rep N p N).clip
          (R.family.path.rep N p N).p
          (R.family.path.rep N p N).beta U -
      (raw G (R.family.side N p) (R.family.path.levels.params N).clip
        (R.family.path.levels.budget N) (R.family.path.β N p N)).additive
        (R.family.path.levels.budget N) U := by
    have hnative := YM.IterationFour.Shore.equal_stamp
      (Planned.Port.pot R.alloy.B.a N p)
      (PhysicalNext.Repeat.Tent.tap (A := R.alloy) N p
        (R.family.path.β N p N))
      (R.alloy.B.kin.path N N) (R.alloy.B.a.params N).clip
      (R.alloy.B.a.budget N) (R.family.path.β N p N) 0
      (show Config G (R.alloy.B.a.S.side N p) from U)
    exact Eq.mpr (congrArg (fun X : Rep G (R.family.side N p) =>
      X.exponent U = X.scalar -
        X.path.inChannels X.clip X.p X.beta U -
        (raw G (R.family.side N p) (R.family.path.levels.params N).clip
          (R.family.path.levels.budget N) (R.family.path.β N p N)).additive
          (R.family.path.levels.budget N) U) hstart) hnative
  rw [hraw, hp, raw_split _ _ r hr _ hβ]
  dsimp only [remainder, Pert.Asymptotics.regulatorRun, Currency.gain]
  ring

end YM.Integration.ActualStartupMaskedAction
end
