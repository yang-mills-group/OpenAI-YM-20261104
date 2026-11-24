import YM.Integration.WilsonPositionProgramInfraredAtlas
import YM.Integration.WilsonPositionProgramSubmittedGeometry
import YM.FVAAlt2.Rocket.Stamps

/-! The common real-space meter has polynomial cost in the reciprocal spacing and logarithmic cost in the auxiliary period. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionProgramInfraredMeter
open Lattice RG RG.Supply Input Org PhysicalNext PhysicalNext.Repeat Legato OPE OPE.Owl
open RegulatorIR RegulatorIR.Oracle RegulatorIR.Ledger RegulatorIR.FVAAlt2 RegulatorIR.FVAAlt2.Rocket
open RegulatorIR.FVAAlt2.Kick RegulatorIR.Atlas RegulatorIR.Uniform WilsonPositionProgramCommonWindow WilsonPositionProgramVariableCircuit
open WilsonPositionProgramInfraredCircuit WilsonPositionProgramSubmittedGeometry
open scoped Classical Topology ENNReal
variable {G : Gauge} (C : Run G) (D : XSpace.Run) {X : Type} (m j : X → ℕ) (w : X → ℕ → ℕ)
    (blocks : ∀ x k, (C.family.S.block (m x+k)).val=D.ratio^(w x k)) (i : X → ℕ)
local notation "S" => WilsonPositionProgramInfraredCircuit.circuit C D m j w blocks
local notation "num" => WilsonPositionProgramInfraredCircuit.count D j w
local notation "B" => WilsonPositionProgramInfraredAtlas.budget C D m j w blocks

def amount (H : ℝ) (x : X) : ℝ := 1+RG16.Lambda C.family.path.levels (m x+j x) +
  |Real.log ((num (Page.opening j x)).val:ℝ)|+(max 0 H+1)/(D.step (i x)).spacing

theorem lower (H : ℝ) (x : X) : 1 ≤ amount C D m j w i H x := by
  have stage := (RG16.Literal.lambda_pos C.family (m x+j x)).le
  have extra : 0 ≤ (max 0 H+1)/(D.step (i x)).spacing := by
    exact div_nonneg (by have : 0 ≤ max 0 H := le_max_left ..; linarith) (D.step _).positive.le
  dsimp [amount]; linarith [abs_nonneg (Real.log ((num (Page.opening j x)).val:ℝ))]

def wallet (H : ℝ) : Uniform.Meter X := ⟨fun x=>ENNReal.ofReal (amount C D m j w i H x),
  fun x => by rw [←ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (lower C D m j w i H x),fun _=>ENNReal.ofReal_ne_top⟩

theorem age (H : ℝ) : OfAge (B) (wallet C D m j w i H) := by
  apply (Poly.roof (coverL j (wallet C D m j w i H))).mono
  intro t
  refine ENNReal.ofReal_le_ofReal ?_
  let p := (num (Page.opening j t.bindW)).val
  let n := (num t).val
  have room : n ≤ p := by
    change D.finalSide.side.val*D.ratio^elapsed (w t.bindW) (remaining j t) ≤
      D.finalSide.side.val*D.ratio^elapsed (w t.bindW) (j t.bindW-0)
    apply Nat.mul_le_mul_left
    apply Nat.pow_le_pow_right (Nat.zero_lt_of_lt D.large)
    rw [Nat.sub_zero]
    exact Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.sub_le ..))
  have hn : 0 < (n : ℝ) := by exact_mod_cast (num t).property
  have hp : (1:ℝ) ≤ p := by exact_mod_cast (num (Page.opening j t.bindW)).property
  have hn1 : 1 ≤ (n:ℝ) := by have := (num t).property; dsimp [n]; exact_mod_cast this
  have price : |Real.log ((p:ℝ)/n)| ≤ |Real.log (p:ℝ)| := by
    have large : 1 ≤ (p:ℝ)/n := (one_le_div hn).2 (by exact_mod_cast room)
    rw [abs_of_nonneg (Real.log_nonneg large),abs_of_nonneg (Real.log_nonneg hp)]
    exact Real.log_le_log (by positivity) (div_le_self (by positivity) hn1)
  change 1+RG16.Lambda C.family.path.levels (m t.bindW+j t.bindW)+|Real.log ((p:ℝ)/n)| ≤ 1+RG16.Lambda C.family.path.levels (m t.bindW+j t.bindW)+|Real.log (p:ℝ)|+(max 0 H+1)/(D.step (i t.bindW)).spacing
  linarith [div_nonneg (a:=max 0 H+1) (by positivity) (D.step (i t.bindW)).positive.le]

theorem displacements {k : ℕ} (H : ℝ) (z : X → Fin k → Cover) (c : X → Four ℝ)
    (inside : ∀ x b, dist (center (D.step (i x)) (c x)) (Motion.slide 1 (z x b)) ≤ H/(D.step (i x)).spacing)
    (b : Fin k) : Nearest (fun x=> center (D.step (i x)) (c x)) (wallet C D m j w i H) (fun x=>z x b) := by
  constructor
  apply (Poly.roof (wallet C D m j w i H)).mono
  intro x
  apply ENNReal.ofReal_le_ofReal
  apply (inside x b).trans
  change H/(D.step (i x)).spacing ≤ 1+_+_+(max 0 H+1)/(D.step (i x)).spacing
  have := div_le_div_of_nonneg_right (show H ≤ max 0 H+1 by have := le_max_right 0 H; linarith) (D.step (i x)).positive.le
  linarith [RG16.Literal.lambda_pos C.family (m x+j x), abs_nonneg (Real.log ((num (Page.opening j x)).val:ℝ))]

end YM.Integration.WilsonPositionProgramInfraredMeter
end
