import YM.Integration.WilsonOriginalProjectedCurvatureFoundry
import YM.QuadraticLocal.Tint.Provision
import YM.Integration.WilsonMovingMentorConcourse

/-! Sealing the complete signed incoming presentation under the actual semester invoice. -/
noncomputable section
namespace YM.Integration.WilsonOriginalProjectedCurvatureReceivedSeal
open Lattice RG Marker Ac QuadraticLocal QuadraticLocal.Earn
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato LocalComparison
open scoped Classical

variable {V α ι:Type} [DecidableEq V] [Countable ι] {G:Gauge} {n:Side}
  {D:Passport n V} {ρ:Census V} {P:Rep G n} (X:ι→Row D ρ G α)
  (incoming:Tint.Incoming D P α Empty ρ) {w:V→ℝ} (t:V→ℕ)
  {σ b z θ:ℝ} {rank height vol degree:ℕ}
  (roster:Scene.Armada X w t σ b rank height vol)
  (invoice:Invoice.Supports P.p z P.p.supportExponent (ConnectedActivityE6.Coat.gStep P.beta) σ θ)
local notation "bill" => Invoice.price P.p z (rank+vol+1) height P.p.supportExponent θ G

include roster invoice
theorem original (R:Run G) (i q:ℕ)
    (retained:incoming.hard.Paid w P.p.B P.p.supportExponent
      ((R.alloy.B.a.clock.hatBeta i)^(-(q:ℝ))*forcedDivisor R.family i))
    (total:bill*b ≤ 1) (localFee:bill*b*Real.exp (-θ)^P.p.B ≤ (ConnectedActivityE6.Coat.gStep P.beta)^degree) :
    ∃ certificate:Travel.Seal (Tint.Patrol.picture X incoming) w 2 1,
      Tint.Campus.Investor.Medal X incoming w certificate 0 ((ConnectedActivityE6.Coat.gStep P.beta)^degree) := by
  have room:=Graces.glyphBound R.family.path.levels i
  have small: (R.alloy.B.a.clock.hatBeta i)^(-(q:ℝ)) ≤ 1:=
    Real.rpow_le_one_of_one_le_of_nonpos (R.alloy.B.a.fits.delayed i).le (neg_nonpos.mpr (Nat.cast_nonneg _))
  have hard:=incoming.hard.mono retained
    ((mul_le_mul_of_nonneg_right small room.1.le).trans ((one_mul _).trans_le room.2))
  have old:incoming.old.Paid w P.p.B P.p.supportExponent 0:=
    Spill.Foundry.empty_lit P incoming P.p.supportExponent P.p.B
  exact Tint.Campus.Investor.pays X incoming w roster.positive t roster invoice
    (by linarith only [total]) localFee old hard

end YM.Integration.WilsonOriginalProjectedCurvatureReceivedSeal
