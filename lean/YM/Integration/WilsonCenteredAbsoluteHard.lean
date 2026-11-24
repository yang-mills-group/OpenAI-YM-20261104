import YM.Integration.WilsonCenteredHardAnswers
import YM.Integration.WilsonCenteredFiledAtoms

/-! Hear the complete original hard-gas contribution to the physical
ordinary mixed-minus-counterterm source on its own Wilson representation. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCenteredAbsoluteHard
open Finset RG Lattice Wilson Marker QuadraticLocal Ac Planned.GuardedAtom Push.Local
open WilsonCenteredHardMount WilsonCenteredHardAnswers
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} {V X : Type} [DecidableEq V] [Fintype V] {R : Census V}
    {o : V→Site n} {P : Rep G n} (H : Hard X P.p P.activities.forced P.activities.K o R)
    (K : Guard.Keeper P.p P.activities) (Z : Support n)
    (u : ℕ×Finset ℕ ↪ ℕ) (l : (ℕ×ℕ)×Finset ℕ ↪ ℕ)

def gas (x : X) (U : Config G n) := ∑' F,QuadraticLocal.Fusion.Attached.packet P.activities P.p (H.hard x) U F

theorem physical (x : X) (U : Config G n) (a b c : V) (M : R.Mode) (apart : a≠b)
    (pair : M.val={a,b}) {v k1 k2 k3 : ℝ} (quiet : P.activities.KBound P.p v)
    (charged : Summable (QuadraticLocal.Fusion.Attached.packet P.activities P.p (H.hard x) U))
    (firstAB : ForceCost P.p P.activities (first H K Z M x u) k1)
    (firstC : ForceCost P.p P.activities (first H K Z (R.fire c) x u) k2)
    (two : ForceCost P.p P.activities (second H K Z a b x l) k3) :
    (gas H x U).part M-(gas H x U).part (R.fire c)=
      read (P:=P) (first H K Z M x u) U-read (P:=P) (first H K Z (R.fire c) x u) U+
      read (P:=P) (second H K Z a b x l) U := by
  have scores (s : R.Mode) : HasSum (fun F=>(QuadraticLocal.Fusion.Attached.packet P.activities P.p (H.hard x) U F).part s)
      ((gas H x U).part s) := (Poly.get s).hasSum charged.hasSum
  have exactAB:=first_sum H K Z x U M u firstAB quiet
  have exactC:=first_sum H K Z x U (R.fire c) u firstC quiet
  have both:=second_sum H K Z x U a b l two quiet
  apply ((scores M).sub (scores (R.fire c))).unique
  apply ((exactAB.sub exactC).add both).congr_fun
  intro F
  by_cases old : P.activities.admissible P.p U F
  · simp only [old,if_pos,QuadraticLocal.Fusion.Attached.packet]
    change WilsonCenteredHardPartitions.face c M (∏j∈F,H.hard x j U)=_
    rw [WilsonCenteredHardPartitions.collection a b c M apart pair]
    simp [WilsonCenteredHardPartitions.booked,WilsonCenteredHardPartitions.face,
      distinct,once,leg,H.quiet,sub_mul,sum_sub_distrib]
  simp [old,QuadraticLocal.Fusion.Attached.packet]

end YM.Integration.WilsonCenteredAbsoluteHard
