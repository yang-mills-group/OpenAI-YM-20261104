import YangMills.WilsonProof.NativeSupport.FreshReclosure
import YangMills.WilsonProof.NativeSupport.CalibratedPlant

/-! Multiply fresh singleton sources into a density that already carries
all the inherited regular and dirty coefficients. The same original flag
set determines which part of each fresh singleton goes into the gas. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.InletSusceptibility.JointShadow
open Finset Function Lattice RG Wilson Marker Extra.Trajectories MergeProof MergeProof.Accent
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} {V J : Type} [Fintype V] [DecidableEq V] [Fintype J]
variable (R : Rep G n) (B : Census V) (born : J→V) (X : J→Support n) (v : J → Config G n → ℂ)

def fresh (regular : Bool) (j : J) (U : Config G n) : Poly B :=
  Poly.send (B.fire (born j))
    (if Healthy R.p.threshold (X j) U ↔ regular=true then v j U else 0)

variable (K : Box n → Config G n→Poly B) (H : Config G n→Poly B)
variable (permits : ∀ U i, K i U≠0 → Sure i) (silent : ∀ U,(H U).part B.quiet=0)

include permits silent in
theorem mount_flags (U : Config G n) :
    play R B (closure K (fresh R B born X v false) X R.p.threshold)
      (fun Y=> H Y+∑ j,fresh R B born X v true j Y) U =
      play R B K H U * ∏ j,(1+Poly.send (B.fire (born j)) (v j U)) := by
  let A := fresh R B born X v
  have dirty (j:J) : A false j U≠0 → ¬Healthy R.p.threshold (X j) U := by
    intro live ok
    exact live (by simp [A,fresh,ok])
  have quiet : (∑ j,A true j U).part B.quiet=0 := by
    rw [Poly.part_sum]
    exact sum_eq_zero fun j _=>by simp [A,fresh,Ne.symm (B.fire_hot (born j))]
  have log_form : Poly.pass (∑ j,A true j U) = ∏ j,(1+A true j U) :=
    pass_sum (R:=B) univ (fun j : J=> B.fire (born j))
      (fun j _=> singleton_nonempty _) _
  have gas_form := allclosed K (A false) X R.p.threshold U (permits U) dirty
  have combine : (∏ j,(1+A true j U))*(∏ j,(1+A false j U)) =
      ∏ j,(1+Poly.send (B.fire (born j)) (v j U)) := by
    rw [←Finset.prod_mul_distrib]
    apply prod_congr rfl
    intro j _
    by_cases healthy : Healthy R.p.threshold (X j) U <;> simp [A,fresh,healthy]
  unfold play
  change (Real.exp (R.exponent U):ℂ) • (Poly.pass (H U+∑ j,A true j U)*
    field (fun j=>closure K (A false) X R.p.threshold j U) _) = _
  rw [pass_add (silent U) quiet,log_form,gas_form,smul_mul_assoc,←combine]
  apply congrArg ((Real.exp (R.exponent U):ℂ) • ·)
  ring

end YM.Integration.InletSusceptibility.JointShadow
