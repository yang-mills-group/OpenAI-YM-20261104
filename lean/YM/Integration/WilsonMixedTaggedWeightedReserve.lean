import YM.MergeProof.Endow
import YM.Push.ABSOLUTE_SUMS.Basic

/-! One support exponent is transferred without changing any fine marker
weight. In particular, an individual input charge is allowed to be small. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMixedTaggedWeightedReserve
open Finset Function Lattice Wilson RG Marker Push AbsoluteSums Extra.Histories Ac MergeProof MergeProof.Accent
open GridApprox.Nil
open scoped BigOperators Classical

theorem original {G:Gauge} {n:Side} {I V:Type} [Fintype I] [DecidableEq V] {J:Census V}
    {S:I→Support n} {F:I→Config G n→Poly J} {B D:ℕ} {α ρ:ℝ} {w:V→ℝ}
    (bank:Towed w S F B α ρ) (wp:∀v,0<w v)
    (spans:∀i U s,(F i U).part s≠0→D≤coverNumber B (S i)) :
    Towed w S F B (α-1) (Real.exp (-(D:ℝ))*ρ) := by
  obtain ⟨wallet,_,hit,atoms⟩:=bank
  let next (i:I):ℝ:=if D≤coverNumber B (S i) then wallet i else 0
  have wn (i:I):0≤wallet i:=((atoms i).fares wp).1
  have nn (i:I):0≤next i:=by dsimp only [next];split <;> first | exact wn i | exact le_rfl
  refine ⟨next,(hasSum_fintype _).summable,?_,?_⟩
  · intro x
    apply budget_mono (budget_scale (Real.exp_pos (-(D:ℝ))).le (hit x))
    · intro i
      split <;> first | exact mul_nonneg (nn i) (Real.exp_pos _).le | exact le_rfl
    intro i
    by_cases hx:x∈S i
    · simp only [if_pos hx]
      by_cases long:D≤coverNumber B (S i)
      · rw [show next i=wallet i from if_pos long]
        have extent:(D:ℝ)≤(coverNumber B (S i):ℝ):=by exact_mod_cast long
        have charge:Real.exp ((α-1)*(coverNumber B (S i):ℝ)) ≤
            Real.exp (-(D:ℝ))*Real.exp (α*(coverNumber B (S i):ℝ)) := by
          rw [←Real.exp_add,Real.exp_le_exp]
          linarith only [extent]
        calc wallet i*_≤wallet i*(Real.exp (-(D:ℝ))*Real.exp (α*(coverNumber B (S i):ℝ))) :=
               mul_le_mul_of_nonneg_left charge (wn i)
             _ = _ := by ring
      · rw [show next i=0 from if_neg long,zero_mul]
        exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (wn i) (Real.exp_pos _).le)
    · simp only [if_neg hx,mul_zero,le_refl]
  · intro i
    by_cases long:D≤coverNumber B (S i)
    · simpa only [next,if_pos long] using atoms i
    · refine ⟨0,le_rfl,?_,?_⟩
      · intro U s
        have z:(F i U).part s=0:=by by_contra live;exact long (spans i U s live)
        rw [z,norm_zero];exact le_rfl
      · simp [wordsPrice,next,long]

end YM.Integration.WilsonMixedTaggedWeightedReserve
