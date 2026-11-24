import YM.MSbar.Pole.Scale.Laurent
import YM.MSbar.Pole.Scale.Queue

/-! # External momenta vs polarization. Rescale the former only. -/
noncomputable section
set_option autoImplicit false
namespace YM.MSbar.Pole
open Function Set Filter MeasureTheory Ambient
open scoped Topology ContDiff Classical BigOperators
variable {I : Type} [Fintype I]

namespace Momentum
variable (A : Finset I)
omit [Fintype I] in
def move {n : ℕ} (t : ℝ) (x : External I n) : External I n := fun i => if i∈A then t • x i else x i
variable {n : ℕ}
omit [Fintype I] in
lemma one (x : External I n): move A 1 x=x:= by ext; simp [move]
omit [Fintype I] in
lemma nesting (x:External I n) (s t:ℝ): move A s (move A t x)=move A (s*t) x:=by funext i; by_cases h:i∈A<;>simp [move,h,mul_smul]

def charge (n:ℕ) : External I n →L[ℝ] External I n := ContinuousLinearMap.pi fun i => if i∈A then ContinuousLinearMap.proj i else 0
lemma moving (t:ℝ) (x:External I n) : move A t x=x+(t-1) • charge A n x:=by
  ext1 i; by_cases h:i∈A
  · simp only [move,h,if_true,Pi.add_apply,Pi.smul_apply,charge,ContinuousLinearMap.pi_apply]; change t • x i=x i+(t-1) • x i; rw [sub_smul,one_smul,add_comm (x i),sub_add_cancel]
  simp [move,h,charge]
omit [Fintype I] in
lemma move_pad (t:ℝ)(x:External I n): move A t (place.pad n ∘ x)=place.pad n ∘ move A t x:=by
  funext i; by_cases h:i∈A; simp only [comp_apply,move,h,if_true,map_smul]; simp [h,move]
omit [Fintype I] in
lemma move_turn (t : ℝ) (J : place n ≃ₗᵢ[ℝ] place n) (x : External I n) : move A t (J ∘ x)=J ∘ move A t x:= by
  funext i; by_cases h:i∈A<;> simp [move,h]
def walks (t:ℝ) (n:ℕ): External I n →L[ℝ] External I n:= ContinuousLinearMap.id ℝ _ + (t-1) • charge A n
lemma walks_on (t:ℝ) (x:External I n) : walks A t n x=move A t x:= (moving A ..).symm
variable {R : ℝ} {F:ℂ→Cloud I}
def augments (A : Finset I) (n:ℕ) (F:ℂ→Cloud I) (z : ℂ) (x : ℝ×External I n) := F z n (move A x.1 x.2)
lemma puts {B : Finset I} (h : Meridian (zone R) F) (n:ℕ): Wall (zone R) (ticket (@id (ℝ × External I n))) 1 (augments B n F) := by
  let C:=External I n; let p:= ticket (@id (ℝ × C)); let S:= strip (ℝ × C) (zone R)
  let f (x:ℂ × (ℝ × External I n)) := (x.1,move B x.2.1 x.2.2)
  let T:=(ContinuousLinearMap.snd ℝ ℂ (ℝ×C)); let L:= (charge B n); let P:= (ContinuousLinearMap.snd ℝ ℝ C).comp T; let Y:=(ContinuousLinearMap.fst ℝ ℝ C).comp T
  let Q:=ContinuousLinearMap.fst ℝ ℂ (ℝ × C)
  have hf : Function.HasTemperateGrowth f:=by
    have h' := (ContinuousLinearMap.lsmul ℝ ℝ).bilinear_hasTemperateGrowth ((Y.hasTemperateGrowth).sub (Function.HasTemperateGrowth.const 1)) (L.hasTemperateGrowth.comp P.hasTemperateGrowth)
    have h₂ := (ContinuousLinearMap.inr ℝ ℂ C).hasTemperateGrowth.comp ((P.hasTemperateGrowth).add h')
    have h₁ := (ContinuousLinearMap.inl ℝ ℂ C).hasTemperateGrowth.comp Q.hasTemperateGrowth
    convert h₁.add h₂ using 1
    ext1 x; rw [Pi.add_apply]; unfold f
    rw [moving]; change _=(x.1+0,0+_); rw [add_zero,zero_add]; rfl
  have hh : Packet S (stretch p) 1 f := Packet.built hf ?_; swap
  · refine bill_single (C:=max (R+1) 1) (l:=1) (zero_le_one.trans (le_max_right _ _)) fun x hx=> ?_
    obtain ⟨z,t,x⟩:= x; let B := max ‖t‖ ‖x‖; have hb: 0≤B:= (norm_nonneg t).trans (le_max_left ..); change ‖1+ max ‖z‖ B‖≤max _ _ * (1+B)^1
    rw [pow_one,Real.norm_of_nonneg (by positivity)]
    rcases le_total ‖z‖ B with hz|hz
    · rw [max_eq_right hz]; exact le_mul_of_one_le_left (by positivity) (le_max_right ..)
    rw [max_eq_left hz]; refine le_trans (b:=max (R+1) 1) ?_ (le_mul_of_one_le_right (zero_le_one.trans (le_max_right ..)) (by linarith))
    exact le_trans (b:=R+1) (by linarith [(zone_mem z R).mp hx.1]) (le_max_left ..)
  refine ⟨Packet.comp (U:=S) (p:=stretch p) (q:=1) (T:=f) (h.budget n).stream
    (fun i hi => ⟨hi.1,mem_univ _⟩) ?_ (Bills.const _) (by simpa using hh),fun z hz x=>(h.budget n).region z hz _⟩
  have hg : Packet S (stretch p) 1 (fun i=> (f i).2):= hh.apply (X:=ContinuousLinearMap.snd ℝ ℂ C)
  exact (Bills.const 1).add hg.values.norm
end Momentum
end YM.MSbar.Pole
