import YM.AllOrder.Plateau.Minutes
import YM.AllOrder.Floe.Circle
import YM.Next.SCHEDULE.TensorCost
/-!
# Geometry for real rendered fields at a mesh. Vacuum only now.

Preserve exactly the charge (zeroth mom), taking short, compact reps with
explicit paths. Difference from the designated unmasked offer is exponentially
small in physical ordinary norms.Q.Count.M.L.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Till
open Lattice Laurent RG Gauge Filter Tree Metric Finset Bloch
open Push.Uniform Precision Bid Wilson Push Exterior Pressure Function Matrix
open Extra.Iteration Push.AbsoluteSums Plateau
open scoped BigOperators Topology Classical ContDiff
variable {G:Gauge} {k w:ℕ} {n : Side}
local notation "T" => RG.Atom G k
variable (s:ℕ→Atom G k)
def simply (u:T):T where
 leg i:= ⟨[],(u.leg i).plaq⟩
 coeff:=u.coeff
lemma simply_length (u:T): (simply u).length=4*k:= by simp [Atom.length,simply,Slot.length,Nat.mul_comm]
lemma enough_length (u:T):4*k≤u.length:= by rw [← simply_length u]; unfold Atom.length; refine sum_le_sum fun i _=>?_ ; unfold simply; dsimp only [Slot.length,List.length_nil]; omega
-- long legs BOTH reloc all ranks. radar power works via Γ either, simpler
noncomputable def scheme (w:ℕ)(u:T):T:=if u.length≤w then u else simply u
lemma window_cost (w:ℕ)(v:T)(h:4*k≤ w): (scheme w v).length ≤ w:= by unfold scheme; split; assumption; rw [simply_length]; exact h
lemma scheme_of_fits (w:ℕ)(v:T)(h:v.length ≤ w): scheme w v=v:= by rw [scheme,if_pos h]
lemma scheme_lines (w:ℕ)(v:T): (scheme w v).coeff=v.coeff:= by unfold scheme; split <;> rfl
lemma scheme_sym(w:ℕ)(v:T)(h:v.Invariant):(scheme w v).Invariant:= by unfold scheme; split <;> exact h
lemma scheme_mono (w:ℕ){t:ℝ}(h:0<t)(u:T):(scheme w u).budget t≤ u.budget t:= by
 unfold scheme; split; exact le_rfl; unfold Atom.budget; rw [simply_length]; change u.magnitude*_≤_; gcongr; · unfold Atom.magnitude; positivity
 exact enough_length u
variable {a b c t:ℝ} (h:Charged s a c)(hp:0<a)
include h hp
abbrev legible(w:ℕ):= scheme w ∘ s
lemma leg_pays(w:ℕ): Charged (legible s w) a c:= budget_mono h (fun i=> paid_nonneg ..) (fun i=> scheme_mono w hp _)
open Floe
lemma action_slips (w:ℕ): ∃ (X Y:ℕ→Atom G k),
    (∀ (n:Side)(U:Config G n), Extra.Iteration.action s U- Extra.Iteration.action (legible s w) U=Extra.Iteration.action X U- Extra.Iteration.action Y U) ∧ Charged X (a/2) (Real.exp (-(a/2)*w)*c)∧Charged Y (a/2) (Real.exp (-(a/2)*w)*c):= by
 let t:= a/2; let X:= Plateau.leaf w ∘ s; let Y:= legible X w; have ht:0<t:=half_pos hp
 let hX:= Plateau.release s hp h w; refine ⟨X,Y,?_, hX, leg_pays X hX ht _⟩
 intro n v
 have hh (U:Config G n) (x:Site n) : (∑' i,(s i).unmasked U x)-(∑' i,(legible s w i).unmasked U x)=(∑' i,(X i).unmasked U x)-(∑' i,(Y i).unmasked U x):= by
    rw [← Summable.tsum_sub (summation s hp h U x) (summation (legible s w) hp (leg_pays s h hp _) U x), ←Summable.tsum_sub (summation X ht hX U x) (summation Y ht (leg_pays X hX ht _) U x)]; apply tsum_congr; intro i; unfold legible Y X; simp only [Function.comp_apply]; unfold Plateau.leaf; split
    next hi=>rw [scheme_of_fits _ (s i) hi, scheme_of_fits _ (mute (s i)) hi]; simp
    next hi=> rfl
 unfold Extra.Iteration.action Patch.average uncut; rw [← mul_sub,← mul_sub]; apply congr_arg; rw [← Finset.sum_sub_distrib,← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro i _; rw [← Finset.sum_sub_distrib,← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun i _=>hh ..
end YM.AllOrder.Till
