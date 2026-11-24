import YM.FormalOPE.RG10.HStein.Sense
import YM.FormalOPE.RG10.Transit.Window
/-! # First consumer for Stein.Boot weights. Polynomial costs only once paid. Next matched-rank sector separate. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.HStein
open Route Route.Bulk Roads PowerSeries Function Topology Tier
open scoped Topology BigOperators Classical
variable {I B J Y:Type} {T:Tape Y} [Fintype I] [DecidableEq I] [Fintype J]
variable {p:I→Y} {q:B→Y} (O:Lens T) {k l n d:ℕ}
variable {e:Episode I B J} {M:ℝ}
local notation "P"=> Sum.elim p q
-- to prove smaller moment; pol n+n
variable (h : e.Supply T p q k d n M)
namespace Driven
include h
lemma demand (hn:l≤n+n): Rails e.joint e.vertices k P T (pol l) M := (stem h.covariance h.fee).order (fun _ hx=> tip_mono_age hx hn)
lemma road (hn:l≤n+n): Along T p P (pol l) k e.spur M:= by
 intro i; rw [gain_classical _ (fun a=> T.sign (p i) (P a))]; exact le_trans (times_le _ l k (fun a=>T.sign (p i) (P a)) _ _ hn) (h.shifts i)
include O
lemma prepared (P₁:Channel I)(hP:Guard P₁ k d) (hn:l≤n+n): mag (O.m ∘ q) l k (e.floats P₁)≤ M^expansive d k * mag (O.m ∘ p) l k P₁ := by
 rw [← gain_classical (O.m ∘ q) (fun i => O.sign (q i)),← gain_classical (O.m ∘ p) (fun i => O.sign (p i))]
 apply rough O (demand h hn) h.toEligible (road h hn) (le_trans (by norm_num) h.width.hi) h.order ?_ P₁ hP
 have h' := h.width.over; push_cast at h'; linarith
end Driven
open Driven Transit
variable {U J' : ℕ → Type} (V : Voyage U J') (W : Scale Y U) [∀ i,Fintype (U i)] [∀ i,DecidableEq (U i)] [∀ i, Fintype (J' i)]
theorem summoned {i} (O:Lens W.tape) (h:V.regular W k d n i M)(hn: l≤n+n)(P₁: Channel (U (i+1)))(hP:Guard P₁ k d) : W.value i l k O ((V.sail i).floats P₁) ≤ M^expansive d k * W.value (i+1) l k O P₁:= by
 apply le_trans (prepared (W.localize i O) h P₁ hP hn)
 apply mul_le_mul_of_nonneg_left (w_le _ _ _ _ (fun j=> (W.localize i _).sign _) _ ?_) (pow_nonneg (le_trans (by norm_num) h.width.hi) _)
 exact fun x=> W.kept i O _ (Nat.le_succ _) _
end YM.FormalOPE.RG10.HStein
