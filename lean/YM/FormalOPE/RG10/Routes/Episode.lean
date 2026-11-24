import YM.FormalOPE.RG10.Routes.Summed
import YM.FormalOPE.RG10.Routes.Stretch

/-!
# Episode (one formal step at given ratio)

Implement with deterministic kernel, noise (cover), actual single variable g at chosen step or
formal common-window expansion parameter; no implicit extra readout-scale conversion. Apply using

* `I` full incoming potential coordinates (can include fine tree slice and impose zero on
constrained variables), `w i` the recenter/reexpress map `ξ_i + Σ B_j (g_coarse/g_fine....) A_tr..`
with the same projection/covariance and endpoint shift computed by the producer. Directions need
not be independent. Only polynomial formal setting.
* `joint` on I as real covariance rows, all contribution legs before norm tested there, coherent
with w and `vertices` explicitly *required from the construction* not solved by invoking any
consumer here.
* `vertices` higher vacuum terms as in `Channel.intake`; V INCLUDES all terms
`+` sign in weight (negative action terms with their signs), `Q` is not a field source. Stencil
chosen consistently before packing. The input `Episode` is mathematical data to be built explicitly
from that Wilson germ with those properties each time it's used.

Estimate has no multiplicative-through-many-step loss asserted at this point. Compute Taylor rows
independently with fixed order. `projective` consistency required with all MarkedSeries inputs.
There is no requirement of nonzero outputs in order ≥1 from each episode, but the bound is on
*whole* formal discrepancy allowing every such coefficient. For the forecast norm, locations at
fine and coarse coincide with assigned tape; no physical Jacobian or mesh changes implicit.
Analytic reserves at each order repeated require new sum budget only when a *join* happens.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Route
open PowerSeries Finset Function Binary
open Multi.Vacuum.Gauss (Row)
open scoped Topology BigOperators Classical
variable {I B J X : Type}

structure Episode (I B J:Type) where
  spur : I→Channel (I⊕B)
  joint : I→Row J
  vertices : Channel (I ⊕ B)
  law : PowerSeries.coeff 0 vertices = 0

namespace Episode
variable [Fintype J] (e : Episode I B J) (p : Channel I)

def floats : Channel I →+ Channel B where
  toFun p := Bulk.transfer e.joint (replot e.spur p) e.vertices
  map_add' p q := by rw [map_add]; exact Bulk.transfer_add _ _ _ e.law _
  map_zero' := by
    rw [map_zero]; have H := Bulk.transfer_add e.joint 0 _ e.law 0; rw [zero_add] at H
    exact add_left_cancel (H.symm.trans (Eq.symm (add_zero _)))

@[simp] lemma float_one : e.floats 1=1 := by
  change Bulk.transfer e.joint ((replot e.spur) 1) e.vertices = 1; rw [map_one,Bulk.transfer,mul_one,← show Bulk.income e.joint e.vertices=Bulk.move e.joint (advance e.vertices) from rfl,PowerSeries.mul_invOfUnit]
  exact (coeff_zero_eq_constantCoeff_apply _).symm.trans (Bulk.accounting ..)

/-- Fundamental binary disagreement (in Channel B). -/
def error (m n:Channel I) := e.floats (m*n)-e.floats m*e.floats n
lemma effect (p q : Channel I) : e.error p q= disagreement e.joint (replot e.spur p) (replot e.spur q) e.vertices := by
  unfold disagreement error floats; simp [map_mul]

local notation "δ" => Binary.Target
variable (S: Tape X) (x : I→X) (y:B→X)
variable (r d n : ℕ)
local notation "D" => d+3*r
local notation "P₀" => Sum.elim x y
structure Eligible (e : Episode I B J) (r:ℕ) : Prop where
  rank : Guard e.vertices r 0
  spur : ∀ i, Guard (e.spur i) r 1
lemma Eligible.forward (E:e.Eligible r) {p : Channel I} (h : Guard p r d) : Guard (e.floats p) r d := Guard.transmitted _ _ _ E.rank (Guard.prep h e.spur E.spur) -- inspect

variable (C:ℝ) [DecidableEq I] [Fintype I]
structure Supply (e : Episode I B J) (S : Tape X) (x : I → X) (y : B → X) (r d n : ℕ) (C : ℝ) : Prop extends e.Eligible r where -- syntax
  width : Wide (Fin r) C (d+3*r)
  order : (r:ℝ)+1 ≤ C
  fee : vacuum e.vertices (Sum.elim x y) C r (n+n) S
  covariance : schur (Sum.elim x y) e.joint S (n+n) C
  shifts : stencilCost x (Sum.elim x y) e.spur (n+n) r C S

-- moment and coupling exponents used in expansive one-time cost

def momentIn (r d n : ℕ) := (n+n)*(d+3*r)
def pressure (r d : ℕ) := burnAll (d+3*r) (Fintype.card (δ (Fin r))) + (d+3*r)+(d+3*r) + 1

variable {S}
variable (O A E : Lens S) (ha : O.m ≤ A.m) (he : O.m ≤ E.m) {L:ℝ} (hr : 0 ≤ L) (hw : A.Spaced E L)
    (c : e.Supply S x y r d n C) (q : Channel I) (hp : Guard p r d) (hq : Guard q r d)
include ha he hr hw c hp hq in
/-- Event estimate for use inside iteration. `momentIn` on marked inputs, twice output moment
on vacuum and row operations. Triangle power suppression between profile sets. -/
theorem experience : tip L n * mag (O.m ∘ y) n r (e.error p q) ≤
    C^pressure r d * mag (A.m ∘ x) (momentIn r d n) r p * mag (E.m ∘ x) (momentIn r d n) r q := by
  let U:=mag (A.m ∘ x) (momentIn r d n) r p; let W:=mag (E.m ∘ x) (momentIn r d n) r q
  let P:=replot e.spur p; let Q:=replot e.spur q
  have h' : 1 ≤ C := enough _ _ c.width; have hC : 0≤C := zero_le_one.trans h'
  have hU : 0 ≤ U := mag_sign _ _ _ (fun i => A.sign (x i)) p; have hE : 0 ≤ W := mag_sign _ _ _ (fun i => E.sign (x i)) q
  let m := Fintype.card (Target (Fin r))
  let Y:= C^burnAll D m*(C^D*U)*(C^D*W)
  have hY : 0 ≤ Y := by unfold Y; positivity
  change _ ≤ C^pressure r d *U*W; rw [mag,Finset.mul_sum]
  refine le_trans (b:=∑ _∈range (r+1),Y) (sum_le_sum fun i hi => ?_) ?_
  · have hi': i≤r:= Nat.le_of_lt_succ (mem_range.mp hi)
    obtain ⟨k,hk,hj⟩:= Finset.exists_subset_card_eq (show i ≤ (univ (α:=Fin r)).card by simpa using hi')
    have uP : ∀ i≤r,worth (A.m ∘ P₀) (n+n) (coeff i P) ≤ C^D*U := by
      intro i hi; apply (current _ _ _ (fun t => A.sign (P₀ t)) _ i hi).trans
      exact transported x P₀ e.spur A (n+n) r C h' c.shifts p _ hp.slim
    have uQ : ∀ i≤r,worth (E.m ∘ P₀) (n+n) (coeff i Q) ≤ C^D*W := by
      intro i hi; apply (current _ _ _ (fun t => E.sign (P₀ t)) _ i hi).trans
      exact transported x P₀ e.spur E (n+n) r C h' c.shifts q _ hq.slim
    have hV: slim e.vertices r D := ((Guard.mono c.rank (Nat.zero_le d))).slim
    rw [effect,← hj]
    exact summer e.joint P Q e.vertices P₀ A E O hr hw ha he D n c.width (C^D*U) (C^D*W) (by positivity) (by positivity) (by simpa using (Guard.prep hp _ c.spur).slim)
       (by simpa using (Guard.prep hq _ c.spur).slim) (by simpa using hV) (by simpa using uP) (by simpa using uQ) (by simpa using c.fee) c.covariance k e.law
  rw [sum_const,nsmul_eq_mul,card_range];
  apply (mul_le_mul_of_nonneg_right (Nat.cast_add_one (R:=ℝ) r ▸ c.order) hY).trans; apply le_of_eq; unfold Y pressure; unfold m; simp only [pow_add]; ring -- inspect
end Episode
end YM.FormalOPE.RG10.Route
