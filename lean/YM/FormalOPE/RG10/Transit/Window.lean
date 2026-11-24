import YM.FormalOPE.RG10.Transit.Slab

/-!
# On a fixed physical reference measure

Geometry for Spine (arbitrary finite-distance estimates on roots, derivative/membership kept by
users). Step `i+1` to `i`, tape units at i. True whenever structural costs for that window and
that invariant class are provided before transmission, at **every** continuation estimate needed.
Does not replace any pre-*block* parameter by a lighter post-choice through arbitrary steps.
Wrapped/winding kernel paths use real tape hypothesis; no quotient identity asserted.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Transit
open Route PowerSeries Finset Function
open scoped Topology BigOperators Classical
variable {U J : ℕ → Type} {X : Type}

structure Scale (X:Type) (U:ℕ→Type) where
  μ : ℕ → ℝ
  positive t : 0 < μ t
  thick t : 2 * μ (t+1) ≤ μ t
  tape : Tape X
  point : ∀ i,U i → X

namespace Scale
variable (W : Scale X U) {i j : ℕ}
local notation "μ" => W.μ
local notation "T" => W.tape

lemma decrease (h : i ≤ j) : μ j ≤ μ i := by
  induction j,h using Nat.le_induction with
  | base => rfl
  | succ j hk ih => exact le_trans (by linarith [W.thick j,W.positive (j+1)]) ih
lemma decreasing (j) : μ (j+1) ≤ μ j := decrease W (Nat.le_succ j)

def zoom (i:ℕ) : Tape X where
  Δ a b := W.tape.Δ a b / W.μ i
  sign _ _ := div_nonneg (W.tape.sign ..) (W.positive _).le
  paid a := by simp [W.tape.paid]
  swap a b := congr_arg (· / μ i) (W.tape.swap a b)
  train a b c := by rw [← add_div]; exact div_le_div_of_nonneg_right (W.tape.train ..) (W.positive _).le
variable (i)
variable (A E : Lens W.tape)

def localize (i : ℕ) (A : Lens W.tape) : Lens (W.zoom i) where
  m x := A.m x/W.μ i
  sign x := div_nonneg (A.sign x) (W.positive i).le
  path a b := by change A.m a/W.μ i ≤ A.m b/_ + W.tape.Δ b a/_; rw [← add_div]; exact div_le_div_of_nonneg_right (A.path ..) (W.positive i).le

lemma local_mono (h : A.m ≤ E.m) : (W.localize i A).m ≤ (W.localize i E).m := fun a => div_le_div_of_nonneg_right (h a) (W.positive i).le
lemma kept (j : ℕ) (h : i ≤ j) : (W.localize i A).m ≤ (W.localize j A).m := fun a => div_le_div_of_nonneg_left (A.sign a) (W.positive j) (decrease W h)
lemma local_pair {L:ℝ} (h:A.Spaced E L) : (W.localize i A).Spaced (W.localize i E) (L/W.μ i) := by
  intro a b; change L/_ ≤ A.m a/W.μ i+W.tape.Δ a b/_+E.m b/_; rw [← add_div,← add_div]; exact div_le_div_of_nonneg_right (h ..) (W.positive _).le

def eyes (i : ℕ) (A : Lens W.tape) := (W.localize i A).m ∘ W.point i
def value (i n r : ℕ) (A : Lens W.tape) (x : Channel (U i)) := mag (W.eyes i A) n r x
lemma alive : 0 ≤ W.eyes i A := fun _ => (W.localize _ _).sign _
variable (n r : ℕ) (p q : Channel (U i))
lemma nn : 0 ≤ W.value i n r A p := mag_sign _ _ _ (W.alive i A) p
@[simp] lemma zero : W.value i n r A 0=0 := mag_empty ..
@[simp] lemma one : W.value i n r A 1=1 := mag_one ..
lemma sum' {K : Type*} (s : Finset K) (p : K → Channel (U i)) : W.value i n r A (∑ z∈s,p z) ≤ ∑ z∈s,W.value i n r A (p z) :=
    mag_sum _ _ _ (W.alive i A) _ _
lemma add : W.value i n r A (p+q) ≤ W.value i n r A p + W.value i n r A q := mag_add _ _ _ (W.alive i A) _ _
lemma mul : W.value i n r A (p*q) ≤ W.value i n r A p * W.value i n r A q := mag_mul _ _ _ (W.alive i A) _ _
lemma mono (h : A.m ≤ E.m) : W.value i n r A p ≤ W.value i n r E p :=
    w_le _ _ _ _ (W.alive i A) p fun x=>W.local_mono i A E h (W.point i x)
lemma sooner (m : ℕ) (h : n ≤ m) : W.value i n r A p ≤ W.value i m r A p := times_le _ _ _ (W.alive i A) p _ h
lemma shift {K : ℝ} (he : 0 ≤ K) (h : ∀ x,A.m x ≤ K+E.m x) :
    W.value i n r A p ≤ tip (K/W.μ i) n *W.value i n r E p := by
  apply ride _ _ _ (W.alive i A) p (div_nonneg he (W.positive _).le) _ (W.alive i E)
  intro x; unfold eyes localize; rw [comp_apply, comp_apply]; dsimp only
  rw [← add_div]; exact div_le_div_of_nonneg_right (h _) (W.positive i).le
end Scale

variable (V : Voyage U J) (W : Scale X U) [∀ i, Fintype (J i)] [∀ i,Fintype (U i)] [∀ i,DecidableEq (U i)]
    (r d n : ℕ)
namespace Voyage
variable {i j N b : ℕ}

def regular (i : ℕ) (C : ℝ) := (V.sail i).Supply (W.zoom i) (W.point (i+1)) (W.point i) r d n C

variable {C L:ℝ}
variable (A E O : Lens W.tape) (he : O.m ≤ E.m) (ho : O.m ≤ A.m) (hy : A.Spaced E L)

variable {T : ℕ} {M : Channel (U T)}
include he ho hy in
lemma event (h:0 ≤ L) (c: regular V W r d n i C) {P Q : Channel (U (i+1))} (hx:Guard P r d) (hh : Guard Q r d) :
    tip (L/W.μ i) n * W.value i n r O ((V.sail i).error P Q) ≤
      C^Episode.pressure r d * W.value (i+1) (Episode.momentIn r d n) r A P * W.value (i+1) (Episode.momentIn r d n) r E Q := by
  let w := fun A : Lens W.tape => (W.localize i A).m ∘ W.point (i+1)
  have hc : 0 ≤ C := le_trans (by norm_num) c.width.hi
  apply ((V.sail i).experience P (W.point (i+1)) (W.point i) r d n C (W.localize i O) (W.localize i A) (W.localize i E)
    (W.local_mono i O A ho) (W.local_mono i O E he) (div_nonneg h (W.positive i).le) (W.local_pair i A E hy) c Q hx hh).trans
  have h1 (A : Lens W.tape) : w A ≤ W.eyes (i+1) A := fun k=>W.kept i A (i+1) (Nat.le_succ i) (W.point (i+1) k)
  have hh' (A : Lens W.tape) : 0 ≤ w A:= fun _ => (W.localize i _).sign _
  apply mul_le_mul (mul_le_mul_of_nonneg_left (w_le (w A) _ _ _ (hh' _) P (h1 A)) (by positivity))
    (w_le (w E) _ _ _ (hh' _) Q (h1 E)) (mag_sign _ _ _ (hh' _) Q) (mul_nonneg (by positivity) (W.nn ..))
end Voyage
end YM.FormalOPE.RG10.Transit
