import YM.Primitives.CONNECTED_GAUSSIAN_CUMULANTS.Price

/-!
# Positions in coarse units and rooted polynomial costs

SUM against a region not a point (the union profile/support version), allowed bounds in supremum
of this `lens`. Does not charge diameter of the whole cluster. Use point and simplex cases too.
All endpoints (including any outgoing legs) located in this geometry before one increment. No
change of lattice units without supplying the rescaled distance rule equations. Does not inherit
any volume/scale-independent constants from unrelated algorithms.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Route
open Finset Function
open scoped Topology BigOperators Classical
variable {X I : Type*}

/-- Explicit distance in the *current operation's* canonical coordinates. Useful also when
using `dist / δ`. Include lattice, midpoint-grid, continuum coordinate versions by adapting
triangle inequalities accordingly. -/
structure Tape (X : Type*) where
  Δ : X → X → ℝ
  sign a b : 0 ≤ Δ a b
  paid a : Δ a a = 0
  swap a b : Δ a b=Δ b a
  train a b c : Δ a c ≤ Δ a b + Δ b c

/-- Use e.g. distance to a ball of profile points. Permit multipart regions without cost of
internal diameter. -/
structure Lens {X : Type*} (T : Tape X) where
  m : X → ℝ
  sign a : 0 ≤ m a
  path a b : m a ≤ m b + T.Δ b a

namespace Tape
variable (T : Tape X)

def weighted [PseudoMetricSpace X] : Tape X where
  Δ := dist
  sign _ _ := dist_nonneg
  paid := dist_self
  swap := dist_comm
  train := dist_triangle

def sphere (x : X) (r : ℝ) : Lens T where
  m y := max 0 (T.Δ x y-r)
  sign y := le_max_left ..
  path a b := max_le (add_nonneg (le_max_left ..) (T.sign ..)) (by linarith [T.train x b a, le_max_right (0:ℝ) (T.Δ x b-r)])
/-- Lens with no position cost. -/
def nowhere : Lens T where
  m := 0
  sign _ := le_rfl
  path _ _ := le_add_of_nonneg_right (T.sign ..)
end Tape
namespace Lens
variable {T : Tape X} (A B : Lens T)

def either : Lens T where
  m y := min (A.m y) (B.m y)
  sign y := le_min (A.sign y) (B.sign y)
  path a b := by rw [← min_add_add_right]; exact min_le_min (A.path ..) (B.path ..)

lemma le_left (x : X) : (A.either B).m x ≤ A.m x := min_le_left ..
lemma le_right (x : X) : (A.either B).m x ≤ B.m x := min_le_right ..

def Spaced (L : ℝ) := ∀ a b : X, L ≤ A.m a + T.Δ a b + B.m b
lemma Spaced.never : A.Spaced B 0 := fun _ _ => add_nonneg (add_nonneg (A.sign _) (T.sign ..)) (B.sign _)
lemma Spaced.swap {L : ℝ} (h : A.Spaced B L) : B.Spaced A L := by intro a b; rw [T.swap]; linarith [h b a]
lemma Spaced.sphere (v w : X) (r s : ℝ) : Spaced (T.sphere v r) (T.sphere w s) (T.Δ v w-r-s) := by
  intro a b
  have hv : T.Δ v a-r ≤ (T.sphere v r).m a := le_max_right ..
  have hw : T.Δ w b-s ≤ (T.sphere w s).m b := le_max_right ..
  linarith [T.train v a w,T.train a b w,T.swap w b]
lemma Spaced.combine {C : Lens T} {r} (h : A.Spaced C r) (h' : B.Spaced C r) : (A.either B).Spaced C r := by
  intro a b; change r ≤ min _ _ + _ + _; rw [← min_add_add_right,← min_add_add_right]; exact le_min (h ..) (h' ..)
end Lens
/-- Sup over legs; empty list costs zero. -/
def along (m : I → ℝ) (s : Finset I) := if h:s.Nonempty then s.sup' h m else 0
lemma along_nn {m : I → ℝ} (h : ∀ i, 0 ≤ m i) (s : Finset I) : 0 ≤ along m s := by
  unfold along; split
  · rename_i hp; obtain ⟨j,hj⟩:=hp; exact (h j).trans (le_sup' _ hj)
  exact le_rfl
lemma along_le (m : I → ℝ) (s : Finset I) {K : ℝ} (h : 0 ≤ K) (he : ∀ i∈s,m i≤K) : along m s ≤ K := by
  unfold along; split
  · exact sup'_le _ _ he
  exact h
lemma le_along {i : I} {s : Finset I} (h : i∈s) (m : I → ℝ) : m i ≤ along m s := by
  rw [along,dif_pos ⟨i,h⟩]; exact le_sup' m h
lemma mono_along {s t : Finset I} (h : s⊆t) (m n : I → ℝ) (he : ∀ i∈s,m i ≤ n i) (ht : ∀ i,0 ≤ n i) :
    along m s ≤ along n t := along_le m s (along_nn ht t) fun i hi => (he i hi).trans (le_along (h hi) _)
@[simp] lemma along_empty (m : I → ℝ) : along m ∅=0 := dif_neg Finset.not_nonempty_empty
@[simp] lemma along_single (m : I → ℝ) (i:I): along m {i}=m i := by rw [along,dif_pos ⟨i,mem_singleton_self _⟩, sup'_singleton];

def tip (x : ℝ) (u : ℕ) := (1+x)^u
lemma tip_pos {x : ℝ} (h : 0 ≤ x) (u : ℕ) : 0 < tip x u := pow_pos (by linarith) _
lemma tip_charge {x : ℝ} (h : 0 ≤ x) (u : ℕ) : 1 ≤ tip x u := one_le_pow₀ (by linarith)
lemma tip_mono {x y : ℝ} (h : x ≤ y) (h' : 0 ≤ x) (u : ℕ) : tip x u ≤ tip y u := pow_le_pow_left₀ (by linarith) (by linarith) _
lemma tip_mono_age {x : ℝ} (h : 0 ≤ x) {a b : ℕ} (h' : a ≤ b) : tip x a ≤ tip x b := pow_le_pow_right₀ (by linarith) h'
lemma tip_add {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (u) : tip (x+y) u ≤ tip x u * tip y u := by
  unfold tip; rw [← mul_pow]; exact pow_le_pow_left₀ (by linarith) (by nlinarith) _
@[simp] lemma tip_zero (u) : tip 0 u=1 := by simp [tip]
end YM.FormalOPE.RG10.Route
