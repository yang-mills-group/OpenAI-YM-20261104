import YM.MS.JetBound
import YM.MS.CostVertex
import YM.MS.LandauCost
/-! Kernel recursion for bulk and one-mark (anchored, both readings can also
  use a translation-total tester). Price tests are on derivative scale t=log R,
  not on the integrated vertex. The lattice LPT and $̅MS prescription produce
  data with this flow; nothing here assumes they give equivalent vertices or
  readings. Natural order includes zero unmarked interaction (not occupied).
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Plane
open Function Filter Set Koszul MeasureTheory Wire Flux Real
open scoped Topology ContDiff
variable {ι A P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
   [MeasurableSpace P] [BorelSpace P] [FiniteDimensional ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E]
   [Fintype A] {p : Sector A}
abbrev Target (A P : Type) (t : Type):= ℕ → t → Row A P ℂ
abbrev Clock (ι : Type) := ι × ℝ

structure Domain (p : Sector A) (P : Type) [MeasurableSpace P] where
   meter : ℝ → Flux A P ℂ -- log-length multiplier
   measure : Measure P
namespace Domain
variable {X : Domain p P}
def paths (n d : ℕ) : Finset ℕ := Finset.Ico d n -- k from d..n-1. use as anchor order
def using_tree (X : Domain p P) (c d : ℕ) (C : ℂ) (g f : ℕ → Row A P ℂ) (t : ℝ) (K : ℝ → Flux A P ℂ := X.meter) : Row A P ℂ :=
   C • ∑ k ∈ paths c d, tree p (K t) (g (c-k)) (f k)
-- optional args note X.meter not reducible? order name length d ignored

def recu (X : Domain p P) (d : ℕ) (C : ℂ) (g f : Target A P (Clock ι)) (k : ℕ) (t : Clock ι) : Row A P ℂ := cycle (X.meter t.2) X.measure (f k t) + X.using_tree k d C (fun j=>g j t) (fun j=>f j t) t.2

def tape (f : Clock ι→Row A P ℂ) (w : Wire A E P) (i:ι) (t : ℝ) : E →ℂ := Chart f w (i,t)
-- Use all t; no gauge fixing formula is an assumption of the flow. Smooth growth
-- on each fixed scale horizon for the kernels, with all these chart derivatives.
def Track (b : Bool) (f g : Clock ι → Row A P ℂ) (w : Wire A E P) :=
   Course b w → (∀ (t : Clock ι), ContDiff ℝ ∞ (Chart f w t)) ∧ (∀ (t : Clock ι), ContDiff ℝ ∞ (Chart g w t)) ∧ (∀ (i : ι) t x (j:ℕ),
     HasDerivAt (fun u=> iteratedFDeriv ℝ j (tape f w i u) x) (iteratedFDeriv ℝ j (tape g w i t) x) t)

abbrev Used (b : Bool) (w : Wire A E P) := b=true → 0 < w.length -- only ignore bulk vacuum; for single total tester `b` can still be true, need use rank count with spur

def Flow (X : Domain p P) (b : Bool) (d : ℕ) (C : ℂ) (g f : Target A P (Clock ι)) := ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E], ∀ (w : Wire A E P) (k : ℕ), d ≤ k → Used b w → Track b (f k) (X.recu d C g f k) w
end Domain

open LogTime LogTime.IntervalFamily
variable (R : LogTime.IntervalFamily ι)
def lane (f : Clock ι → Row A P ℂ) (u : R.Inst) := f (index u,t u)
def rate (a : ℝ) (u : R.Inst) := exp (-a*t u)
def herecost (f : Clock ι → Row A P ℂ) (w : Wire A E P) (h : ℤ) (m : A→ℤ):= Virt R.primary (lane R f) w h m

section
open Domain
variable {b : Bool} (X Y : Domain p P) {h : ℤ} {w : Wire A E P} {a : R.Inst → ℝ} {m : A → ℤ}
   {G F L Q : Target A P (Clock ι)}
omit [MeasurableSpace P] [BorelSpace P] [FiniteDimensional ℝ P] [Fintype A] in
lemma along_tape {F H P' Q' : Clock ι → Row A P ℂ}
    (hf : Track b F H w) (hg : Track b P' Q' w) (hv : Course b w) : ∀ j, R.Along (tape (F-P') w) (tape (H-Q') w) j := by
  intro j i t ht p
  have H1 := (((hf hv).2.2 i t p j).sub ((hg hv).2.2 i t p j))
  apply HasDerivAt.hasDerivWithinAt
  convert! H1 using 1
  · funext u; rw [show tape (F-P') w i u=tape F w i u-tape P' w i u from rfl]; exact congr_fun (iteratedFDeriv_sub (((hf hv).1 (i,u)).of_le (by exact_mod_cast le_top)) (((hg hv).1 (i,u)).of_le (by exact_mod_cast le_top))) p
  rw [show tape (H-Q') w i t=tape H w i t-tape Q' w i t from rfl]; exact congr_fun (iteratedFDeriv_sub (((hf hv).2.1 (i,t)).of_le (by exact_mod_cast le_top)) (((hg hv).2.1 (i,t)).of_le (by exact_mod_cast le_top))) p

omit [FiniteDimensional ℝ P] [BorelSpace P] [MeasurableSpace P] [Fintype A] in
lemma Light.add {r u v l : Pool ι A P} {a : ι → ℝ} {S : Scale ι} (hh : Light S a m r u w h) (hg : Light S a m v l w h) : Light S a m (r+v) (u+l) w h := Like.add hh hg
omit [FiniteDimensional ℝ P] [BorelSpace P] [MeasurableSpace P] [Fintype A] in
lemma Light.scalar {r u : Pool ι A P} {a : ι→ℝ} {S : Scale ι} (hh : Light S a m r u w h) (c:ℂ) : Light S a m (c • r) (c • u) w h := Like.L hh (ContinuousLinearMap.mul ℝ ℂ c)
omit [FiniteDimensional ℝ P] [BorelSpace P] [MeasurableSpace P] [Fintype A] in
lemma Light.sum_entries {a : ι→ℝ} {S : Scale ι} (ha : ∀ i, 0 ≤ a i) {r u : ℕ → Pool ι A P} (K : Finset ℕ) (hh : ∀ n∈K, Light S a m (r n) (u n) w h) : Light S a m (fun i=>∑ n∈K,r n i) (fun i=>∑ n∈K,u n i) w h := by
   classical
   unfold Light Chart; simp_rw [Finset.sum_apply]; exact Like.sum hh (fun i p hp=> zpow_nonneg (S.pos _).le _) ha

variable (D : Set P)
    (hy : X.measure= Y.measure.restrict D) (hd : MeasurableSet D) (hD : ∀ p : P, p ∉ D → 1≤‖p‖)
    (j :ℕ) (ha : ∀ u, (R.primary.length u ^ j)⁻¹ ≤ a u)
include ha
omit [BorelSpace P] [FiniteDimensional ℝ P] in
lemma use_cost {h : ℤ} (e : ℤ) (TX TY : ℝ→ Flux A P ℂ)
    (hx : Meter m a R.primary (fun u=>TX (t u)) (fun u=>TY (t u)) (fun _=> D) e) (n d : ℕ) (C : ℂ)
    (hw : Course b w) (FG : ∀ i∈paths n d, ∀ r, Match R.primary true (lane R (G (n-i))) (lane R (L (n-i))) 4 a m (r+1))
    (H : ∀ i∈paths n d, ∀ r, Match R.primary b (lane R (F i)) (lane R (Q i)) h a m (r+1)) :
    Light R.primary a m
       (lane R fun u=> using_tree X n d C (fun i=> G i u) (fun i=> F i u) u.2 TX)
       (lane R fun u=> using_tree Y n d C (fun i=> L i u) (fun i=> Q i u) u.2 TY) w (4+h-e) := by
   have ht i : 0 ≤ a i := (inv_nonneg.mpr (pow_nonneg (R.primary.pos i).le j)).trans (ha i)
   exact (Light.sum_entries (r:=fun i u=> tree p (TX (t u)) (lane R (G (n-i)) u) (lane R (F i) u)) (u:=fun i u=> tree p (TY (t u)) (lane R (L (n-i)) u) (lane R (Q i) u)) ht (paths n d) (fun i hi=> dot_line_tree hx ht hw (fun j _=>FG i hi j) (fun j _=> H i hi j))).scalar C

include hy hd hD
lemma recu_cost [Y.measure.IsAddHaarMeasure] (hm : Module.finrank ℝ P=4) {e : ℤ}
    (hx : Meter m a R.primary (fun u=>X.meter (t u)) (fun u=> Y.meter (t u)) (fun _=> D) e) (n d : ℕ) (C : ℂ)
    (hw : Course b w) (HO : Match R.primary b (lane R (F n)) (lane R (Q n)) h a m (w.length+2))
    (FG : ∀ i∈paths n d, ∀ r, Match R.primary true (lane R (G (n-i))) (lane R (L (n-i))) 4 a m (r+1))
    (H : ∀ i∈paths n d, ∀ r, Match R.primary b (lane R (F i)) (lane R (Q i)) h a m (r+1)) : Light R.primary a m
    (lane R (X.recu d C G F n)) (lane R (Y.recu d C L Q n)) w (4+h-e):= by
   let A := fun u => cycle (X.meter (t u)) X.measure (lane R (F n) u); let B := fun u=> cycle (Y.meter (t u)) Y.measure (lane R (Q n) u)
   have L0 : Light R.primary a m A B w (4+h-e) := by
      dsimp only [A,B]; rw [hy]; convert! dot_line_cycle hx j ha (fun _=>hD) hw HO Y.measure (fun _=>hd) using 1; rw [hm]; omega
   exact L0.add (use_cost R X Y D j ha e X.meter Y.meter hx n d C hw FG H)
end
end YM.MS.Plane
