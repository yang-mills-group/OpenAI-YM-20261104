import YM.FormalOPE.RG10.Wing.Spoon
/-! # Topologically nilpotent at every gauge perturbation order; Rank at each grade finite. Not claiming convergence nor top-degree ghosts. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Wing
open Function PowerSeries Finset HStein Route Cycle
open scoped Topology BigOperators Classical
variable {X : Type} [Fintype X]
local notation "Q"=> Packet X
local notation "W"=> Channel X
variable {i j k d:ℕ} (u:X→ Channel X) (P:Channel X)
local notation "β"=> down u 0

def steadyDown (u:X→Channel X): Prop:= ∀ i,down u 0 (PowerSeries.coeff 0 (u i))=0
variable (h : steadyDown u)
local notation "E"=> numeral (down u 0)
local notation "A"=> powers (down u 0)
include h
lemma off (i:X): E 2 (MvPolynomial.X i)=0 := (alive ..).mpr (by change Cycle.powers (down u 0) (1+1) (MvPolynomial.X i)=_; rw [newDay,show 1=0+1 from rfl,newDay,steady,down_axis]; exact h i)
local notation "l"=> Primitives.GCC.LocalPolynomial.length
lemma smoke (m:Letters X): E (l m+1) (glyph m)=0:= by
 obtain hp|hp:=eq_empty_or_nonempty m.support
 · rw [Finsupp.support_eq_empty.mp hp, show glyph (0 : Letters X)=1 from rfl]; apply (alive ..).mpr; change A (0+1) _=_; rw [newDay,steady, Derivation.map_one_eq_zero]
 obtain ⟨a,ha⟩:= hp
 let w:=m-Finsupp.single a 1; have he : m=w+Finsupp.single a 1:= (Finsupp.sub_add_single_one_cancel (Finsupp.mem_support_iff.mp ha)).symm
 have hu : l w+1=l m:= distill ha
 nth_rw 2 [he]; rw [← comma,call]; exact void _ _ _ (l w) 1 (l m+1) (smoke w) (off u h a) (by omega)
termination_by l m
decreasing_by have hj:= distill ha;omega
lemma bottom (p : Packet X)(hx:p.totalDegree ≤ d)(he:d < i) : A i p=0:= (alive ..).mp (by
 rw [resolves p,map_sum]; apply sum_eq_zero; intro m hm; have hu := (show l m≤ p.totalDegree from MvPolynomial.le_totalDegree hm).trans hx; rw [map_smul,Cycle.busy _ _ (smoke u h m) (show l m+1 ≤ i by omega), smul_zero])
omit h
-- once erased at all prior grades,
local notation "D"=> kick u
local notation "♯"=> powers (kick u)
def behind (P:Channel X)(k:ℕ) : Prop:= ∀ i<k,coeff i P=0
omit [Fintype X] in
lemma quiet_eq : Through k P 0 ↔ behind P (k+1):= ⟨fun h i hi=> (h i (by omega)).trans (map_zero _),fun h i hi=> (h i (by omega)).trans (map_zero _).symm⟩
variable (he:behind P k)
include he
lemma stayed : behind (D P) k:= by intro i hi; rw [leftQuiet u P i (fun j hj=> he _ (lt_trans hj hi)), he i hi,map_zero]
lemma staying : behind (♯ i P) k:= by induction i with | zero=>exact he | succ i ih=> rw [newDay]; exact stayed u _ ih -- leading ∆ acts
lemma propped : coeff k (♯ i P)= A i (coeff k P):= by
 induction i with
 | zero=> rfl
 | succ i ih => rw [newDay,leftQuiet u _ k (staying u P he),ih,newDay]
local notation "U"=> (d+3*k+1)
omit he
include h
variable (S : Guard P k d) (H: ∀ i,Guard (u i) k 1)
include H S
lemma leaning (hi:i≤k+1) : behind (♯ ((d+3*k+1)*i) P) i:= by
 induction i with
 | zero=> intro x hx; omega
 | succ i ih=>
   let p := ♯ (U*i) P; have he:i≤ k:= by omega
   have hz:behind p i:= ih (Nat.le_trans he (Nat.le_succ k))
   have ht : MvPolynomial.totalDegree (coeff i p)≤ d+3*k:= le_trans (closed_powers u P H d S (U*i) i he) (by omega) -- totalDegree notation
   have hu : behind (♯ U p) (i+1):= by
      intro x hx; obtain hh|hh:=lt_or_eq_of_le (show x ≤ i by omega); · exact staying u p hz _ hh
      subst x; rw [propped u p hz,bottom u h _ ht (by omega)]
   rw [Nat.mul_succ, Nat.add_comm (U*i) U, Cycle.powers,pow_add]; exact hu

def cycle (d k:ℕ) := (d+3*k+1)*(k+1)
lemma shutdown : Through k (numeral (kick u) (cycle d k) P) 0 := by intro i hi; unfold numeral cycle; rw [LinearMap.smul_apply, coeff_smul,leaning u P h S H (le_refl _) i (show i<k+1 by omega),smul_zero,map_zero]; -- maybe params behind
end YM.FormalOPE.RG10.Wing
