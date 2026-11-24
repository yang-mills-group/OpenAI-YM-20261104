import YM.FormalOPE.RG10.Routes.Binary

/-!
# Currency adjustment for iteration

`Wide` needs at most the fixed arity bounds at *this* order. Use always with `K=Fin r` dummy
mark type (containing nothing else); omits all structural hypotheses on the gauges/schemes.
In addition to these arity charges, actual tuning/post-block polynomial uniform bound needed on
post-mean-shift vacuum vertex norms *anchored to any fine fluctuation leg*. This never charges
an unrooted vacuum output.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Route.Binary
open Marker Extra.Trajectories FlatFeed Word Polar PowerSeries Finset Joins Joins.Gauss Function
open MvPolynomial (aeval totalDegree)
open Primitives.GCC Grove
open Multi (parts shards)
open Multi.Vacuum.Gauss (Row)
open scoped Topology BigOperators Classical
variable {I J B K X : Type} [Fintype J] [Fintype K] [DecidableEq K]
variable (q : I → Row J) (P Q V : Channel (I⊕B))
variable {T : Tape X} (p : I ⊕ B → X)
local notation "T₀" => Polar.budget bill K
local notation "TB" => parts T₀
local notation "δ" => posted P Q V
local notation "m" => Fintype.card (Target K)

lemma needs (a : Index I B) : rank a ≤ LocalPolynomial.length a := by
  have h : LocalPolynomial.length a=rank a+LocalPolynomial.length (coarse a) := by
    unfold rank LocalPolynomial.length; nth_rw 1 [sound a]; rw [Finsupp.sum_sumElim]; rfl
  omega -- inspect

def cuts (v : Target K) (i : Bool) := i∈ (Polar.mark v.val).val
lemma in_v (v : Target K) (i) : cuts v i ↔ Sum.inl i∈ v.val.val := by simp [cuts,Polar.mark]

variable (k : Finset K) {s : (Multi.parts (Polar.budget bill K)).Mode} (hs : s∈ shards (Polar.budget bill K) (pay bothMarks k))
include hs
lemma cutting (i) : ∃ p∈s.val,cuts p i := by
  have he := congr_arg Subtype.val (show Multi.unionOf s = pay bothMarks k from (mem_filter.mp hs).2)
  have hi : Sum.inl i∈ (pay bothMarks k).val := by cases i <;> simp [pay,bothMarks]
  rw [← he] at hi; obtain ⟨p,hp,h⟩:= mem_biUnion.mp hi; exact ⟨p,hp,(in_v p _).2 h⟩
omit hs
lemma unique_cut {u v : Target K} {i} (h : u∈s.val) (h' : v∈s.val) (hp : cuts u i) (hq : cuts v i) : u=v := by
  by_contra hb; exact disjoint_left.mp (Multi.parts_wise s h h' hb) ((in_v u i).1 hp) ((in_v v i).1 hq)

lemma mark_near {u : Target K} (h : cuts u false) (h' : ¬ cuts u true) : mark u.val=bill.fire false := by
  apply Subtype.ext; ext b; cases b <;> first | simpa [Census.fire,cuts] using h | simpa [Census.fire,cuts] using h'
lemma mark_far {u : Target K} (h : cuts u true) (h' : ¬ cuts u false) : mark u.val=bill.fire true := by
  apply Subtype.ext; ext b; cases b <;> first | simpa [Census.fire,cuts] using! h | simpa [Census.fire,cuts] using! h'
lemma mark_vac {u : Target K} (h : ¬ cuts u true) (h' : ¬ cuts u false) : mark u.val=bill.quiet:= by
  apply Subtype.ext; ext b; cases b <;> first | simpa [Census.quiet,cuts] using! h | simpa [Census.quiet,cuts] using! h'
lemma mark_both {u : Target K} (h : cuts u true) (h' : cuts u false) : mark u.val=bothMarks:= by
  apply Subtype.ext; ext b; cases b <;> first | simpa [bothMarks,cuts] using! h | simpa [bothMarks,cuts] using! h'
variable (C : ℝ) (d : ℕ) (u : Target K)

/-- Dominates constants of arity formulas at *fixed* coefficient order. Uniform in volume,
post-block scale included in C by events separately. Pin the Mark-to-step expansion algebra, not
assuming true interaction vertex dimension bounded by d at any coefficient until shown.
-/
structure Wide (K : Type) [Fintype K] [DecidableEq K] (C : ℝ) (d : ℕ) : Prop where
  hi : 8 ≤ C
  over : (d:ℝ)+1 ≤ C
  fac_rank : (d.factorial:ℝ) ≤ C
  heat : Real.exp (d/4 : ℝ) ≤ C
  ticket : ((Fintype.card K).factorial:ℝ) ≤ C
  markers : ((Fintype.card (Target K)):ℝ) ≤ C
  trees : ((Fintype.card (Parent (Target K))):ℝ) ≤ C
  mix : ((Fintype.card (Multi.parts (Polar.budget bill K)).Mode):ℝ) ≤ C
lemma exists_wide (K : Type) [Fintype K] [DecidableEq K] (d : ℕ) : ∃ a : ℝ, ∀ b≥a, Wide K b d := by
  simp_rw [show ∀ b, Wide K b d ↔ 8 ≤ b ∧ (d:ℝ)+1≤b ∧ (d.factorial:ℝ)≤b ∧ Real.exp (d/4:ℝ)≤b ∧ ((Fintype.card K).factorial:ℝ)≤b ∧ ((Fintype.card (Target K)):ℝ) ≤ b ∧ ((Fintype.card (Parent (Target K))):ℝ) ≤ b ∧ ((Fintype.card (Multi.parts (Polar.budget bill K)).Mode):ℝ) ≤ b from fun _ => ⟨fun h=> ⟨h.hi,h.over,h.fac_rank,h.heat,h.ticket,h.markers,h.trees,h.mix⟩,fun ⟨a,b,c,e,f,g,y,z⟩=>⟨a,b,c,e,f,g,y,z⟩⟩]
  rw [← Filter.eventually_atTop]
  apply Filter.Eventually.and; exact Filter.eventually_ge_atTop _ -- inspect
  repeat first | apply Filter.Eventually.and | exact Filter.eventually_ge_atTop _
variable (c : Wide K C d)
include c
lemma enough : 1 ≤ C := le_trans (by norm_num) c.hi
lemma rent_admissible {t : ℕ} (ht : t ≤ m) (hp : 0 < t) : rent C d t ≤ C^((1+4*d)*m+1) := by
  have h1 : 0 ≤ C := zero_le_one.trans (enough C d c)
  have hu : (t:ℝ) ≤ C:= (by exact_mod_cast ht : (t:ℝ) ≤ m).trans c.markers
  have hh := (mul_le_mul (mul_le_mul (mul_le_mul c.hi c.over (by positivity) h1) (le_refl C) h1 (by positivity)) hu (by positivity) (by positivity));
  rw [← sq,← pow_succ,← pow_succ] at hh -- inspect
  have he := scale_le (K:=C) d (enough C d c) hp
  apply le_trans (b:= (C^(1+4*d))^t * C) (mul_le_mul (pow_le_pow_left₀ (scale_nn ..) (he.trans ?_) t) c.heat (Real.exp_pos _).le (by positivity))
  · rw [pow_add (n:=1),← pow_mul,pow_one]; gcongr; exact enough C d c
  rw [pow_add,pow_mul,pow_one]; exact mul_le_mul c.fac_rank (pow_le_pow_left₀ (by positivity) hh d) (by positivity) h1
lemma ticket_cost (u : Target K) : ((tickets u.val).card.factorial : ℝ) ≤ C := (by exact_mod_cast (Nat.factorial_le (Finset.card_le_univ (tickets u.val))) : ((tickets u.val).card.factorial:ℝ) ≤ (Fintype.card K).factorial).trans c.ticket -- inspect
omit c
variable [DecidableEq I] (r n : ℕ)

def slim (V : Channel I) (r d : ℕ) := ∀ i ≤ r,totalDegree (coeff i V) ≤ d
def vacuum (T : Tape X) := ∀ i ≤ r,∀ a, pins p T n (coeff i V) a ≤ C
omit [DecidableEq I] in
lemma ink (hp : slim P (Fintype.card K) d) (hq : slim Q (Fintype.card K) d) (hv : slim V (Fintype.card K) d) (a : Index I B)
    (h : a ∈ (δ u).support) : rank a ≤ d := by
  apply (needs a).trans; apply (MvPolynomial.le_totalDegree h).trans; apply (MvPolynomial.totalDegree_smul_le ..).trans
  unfold selectGen; have ht := card_le_univ (tickets u.val); split_ifs <;> first | exact hp _ ht | exact hq _ ht | exact hv _ ht | simp
lemma pins_scale (T : Tape X) (M : Packet (I ⊕ B)) (a : I) (c : ℂ) : pins p T n (c • M) a= ‖c‖*pins p T n M a := by
  unfold pins; by_cases h:c=0
  · simp [h]
  rw [show MvPolynomial.support (c • M) = M.support from ?_, Finset.mul_sum]; swap
  · ext; simp [MvPolynomial.mem_support_iff,h]
  refine sum_congr rfl fun i _ => ?_; rw [MvPolynomial.coeff_smul,norm_smul]; ring
end YM.FormalOPE.RG10.Route.Binary
