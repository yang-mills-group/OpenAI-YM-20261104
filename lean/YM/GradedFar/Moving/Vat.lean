import YM.GradedFar.Moving.Hats
/-!
# Unit-cost power series evaluation (for the compact comparison)
-/
namespace YM.FVA2.GradedFar.Moving
noncomputable section
open Filter Function Real PowerSeries Set Asymptotics
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Score O.Enh O.Canon Scale Dframe Jury Facets Growth
open MS.Book.Program
open scoped Topology BigOperators Classical ContDiff
variable {G : Gauge} {n d e : ℕ} {I J : Type}
variable (f : Filter I) {p : ℕ} {g : I→ℝ}
section
variable {E : Type} [NormedAddCommGroup E] {q : I→ E}
/-- cost with no polylog multipliers. -/
abbrev Buys (f : Filter I) (q : I→E) (g : I→ℝ) (p : ℕ) := q=O[f] (fun i=>g i^p)
lemma budget_of {C:ℝ} (h : ∀ᶠ i in f, ‖q i‖ ≤ C*(g i)^p) (hp : ∀ᶠ i in f,0 ≤ g i) : Buys f q g p := by
    refine IsBigO.of_bound C ?_; filter_upwards [h,hp] with i hi h
    rwa [Real.norm_of_nonneg (pow_nonneg h _)]
lemma budget {C:ℝ} (h : ∀ᶠ i in f, ‖q i‖ ≤ C) : Buys f q g 0 := IsBigO.of_bound C (h.mono fun i h=>by simp; exact h)
def Till (f : Filter I) (x : I→Portion E) (g : I→ℝ) (p : ℕ) : Prop := ∀ i≤p, Buys f (fun z=>x z i) g 0
lemma Till.const (x : Portion E) : Till f (fun (_:I)=>x) g p := fun i _=> budget f (Eventually.of_forall fun _=> le_refl ‖x i‖)
lemma pull (h : Till f (E:=E) (fun i=> fun (_:ℕ)=> q i) g p) : Buys f q g 0:= h 0 p.zero_le
lemma budget_times_smul [NormedSpace ℂ E] {y : I→ℂ} (hp : Buys f y g p) (hq : Buys f q g 0) : Buys f (fun i=> y i • q i) g p := by
    obtain ⟨C,hC,hp⟩:= hp.exists_pos; obtain ⟨D,hD,hq⟩:= hq.exists_pos
    refine IsBigO.of_bound (C*D) ?_; filter_upwards [hp.bound,hq.bound] with i hp hq
    rw [pow_zero,norm_one,mul_one] at hq; rw [norm_smul]
    exact (mul_le_mul hp hq (norm_nonneg _) ((norm_nonneg _).trans hp)).trans_eq (by ring)
lemma passes_cost {U : Type} [NormedAddCommGroup U] {x : I→U} (h : Buys f x g p) (hq : ∀ᶠ i in f, ‖q i‖ ≤ ‖x i‖) : Buys f q g p:= by obtain ⟨C,hB,h⟩:=h.exists_pos; exact IsBigO.of_bound C (hq.mp ((h.bound).mono fun i h w=> w.trans h))
lemma budget_growth (h : Buys f q g p) (n : ℕ) (hn : n ≤ p) (H : ∀ᶠ i in f,|g i| ≤ 1) : Buys f q g n := by
    exact h.trans (IsBigO.of_bound 1 (H.mono fun i H=> by simp only [one_mul,norm_pow,Real.norm_eq_abs]; exact pow_le_pow_of_le_one (abs_nonneg _) H hn))
end
lemma times_cost {E : Type} [NormedRing E] {x y : I→E} (hx : Buys f x g p) (hy : Buys f y g n) :
    Buys f (fun i=> x i*y i) g (p+n) := by
    -- use IsBigO.mul
    exact (hx.mul hy).congr_right (fun i=> (pow_add ..).symm)
lemma Till.revs {E : Type} [NormedRing E] {x y : I→Portion E} (hx : Till f x g p) (hy : Till f y g p) : Till f (fun i=> revenue (x i) (y i)) g p := by
    intro i hi; apply IsBigO.sum; intro j hj; have hw:= Finset.HasAntidiagonal.mem_antidiagonal.mp hj; exact times_cost f (hx _ (by omega)) (hy _ (by omega))

section cutoff
variable {E : Type} {t : I→ℂ} (ht : Buys f t g 1) (hg : Tendsto g f (𝓝 0))
include hg in
lemma jet_level : ∀ᶠ i in f, |g i|≤1 := (hg.eventually (Metric.closedBall_mem_nhds _ zero_lt_one)).mono fun i (h:dist (g i) 0≤1)=> by rw [← Real.norm_eq_abs, ← dist_zero_right]; exact h
include ht
lemma budget_pow (k : ℕ) : Buys f (fun i=>t i^k) g k := by
    induction k with | zero=>simpa only [pow_zero] using budget (g:=g) f (by filter_upwards with i; exact le_refl ‖(1:ℂ)‖) | succ k h=> simpa only [pow_succ] using times_cost f h ht
variable {x y : I→Portion E}
include hg
lemma before [NormedAddCommGroup E] [NormedSpace ℂ E] (hx : Till f x g p) : Buys f (fun i=> blend (x i) p (t i)) g 0 := by
    unfold blend; apply IsBigO.sum; intro j hj; exact budget_times_smul f (budget_growth f (budget_pow f ht j) _ j.zero_le (jet_level f hg)) (hx _ (Finset.mem_range_succ_iff.mp hj))
lemma past_purchase [NormedRing E] [NormedAlgebra ℂ E] (hx : Till f x g p) (hy : Till f y g p) :
    Buys f (fun i=> blend (x i) p (t i)*blend (y i) p (t i)- blend (revenue (x i) (y i)) p (t i)) g (p+1) := by
    simp_rw [compose_blend,add_sub_cancel_left]; apply IsBigO.sum; intro j hj
    obtain ⟨⟨h1,h2⟩,hk⟩:=(mem_pairsAbove p j).1 hj; exact budget_times_smul f
      (budget_growth f (budget_pow f ht _) (p+1) hk (jet_level f hg)) (times_cost f (hx _ h1) (hy _ h2))

omit ht hg in
def Pays {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (f : Filter I) (v : I→E) (x : I→Portion E) (g : I→ℝ) (p : ℕ) (t : I→ℂ) :=
    Till f x g p ∧ Buys f (fun i=> v i-blend (x i) p (t i)) g (p+1)
namespace Pays
lemma fee [NormedAddCommGroup E] [NormedSpace ℂ E] {v : I→E} (h : Pays f v x g p t) : Buys f v g 0 :=
    ((budget_growth f h.2 0 (Nat.zero_le _) (jet_level f hg)).add (before f ht hg h.1)).congr_left (fun _=> sub_add_cancel ..)
lemma joint [NormedRing E] [NormedAlgebra ℂ E] {v w : I→ E} (hx : Pays f v x g p t) (hy : Pays f w y g p t) :
    Pays f (fun i=> v i*w i) (fun i=> revenue (x i) (y i)) g p t := by
  refine ⟨Till.revs f hx.1 hy.1,?_⟩
  have he:= times_cost f (fee f ht hg hx) hy.2; rw [zero_add] at he
  refine ((he.add (times_cost f (p:=p+1) (n:=0) hx.2 (before f ht hg hy.1))).add (past_purchase f ht hg hx.1 hy.1)).congr_left
    (fun i=>?_); dsimp; rw [sub_mul,mul_sub]; abel
end Pays
section
variable {V : I → PowerSeries ℂ} (hv : Till f (fun i=>tells (V i)) g p) (he : ∀ i, Rooted (V i))
include hv
omit ht hg in
lemma acquired (k:ℕ) : Till f (fun i=> tells (V i^k)) g p := by
    induction k with
    | zero => simp_rw [pow_zero]; exact Till.const f _
    | succ k h=> simp_rw [pow_succ,revenue_tells]; exact Till.revs f h hv
omit ht hg in
lemma shifted [NormedAddCommGroup E] [NormedSpace ℂ E] (hq : Till f y g p) : Till f (fun i=>substitute (V i) (y i)) g p := by
  intro i hi; simp_rw [rules]; apply IsBigO.sum; intro j hj; exact budget_times_smul f (acquired f hv j i hi) (hq j ((Finset.mem_Iic.mp hj).trans hi))
lemma registered_power (k : ℕ) : Pays f (fun i=> blend (tells (V i)) p (t i)^k) (fun i=> tells (V i^k)) g p t := by
    induction k with
    | zero => refine ⟨acquired f hv _,?_⟩; simp [blend, tells]; exact isBigO_zero ..
    | succ k h=>
      simp_rw [pow_succ,revenue_tells]; exact Pays.joint f ht hg h ⟨hv, by simp; exact isBigO_zero ..⟩
include he
lemma recrop_substitution [NormedAddCommGroup E] [NormedSpace ℂ E] (hq : Till f y g p) :
    Buys f (fun i=> blend (y i) p (blend (tells (V i)) p (t i))- blend (Program.substitute (V i) (y i)) p (t i)) g (p+1) := by
    have hh i : blend (y i) p (blend (tells (V i)) p (t i))- blend (Program.substitute (V i) (y i)) p (t i)=
        ∑ j∈ Finset.range (p+1), (blend (tells (V i)) p (t i)^j -blend (tells (V i^j)) p (t i)) • (y i j) := by
      rw [blend_substitute _ _ _ _ (he i),blend]; simp_rw [sub_smul, Finset.sum_sub_distrib]
    simp_rw [hh]; apply IsBigO.sum; intro j hj; exact budget_times_smul f (registered_power f ht hg hv j).2 (hq _ (Finset.mem_range_succ_iff.mp hj))
end
end cutoff
end
end YM.FVA2.GradedFar.Moving
