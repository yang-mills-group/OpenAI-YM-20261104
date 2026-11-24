import YM.FVA2.Full.Glyph
import YM.FVA2.Press.Lights
/-!
# Internal shifts on FullBook: use precisely XSpace.Bare.column's starting vectors

bidegree labelling at native horizon. All orders and any surveys. Mirror certifies parity of
input stencils. This certificate imposes no parity condition on the coupling reset.
Used to construct `Press.wickInput` with the same MS landings via Film0, (see also `Position/Table`),
and thus match using the **same extended columns**. In the surveys use each column
at its own horizon, and in the sums use the through-horizon, with the ranks from here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Press
open Function Filter Set Lattice Wilson Labels Source Source.Drops Bid XSpace
open MS MS.Koszul MS.Cylinder Lab MS.Native MS.Native.Sew MS.Book MS.Local.Physical MS.Rake MS.Lifting MS.Theater MS.Menus
open MvPolynomial Finsupp Next.Rank.Normal XSpace.Contraction
open scoped Topology BigOperators ContDiff Classical
variable {G:Gauge}{H:Hol G}{w u v r:ℕ} (Y:XSpace.Initialize G)
local notation "B" => portDeck G
section rank
-- reproduce the necessary General_ward facts w/o other imports
variable {I:Type*} (K:Cov I)
local notation "R" => (fun _ : I=> (1:ℕ))
private lemma birthday (s:I→₀ℕ)(i:I): weight R (s+single i 1) = weight R s+1:= by rw [map_add,weight_single,one_smul]
private lemma circle_nil {s : I→₀ℕ} (h: weight R s=0): s=0:= by
  ext1 i; by_contra ha
  obtain He:= (Finset.sum_eq_zero_iff_of_nonneg (s:=s.support) (fun i _=>Nat.zero_le (s i • (1:ℕ)))).1 h i (Finsupp.mem_support_iff.mpr (show s i ≠ 0 from ha)); simp at He; exact ha He
private lemma owns_x (i:I) : MvPolynomial.X i ∈ weightBound R 1:= (bounded _).2 (fun k hk=> (show weight R k = 1 from isWeightedHomogeneous_X («R»:=ℂ) R i (MvPolynomial.mem_support_iff.mp hk)).le)
private lemma leaner (p:poly I) (h:p∈weightBound R (v+1)): milk K p-p∈ weightBound R v:= by
  have he (s:I→₀ℕ)(t:ℂ): milk K (monomial s t)-monomial s t∈ weightBound R (weight R s -1):=by
    apply Extra.FD.per_factor s; simp [Next.Rank.Normal.fine]
    intro s i H; rw [monomial_add_single,pow_one,mul_comm,feeds, add_sub_right_comm,← mul_sub,birthday s i,Nat.add_sub_cancel]; refine Submodule.add_mem _ ?_ (slit_bound _ _ (wick_bound _ _ (has_self _ _ t)))
    rcases Nat.eq_zero_or_pos (weight R s) with hp|hp; · simp [circle_nil hp]
    refine (show 1+(weight R s-1)=weight R s by omega) ▸ bounds_mul R (owns_x i) H
  rw [p.as_sum,_root_.map_sum,← Finset.sum_sub_distrib]; apply Submodule.sum_mem; intro i hi; apply XSpace.Contraction.higher _ _ (he ..); have ht:weight R i≤ v+1:=(bounded _).1 h _ hi; omega
end rank

variable (A: Survey G H w)
def beginning (i:(B).BIndex w r) : Labels.Label G w:= ⟨film B i, limitH (cinema _|>.mp (filmW B i) |>.1), cinema _|>.mp (filmW B i) |>.2.1⟩
lemma primary (i:(B).BIndex w r) : beginning i ∈ Labels.Grade (w,r):= (pure_grade ..).mpr ((cinema _).mp (filmW B i)|>.1)
lemma reality (i:(B).BIndex w r) : realBar (beginning i) = beginning (w:=w) i:= Subtype.ext (show Labels.conjPol (film _ i (h:=w))= _ from (cinema _).mp (filmW B i)|>.2.2)

def diff (V:Labels.Label G w):= A.insertW (-1) V - V
variable {V:Labels.Label G w}
lemma projects_out (i:(B).BIndex w r) (u v:ℕ): (gradePart (u,v) (diff A (beginning i))).val ∈ Film0 G u v:= by
 apply (cinema _).mpr; let z:=beginning (w:=w) i; set x := gradePart (u,v) (diff A z); refine ⟨(pure_grade ..).mp (gradePart_mem (u,v) (diff A z)), x.property.2,?_⟩; have he: realBar x=x:= by unfold x; rw [← gradePart_bar,diff,map_sub,← A.wick_real,show realBar z=z from reality i]
 exact congr_arg Subtype.val he
lemma pure_count (hv: V∈Labels.Grade (v,r)) : IsWeightedHomogeneous (fun _=> (1:ℕ)) V.val r := by
 intro s hs; have hx:= (pure_grade ..).mp hv hs; rw [weight_slot] at hx; simpa only [Finsupp.weight_apply, smul_eq_mul,mul_one] using (congr_arg Prod.snd hx)
lemma upper_empty (h : V∈ Labels.Grade (w,r)) (n s:ℕ)(hp:r ≤ s): gradePart (n,s) (diff A V)=0:= by
 rcases r with _|r
 · obtain ⟨c,rfl⟩:= scalar_grade w h; rw [diff,map_smul,A.wick_unit,sub_self,map_zero]
 apply Subtype.ext; ext i
 have hz: ∀ i∈ (diff A V).val.support, weight (fun _ : Labels.Key G=> (1:ℕ)) i ≤ r:= (bounded _).1 (show (diff A V).val∈ _ from leaner (A.selfCov _) V.val ((bounded _).2 (fun i hi=> (pure_count h (MvPolynomial.mem_support_iff.mp hi)).le)))
 change (weightedHomogeneousComponent bidegree (n,s) (diff A V).val).coeff i=_; rw [Submodule.coe_zero,MvPolynomial.coeff_zero,MvPolynomial.coeff_weightedHomogeneousComponent]; split_ifs with ht; swap; rfl
 by_contra ha; specialize hz i (MvPolynomial.mem_support_iff.mpr ha); rw [weight_slot] at ht; rw [show weight (fun _:Labels.Key G=> (1:ℕ)) i=s from by simpa only [Finsupp.weight_apply, smul_eq_mul, mul_one] using congr_arg Prod.snd ht] at hz; omega
private lemma mirror_id (G:Gauge): XSpace.Taylor.mirror (Labels.Key G)= changed (fun i => -( LinearMap.id (R:=ℝ) (M:= Labels.Taylor G i) )):= by
 ext1 i; apply Labels.eval_ext; intro x; rw [eval_changed,XSpace.Taylor.mirror,aeval_X,map_neg]; simp [Labels.read,Labels.coord,changedJet]
local notation "ξ" => XSpace.Taylor.mirror
lemma diff_parity (ht: V∈ Labels.Grade (u,r)): ξ _ (diff A V).val = ((-1:ℂ)^r) • (diff A V).val:= by
    change ξ _ (milk ( A.selfCov (-1) ) V.val - V.val)= _ • (_- _)
    rw [map_sub, ← XSpace.Taylor.reflected_milk, XSpace.Bare.slot_parity r V.val (fun i hi=>?_ ), map_smul,smul_sub]; rfl
    have hp:= (pure_grade ..).1 ht (MvPolynomial.mem_support_iff.mp hi); rw [weight_slot] at hp; exact congr_arg Prod.snd hp.symm
lemma odd_empty (h: V ∈ Labels.Grade (u,r))(k n:ℕ)(hn:n ≤ r)(hp: Odd (r-n)): gradePart (k,n) (diff A V)=0:= by
 apply Subtype.ext; let F:= (gradePart (k,n) (diff A V)).val
 have ht: ξ _ F= ((-1:ℂ)^r) • F:= by
    change ξ _ (piece _ _) = _; rw [mirror_id, component_change, ← mirror_id,diff_parity A h,map_smul]; rfl
 have hx: ξ _ F= ((-1:ℂ)^n) • F:= XSpace.Bare.slot_parity n F (fun i hi=> by
    have hp':= (pure_grade ..).1 (gradePart_mem (k,n) (diff A V)) (MvPolynomial.mem_support_iff.mp hi); rw [weight_slot] at hp'; exact congr_arg Prod.snd hp'.symm)
 by_contra he; obtain he:= smul_left_injective ℂ (show F≠0 from he) (ht.symm.trans hx); rw (occs:=.pos [1]) [← Nat.sub_add_cancel hn,pow_add,hp.neg_one_pow] at he; have hN:= mul_right_cancel₀ (b:= ( -1:ℂ )^n ) (by norm_num) (he.trans (one_mul _).symm); norm_num at hN

def chip (c : Glyph B v) (j : c.Bundle) : Labels.Label G c.size :=
    j.elim (fun _=> beginning (w:=c.size) c.2.2)
           (fun p=> gradePart (p.1.val, p.2.val) (diff (Y.surveys c.size) (beginning c.2.2)))
lemma compact (c:Glyph B v): (Y.surveys c.size).insertW (-1) (beginning c.2.2)= ∑ j: c.Bundle, chip Y c j:= by
 rw [Fintype.sum_sum_type,Fintype.sum_unique, Fintype.sum_prod_type]; let V:= beginning (w:=c.size) c.2.2; let A:= Y.surveys c.size; let f (i j:ℕ):= gradePart (i,j) (diff A V)
 change _= V+ ∑ i:Fin (c.size+1), ∑ j:Fin c.grade, f i.val j.val; suffices he: ∑ i:Fin (c.size+1), ∑ j:Fin c.grade, f i.val j.val=diff A V by rw [show ∑ i: Fin (c.size+1),∑ j:Fin c.grade, _ = _ from he]; change A.insertW _ _= _ + (A.insertW _ _ - _); abel
 simp_rw [Fin.sum_univ_eq_sum_range]; rw [Fin.sum_univ_eq_sum_range (fun x=> ∑ j∈Finset.range c.grade,f x j), ← show ∑ i∈Finset.range (c.size+1), ∑ j∈ Finset.range (c.size+1), f i j=diff A V from decompose _]; refine Finset.sum_congr rfl (fun i _=> Finset.sum_subset (Finset.range_mono (show c.grade≤ c.size+1 from c.2.1.isLt.le)) (fun j _ hj=> upper_empty A (primary (w:=c.size) c.2.2) i j (le_of_not_gt (fun h=> hj ( Finset.mem_range.mpr h )))))
/-- Construct a consistent MS `FullBook` for the entire calculation.
`frost`: add slots for the required W pieces, with precisely the correct (lower rank) domains.
`program` is the uncompensated operator. `Lifetime` and the metric comparison
use the compensated book constructed here.
`Voice/Encore.lean` also explains the MS entrance directly from the raw unshifted columns. -/
def wickInput (Y:XSpace.Initialize G) : FullBook B where
    toLitBook := program Y
    frost x _i u j := dot (Y.surveys x)
      (gradePart (j.1.val, j.2.val) (diff (Y.surveys x) (beginning u))).val
    prepares x _i u j := (awake (Y.surveys x) (projects_out _ u j.1.val j.2.val)
      (Nat.le_of_lt_succ j.1.isLt)).1
lemma stampF (c : Glyph B v) (j : c.Bundle) :
        Glyph.hand (wickInput Y) c j = dot (Y.surveys c.size) (chip Y c j).val := by
    cases j <;> rfl
lemma pure_chip (c : Glyph B v) (j : c.Bundle) :
        ∃ v:ℕ, chip Y c j ∈ Labels.Grade (v,c.tally j) := by
    cases j with
    | inl a => exact ⟨_, primary _⟩
    | inr a => exact ⟨a.1.val, gradePart_mem ..⟩
end YM.FVA2.Press
