import YM.IterationFour.Vacuum.Trace

/-!
# Soft failure packets for an old-layout comparison

Often the obstacle to iteration is not preserving the vacuum scalar or
shifting beta but picking the dictionary for the *next* step's marker
certificates before opened and analytic terms have recohered. In this
variant, we don't try to lift one-mark or multi-mark norms from a novel
vacuum rep back to H. Require RG03 perform the E- and mask alignment on
the actual current pre-reset X, retaining every healthy-mask discrepancy as
a soft expenditure on FAILS. Still get the utility of the E_hat alignment
and equality/polynomial tests AFTER alignment. BUT carry the old K layout
and still hold all markers over it. We prove per-output step quantitative
coupling reexpression on these uses. This file: real FAILS currency and
joining ANY such collection BEFORE the final merger.
-/
set_option autoImplicit false
noncomputable section
namespace YM.IterationFour.Shore
open Lattice Wilson RG Function MeasureTheory Filter Vacuum AnalyticBridge VerifiedReset Collection Extra.Iteration Ovens Progress.DirectedRecipe
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff Classical
variable {G : Gauge} {n : Side}

/-- Unnormalized logarithm insertion requiring at least one failed predicate,
    exact real evaluation at all fields. `places` doesn't claim nonwrapping.
    Pack possible test history in supports. -/
structure Shard (G : Gauge) (n : Side) where
    places : ℕ → Support n
    lens : ℕ → Config G n → ℝ
    sites : ∀ i,(places i).Nonempty
namespace Shard
variable (T : Shard G n)
def read (U : Config G n):= ∑' i,T.lens i U
structure Wins (p : BudgetPoint) (t : ℝ):Prop where
    forces i : ∀ U,T.lens i U ≠ 0 → ¬Healthy p.threshold (T.places i) U
    steady i : GaugeInvariant (T.lens i)
    looks i : UsesFinal p.threshold (T.places i) (T.lens i)
    measurable i : Measurable (T.lens i)
    carries s (b:Site n): ∃ v:Equiv.Perm ℕ,(∀ i,T.places (v i)=(T.places i).image (affine s b)) ∧
      ∀ U i,T.lens (v i) U=T.lens i (pull s b U)
    wields : ∃ q:ℕ→ℝ,(∀ i,0≤q i) ∧ (∀ i U,‖T.lens i U‖≤q i) ∧ Ac.Hit T.places p.B q (p.supportExponent+1) t
variable {T} {p : BudgetPoint} {t c : ℝ}
lemma Wins.income (h:T.Wins p t) {z:ℝ} (hz:t ≤ z): T.Wins p z:= by obtain ⟨q,hq,hv,hZ⟩:=h.wields; exact {h with wields:= ⟨q,hq,hv,fun i=>Cost.enlarge (hZ i) hz⟩}
lemma Wins.nonneg (h:T.Wins p t) : 0 ≤ t:= by obtain ⟨u,-,-,hv⟩:=h.wields; exact Cost.nonneg (hv 0)
lemma Wins.bound (h:T.Wins p t): Dominated T.lens:= by
   obtain ⟨u,hp,h,hQ⟩:=h.wields; exact ⟨u,Activities.summable_charge T.sites hp (Payments.drop_reserve p _ hp hQ),h⟩
lemma Wins.near (h:T.Wins p t){U} (hx: flags p.threshold U=∅): T.read U=0:=by
   unfold read; simp_rw [show ∀ i,T.lens i U=0 from fun i=>by by_contra he; apply (h.forces i U he); simp [Healthy,hx]]; simp

-- buffs
variable (T : Shard G n)
def dark:Shard G n where
    places:=T.places
    lens i U:= -(T.lens i U)
    sites:=T.sites
variable {T}
lemma dark_read (U) : T.dark.read U= -T.read U:=by unfold Shard.read; exact tsum_neg
lemma dark_pay (h:T.Wins p t): T.dark.Wins p t:=by
   obtain ⟨q,hQ,hv,hW⟩:=h.wields
   refine ⟨fun i U hx=> h.forces i U (fun hy=> hx (by unfold dark; dsimp only; rw [hy,neg_zero])),fun i a b=> congr_arg Neg.neg (h.steady i a b),fun i a b x y=> congr_arg Neg.neg (h.looks i a b x y),fun i=> h.measurable i |>.neg,?_,q,hQ,fun i U=> (norm_neg _).trans_le (hv i U),hW⟩
   intro s b; obtain ⟨v,hV,hZ⟩:=h.carries s b; exact ⟨v,hV,fun U i=> congr_arg Neg.neg (hZ U i)⟩
private def city:= numbering (ℕ⊕ℕ)
def mix {I:Type*}(f g : ℕ→I): ℕ→I:= Sum.elim f g ∘ city
lemma books (f g:ℕ→ℝ) (hf:Summable f) (hg:Summable g): ∑' i,mix f g i= (∑' i,f i)+(∑' i,g i):=by
   exact (city.tsum_eq (Sum.elim f g)).trans (Summable.tsum_sum (f:=Sum.elim f g) hf hg)
lemma common {f g:ℕ→ℝ}{X Y:ℕ→Support n}{A:ℝ}{B:ℕ}(hx : Ac.Hit X B f A t)(hy:Ac.Hit Y B g A c):
    Ac.Hit (mix X Y) B (mix f g) A (t+c):= by
   intro i; let m (x:Support n) (y:ℝ):= if i∈ x then y*Real.exp (A*coverNumber B x) else 0
   let v j:=m (X j) (f j); let u j:=m (Y j) (g j)
   exact Cost.equiv city (Cost.sum (f:=fun j=>m (Sum.elim X Y j) (Sum.elim f g j)) (hx i) (hy i))

variable (T S : Shard G n)
def adds:Shard G n where
   places:=mix T.places S.places
   lens:=mix T.lens S.lens
   sites i:= by unfold mix; dsimp only [comp_apply]; rcases city i with a|b; exact T.sites a; exact S.sites b
variable {T S}
lemma advances (h:T.Wins p t) (hh:S.Wins p c) : (adds T S).Wins p (t+c):=by
   obtain ⟨v,hV,hx,hq⟩:= h.wields; obtain ⟨u,hU,hz,hW⟩:=hh.wields
   refine ⟨fun i=>?_,fun i=>?_,fun i=>?_,fun i=>?_,fun s b=>?_,mix v u,fun i=>?_,fun i=>?_,common hq hW⟩
   · unfold adds; dsimp only [mix,comp_apply]; cases city i with | inl a=> exact h.forces a | inr a=> exact hh.forces a
   · unfold adds; dsimp only [mix,comp_apply]; cases city i with | inl a=> exact h.steady a | inr a=> exact hh.steady a
   · unfold adds; dsimp only [mix,comp_apply]; cases city i with | inl a=> exact h.looks a | inr a=> exact hh.looks a
   · unfold adds; dsimp only [mix,comp_apply]; cases city i with | inl a=> exact h.measurable a | inr a=> exact hh.measurable a
   · obtain ⟨X,hX,hE⟩:=h.carries s b; obtain ⟨Y,hY,hL⟩:=hh.carries s b; let U:=Equiv.sumCongr X Y; refine ⟨(city.trans U).trans city.symm,fun i=>?_,fun V i=>?_⟩
     · unfold adds; dsimp only [mix,comp_apply]; simp_rw [Equiv.trans_apply,Equiv.apply_symm_apply]; rcases city i with a|b; exact hX a; exact hY b
     unfold adds; dsimp only [mix,comp_apply]; simp_rw [Equiv.trans_apply,Equiv.apply_symm_apply]; rcases city i with a|b; exact hE V a; exact hL V b
   · unfold mix; dsimp only [comp_apply]; cases city i with | inl a=> exact hV a | inr a=> exact hU a
   unfold adds; dsimp only [mix,comp_apply]; cases city i with | inl a=> exact hx a | inr a=> exact hz a
lemma increased (h:T.Wins p t) (hh:S.Wins p c) (U:Config G n) : (adds T S).read U=T.read U+ S.read U:= by
   unfold Shard.read; rw [← books (fun i=> T.lens i U) (fun i=> S.lens i U) (h.bound.summable U) (hh.bound.summable U)]
   refine tsum_congr (fun i=>?_); unfold adds; dsimp only [mix,comp_apply]; cases city i<;>rfl
end Shard
end YM.IterationFour.Shore
