import YM.Frontier6.Bouquet.Market.Grooves

/-! Uniform single-parent annulus bounds from refinement hypotheses.
    Fix the test order prior to any Air instance. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Bouquet.Atelier
open Function Set Finset Ensemble MeasureTheory Normal Filter Road Forest Tale Spec Curtains Prescription Metric Audit Submodule Fareway
open scoped Topology BigOperators Classical InnerProductSpace lp ContDiff Matrix.Norms.Frobenius
open scoped YM.Frontier6.Bouquet
variable {I X L Y:Type}{G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}
variable [NormedAddCommGroup Y][NormedSpace ℂ Y][NormedSpace ℝ Y][IsScalarTower ℝ ℂ Y][CompleteSpace Y]
variable (K:Final C F S)(d:Slot→ℕ)(v:(i:Slot)→S.Field (d i)){P:Ensemble}(i:P)
structure Settled (K:Final C F S)(d:Slot→ℕ)(v:(i:Slot)→S.Field (d i))(i:P)(R:Air (S:=S) P I L Y)(n:ℕ)(M:Pod→ℝ)(B C' ε D:ℝ): Prop where
   pos : 0 ≤ D
   price : ∀ (x:I)(t A a:ℝ)(f:Full (fiber P)), Length P M t→0<a→R.suitable x C' t→Fellow P (R.lengths x) (R.region x) B f n A→ Flare i f (R.lengths x i) → ‖launch K d v (R.region x) (R.sky x) t a f‖≤D*A*R.freight d x ε
   discount : ∀ (x:I)(t A a b:ℝ)(f:Full (fiber P)),Length P M t→0<a→a≤b→ R.suitable x C' t→ Fellow P (R.lengths x) (R.region x) B f n A→ Flare i f (R.lengths x i)→ ‖launch K d v (R.region x) (R.sky x) t a f-launch K d v (R.region x) (R.sky x) t b f‖≤ D*A*R.freight d x ε*R.delta x b

section
variable {R: Air (S:=S) P I L Y}{M:Pod→ℝ}{n:ℕ}{B C' ε:ℝ}{V:Type}[Fintype V]
variable (Z: V→ Court i)(g: V→ Full (normal i.val)) (ht:∀ q:V, tsupport (g q) ⊆ (Z q).chamber) (hg:∀ x∈Ringed (normal i.val) 1, ∑ q:V,g q x=1)
include Z hg ht
theorem settles (h:∀ q:V,∃ u:ℝ,0 ≤ u∧(Z q).Asks u K d v M R n B C' ε)(hw:R.Welkin M):∃ D, Settled K d v i R (n+n) M B C' ε D:=by
   choose p hp hP using h; choose C hC H using fun q:V=> issues i (g q) n; let D:=∑ q:V,p q*C q; let F(x:I)(t a:ℝ)(f:Full (fiber P)):= launch K d v (R.region x) (R.sky x) t a f; let g'(q:V)(x:I)(f):= issued i (g q) (R.lengths x i) f
   have hf(q:V)(x:I){A t:ℝ}{f:Full (fiber P)}(hh:Fellow P (R.lengths x) (R.region x) t f (n+n) A): (Z q).Contains (R.lengths x i) (g' q x f) ∧ Fellow P (R.lengths x) (R.region x) t (g' q x f) n (C q*A):= ⟨Court.issued_here i (Z q) (R.length_pos x i) (ht q),H q A t _ (R.region x) f (R.length_pos x i) hh⟩
   have hm(x:I)(t A:ℝ)(f:Full (fiber P))(hh:Fellow P (R.lengths x) (R.region x) B f (n+n) A)(he:Flare i f (R.lengths x i))(a:ℝ): F x t a f=∑ q,F x t a (g' q x f):=by
       nth_rw 1 [cartoons i g hg he (R.length_pos x i)]; let A:= prepared K (common a) d v t; let u:= (R.region x).center; let H:=R.sky x; exact selects K A (common a) u H Finset.univ Finset.univ (fun q _=> Welcomes.appointed K A (common a) u H _ ⟨_,hw.smooth x,(hf q x hh).2.fair⟩)
   have hp'(B:ℝ) : ∑ q:V,p q*(C q*B)=D*B:= by unfold D; rw [Finset.sum_mul]; simp_rw [mul_assoc]
   refine ⟨D,sum_nonneg (fun q _=>mul_nonneg (hp q) (hC q)),fun x t A a f hl hu hr hh hc=>?_,fun x t A a b f hl hu hv hr hh hc=>?_⟩
   · change ‖F x t a f‖ ≤ _; rw [hm x t A f hh hc, ← hp', Finset.sum_mul]; apply (norm_sum_le ..).trans; refine Finset.sum_le_sum fun q h=>?_ ; exact (hP q).price x _ _ _ _ hl hu hr (hf q _ hh).2 (hf q _ hh).1
   change ‖F x t a f - F x t b f‖≤_; rw [hm x t A f hh hc, hm x t A f hh hc, ← Finset.sum_sub_distrib,← hp', Finset.sum_mul, Finset.sum_mul]; exact (norm_sum_le ..).trans (Finset.sum_le_sum fun q _=> (hP q).many x t _ _ _ _ hl hu hv hr (hf q _ hh).2 (hf q _ hh).1)
end
-- no element dependence of testing order
def Seated (n:ℕ):Prop:=∀ {Y I L:Type}[NormedAddCommGroup Y][NormedSpace ℂ Y][NormedSpace ℝ Y][IsScalarTower ℝ ℂ Y][CompleteSpace Y]{M:Pod→ℝ}{X:Air (S:=S) P I L Y}, Dais K d P M → X.Welkin M→ Air.Hosts K X→∀ (B C ε:ℝ),1≤B→1≤C→0<ε→∃ D,Settled K d v i X n M B C ε D
lemma seated (h:∀ Q<P,∃ n,Sails K d v Q n): ∃ n, Seated K d v i n:=by
    obtain ⟨V,_,Z,g,hP,hg⟩:=unit_choice i; choose n hn using fun z:V=> h (Z z).split ((Z z).legend.strict)
    obtain ⟨D,hD⟩:∃ D:ℕ,∀ z:V, n z ≤ D:= (eventually_all.mpr fun i:V=> eventually_ge_atTop (n i)).exists
    let p:=D+D; refine ⟨p+p,?_⟩; intro Y I L _ _ _ _ _ M X hk hw hx B C ε hB hC hε; refine settles K d v i Z g hP hg (fun z=>?_) hw; obtain ⟨w,h⟩:= hn z (hk.lower (Z z).legend.le) ((Z z).overSky X hw hk) ((Z z).following X hx) B C ε hB hC hε; exact (Z z).earned v hw (h.more (hD z)) (zero_lt_one.trans_le hB)
end YM.Frontier6.Bouquet.Atelier
