
import YM.MergeProof.Pulse
/-! # Following reallocations with live soft terms. -/
set_option autoImplicit false
noncomputable section
namespace YM.Merge.Motion
open Function Filter Set Lattice Wilson RG Ovens Ovens.Pipes MeasureTheory Work.H03
open Pressure Progress.DirectedRecipe Rack ConnectedActivityE6 Finset Push Push.AbsoluteSums
open PhysicalNext.Repeat Mallow Daisy Switch
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {ι:Type}[Fintype ι] {G : Gauge}{n : Side}
    {X:Pipes G n} {d:Tap G n} {P : BudgetPoint} {r c δ A B κ γ w v a:ℝ} {o : Site n}
open GridRenewal.Rain
lemma sproutW (y:ℝ): (∑' i:ℕ,slide y (i+1))=Real.exp y-1:=by
    have hf:= meter y; have hu:= hf.summable.sum_add_tsum_nat_add 1
    simp only [sum_range_one, GridRenewal.Rain.slide,pow_zero, Nat.factorial_zero,Nat.cast_one,div_one] at hu -- right slide no change? unfolds slide on RHS. careful
    change (1 + ∑' i:ℕ,slide y (i+1))=∑' i,slide y i at hu
    rw [hf.tsum_eq] at hu; linarith
lemma kindle {Y:Type}{f:Y→Ways ι}{a:ℝ} (h:Paid f a)(ha:a≤1) : Paid (fun U x p=> Real.exp (f U x p)-1) (2*a):=by
    have hb:= Switch.issue (fun i:ℕ=> paidTerms (i+1) h) ((summable_nat_add_iff _).2 (meter a).summable)
    have hx:Paid (fun U t P=>∑' i:ℕ,slide (f U t P) (i+1)) _:= hb.1
    simp_rw [sproutW] at hx; refine hx.weaken ((le_abs_self _).trans ?_); have hp: |a|=a:= abs_of_nonneg h.rocket; have hh:= Real.abs_exp_sub_one_le (hp.trans_le ha); rwa [hp] at hh

abbrev Traversal := ℝ→Finset ι→ Code G n
def alt (k l: Code G n) : Tap G n := ⟨d.regular,k,l⟩ -- d binder unused. use basal.Synth
set_option quotPrecheck false
variable (d)
section
variable {K Z: ℝ→Finset ι→ Code G n} (h:Pays (X.pours d) P K B (P.supportExponent+1))
structure Smoke {G:Gauge}{n:Side}(X:Pipes G n)(P:BudgetPoint){ι:Type} (Z:ℝ→Finset ι→ Code G n)(w:ℝ)[Fintype ι] :Prop where
    off j: Z 0 j=0
    failed i V : ∀ x q,Z x q i V≠0 → ¬Healthy P.threshold (X.softer i) V
    crown x q i : GaugeInvariant (Z x q i)
    story x q i : UsesFinal P.threshold (X.softer i) (Z x q i)
    measurable x q i: Measurable (Z x q i)
    paid : ∃ a:ℕ→ℝ,(∀ i,Paid (fun U x q => Z x q i U) (a i)) ∧ Ac.Hit X.softer P.B a (P.supportExponent+1) w
local notation "Z₀"=> (fun x i=> alt (d:=d) (K x i) (Z x i))
variable (ht:Smoke X P Z w)
include h ht
lemma firesL (x:ℝ)(hx:x∈ Set.Icc (0:ℝ) 1)(p:Finset ι): Kiln X (alt (d:=d) (K x p) (Z x p)) P:=by
   refine ⟨h.licensed x p hx,fun i U=>ht.failed i U x p, ?_,ht.crown x p,ht.story x p,ht.measurable x p,PaidK h (by linarith [P.exponent_pos]) hx p⟩
   obtain ⟨b,hb,hP⟩:= ht.paid
   let T₀:= P.supportExponent+1
   have h':0≤ P.supportExponent+1:= le_add_of_le_of_nonneg P.exponent_pos.le zero_le_one
   have hU:= AbsoluteSums.Product.everyone_ne X.softer P.B (fun i=>(hb i).rocket) (fun i _=> X.sites i) hP
   exact ⟨b,hU.2.1.of_nonneg_of_le (fun i=> Paid.rocket (hb i)) (fun i=> le_mul_of_one_le_right (Paid.rocket (hb i)) (Real.one_le_exp (mul_nonneg h' (by positivity)))),fun i U=> Paid.tasting (hb i) U x hx p⟩
omit h ht
private def primaryU (p q : ℕ → ℝ) (κ : ℝ) : Ovens.Label → ℝ:= Sum.elim (fun i=> Real.exp κ * p i) (fun i=> 2*q i)
private def mind (κ : ℝ)(i:Ovens.Label) := Sum.elim (fun _=> Real.exp (-κ)) (fun _=>1) i
private theorem scaleU {ι : Type*}(p : ι→Support n)(b : ι→ℝ){P : BudgetPoint} (hh:Ac.Hit p P.B b (P.supportExponent+1) v)(ha:0≤a): Ac.Hit p P.B (fun i=> a*b i) (P.supportExponent+1) (a*v):=by
   intro i; convert! budget_scale ha (hh i) using 1; ext j; by_cases hk:i∈p j <;> simp [hk,mul_assoc]
-- pure prop certification
variable (he : Payments.Rates P.B A B w κ)
include h ht he
lemma stashW : ∃ f : Ovens.Label → ℝ,(∀ i,0≤ f i) ∧ Ac.Hit X.patch P.B f (P.supportExponent+1) (Payments.inflation B w κ) ∧ ∀ i, Paid (fun U t j=>reach (Z₀ t j) i U) (mind κ i*f i):= by
  obtain ⟨f,hP,hH⟩:= h.bought
  have hf i:= (hP i).rocket; obtain ⟨v,hg,hx⟩:= ht.paid; have hv i:0≤v i:=(hg i).rocket
  refine ⟨primaryU f v κ,fun i=>?_, ?_,fun i=> ?_⟩
  · cases i
    · exact mul_nonneg (Real.exp_pos _).le (hf _)
    exact mul_nonneg zero_le_two (hv _)
  · exact Labels.together _ _ _ (scaleU _ _ (P:=P) hH (Real.exp_pos κ).le) (scaleU _ _ (P:=P) hx (show (0:ℝ)≤2 by norm_num))
  rcases i with i|i; simp only [primaryU,mind, Sum.elim_inl,Real.exp_neg,inv_mul_cancel_left₀ (Real.exp_pos κ).ne']; exact hP i
  simp only [primaryU,mind,Sum.elim_inr,one_mul]; apply kindle (hg i); obtain ⟨U,hp⟩:= X.sites i; have hr := Samples.one_le_quote (Payments.drop_reserve P _ hv hx U) i;rw [if_pos hp] at hr; exact ((P.loMass _ _ (hv i)).trans hr).trans he.soft_limit
lemma harvestU (F : ℕ ≃ Pellet X): Pays (fused F P (alt (d:=d) d.forced 0)) P (fun t i=> solid F P (Z₀ t i)) A P.supportExponent:=by
  constructor
  · intro j; dsimp only; rw [h.term j,ht.off j]; rfl
  · intro t j hr; obtain ⟨h,h₁,h₂,h₃,h₄,h₅,h₆⟩:= Passage.fused_forcedFamily F (firesL d h ht t hr j)
    exact ⟨h,h₁,h₂,h₃,h₄,h₅,h₆⟩
  obtain ⟨f,hF,hW,hK⟩:=stashW d h ht he
  let v i:= ∏ j∈ (F i).val, f j; let M i:= Real.exp (-κ)*v i; let γ:=Payments.inflation B w κ
  have hp : 0≤ γ:= add_nonneg (mul_nonneg (Real.exp_pos _).le he.hard) (mul_nonneg zero_le_two he.soft)
  have hv i :0≤ v i:= prod_nonneg fun j _=> hF _; have hh i:0≤ M i:=mul_nonneg (Real.exp_pos _).le (hv i)
  refine ⟨M,fun i=>?_,fun x=>?_⟩
  · let f':= ∏ j∈(F i).val,fun U t i'=>reach (Z₀ t i') j U
    have hg:= Paid.prod (F i).val _ _ (fun j (_ : j∈(F i).val)=> hK j)
    refine Paid.congr ((Paid.gate (X:={U|(addr F P i).eligible P.threshold U}) (hg.weaken ?_))) (fun U t ht=> ?_)
    · rw [prod_mul_distrib]; unfold M v; apply mul_le_mul_of_nonneg_right _ (hv _)
      obtain ⟨j,hj⟩:= (F i).property.1
      have hm (i : Ovens.Label):mind κ i≤1:=by cases i; exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr he.heading); rfl
      rw [← mul_prod_erase _ _ (Finset.mem_toLeft.mp hj)]
      exact mul_le_of_le_one_right (Real.exp_pos (-κ)).le (Finset.prod_le_one (fun i hi=> by cases i; exact (Real.exp_pos _).le; exact zero_le_one) (fun i hi=> hm i))
    ext i'; by_cases hz: (addr F P i).eligible P.threshold U
    · rw [Set.indicator_of_mem (show U∈_ from hz)]; simp_rw [Finset.prod_apply]; exact (if_pos hz).symm
    rw [Set.indicator_of_notMem]; exact (if_neg (show ¬ (addr F P i).eligible P.threshold U from hz)).symm; exact hz
  · have hR:= Ac.forest X.patch P.B P.exponent_pos.le hF hW he.capital hp x
    let b (p):= (F p).val; have hi : Injective b:= Subtype.val_injective.comp F.injective
    refine budget_loosen (budget_mono (budget_scale (Real.exp_pos (-κ)).le (budget_pull b hi hR)) (fun i=>?_) (fun i=> ?_)) he.returns
    · split; · exact mul_nonneg (hh _) (Real.exp_pos _).le
      exact le_rfl
    split
    next h=>
      unfold Ac.roots; dsimp only; rw [if_pos ⟨(F i).property.2.1,h⟩]; apply le_of_eq; change M i*_=Real.exp (-κ) *(Real.exp _* v i) -- orientation?
      unfold M v; ring_nf; rfl
    exact (budget_scale (Real.exp_pos (-κ)).le (budget_pull b hi hR)).1 _
end
end YM.Merge.Motion
