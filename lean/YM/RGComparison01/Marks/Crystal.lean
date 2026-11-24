import YM.MergeProof.Pulse
import YM.MergeProof.Appl
/-!
# Simultaneous marked and unmarked mask reallocations

 Analogue of Merge.Motion for variable soft taps (which needn't translate
 covariantly; only their vacuum evaluations will). In particular proves price
 and occurrence identity in the SAME digest. Does not put a Taylor series on
 the unmarked vacuum density. -/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01.Mood
open Function Filter Set Lattice Wilson RG Ovens Ovens.Pipes MeasureTheory Work.H03
open Pressure Progress.DirectedRecipe Rack ConnectedActivityE6 Finset Push Push.AbsoluteSums
open PhysicalNext.Repeat Mallow Daisy Merge Switch
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {ι:Type} [Fintype ι] {U:Type} {G : Gauge}{n : Side} {X:Pipes G n} {d:Tap G n} {P : BudgetPoint} {r c δ A B κ γ w v a:ℝ}
open Merge Motion GridRenewal.Rain
lemma salable (x:ℝ): HasSum (fun n=> slide x (n+1)) (Real.exp x-1):= by
    have hx:= (hasSum_nat_add_iff' 1).mpr (meter x);
    simpa only [sum_range_one,GridRenewal.Rain.slide,pow_zero,Nat.factorial_zero,Nat.cast_one,div_one] using hx
lemma cumulus (f : U → Ways ι) (h : Paid f a): Paid (fun u x p=> Real.exp (f u x p)-1) (Real.exp a-1):=by
  have he := issue (fun n : ℕ=>paidTerms (n+1) h) ((salable a).summable)
  simp_rw [show ∀ i x v, (∑' n:ℕ, slide (f i x v) (n+1))=_ from fun _ _ _=>(salable _).tsum_eq] at he; convert! he.1; exact (salable a|>.tsum_eq.symm)
structure Frost (X:Pipes G n)(d:Tap G n)(P:BudgetPoint)(T:ℝ→Finset ι→ Code G n)(α w:ℝ) : Prop where
   off j:T 0 j=d.logarithm
   texts t (ht:t∈Icc (0:ℝ) 1) i j: UsesFinal P.threshold (X.softer i) (T t j i)
   idle t (ht:t∈ Icc (0:ℝ) 1) i j V: Healthy P.threshold (X.softer i) V→T t j i V=0
   invariant t (ht:t∈Icc (0:ℝ) 1) i j: GaugeInvariant (T t j i)
   measures t (ht:t∈Icc (0:ℝ) 1) i j: Measurable (T t j i)
   billed : ∃ u:ℕ→ℝ,(∀ i,Paid (fun y t j=>T t j i y) (u i)) ∧ Ac.Hit X.softer P.B u α w

def crystal (d:Tap G n)(U W:ℝ→Finset ι→ Code G n)(t:ℝ)(i:Finset ι): Tap G n:= { d with logarithm:=W t i,forced:=U t i }
variable {K V : ℝ→Finset ι→ Code G n} (h : Motion.Pays (X.pours d) P K B (P.supportExponent+1))
   (hp: Frost X d P V (P.supportExponent+1) w)
local notation "Z" => crystal d K V
include h hp
lemma Frost.kettle (x : ℝ)(ht:x∈ Icc (0:ℝ) 1)(i:Finset ι): Kiln X (crystal d K V x i) P := by
  refine ⟨h.licensed _ _ ht,fun j U hi hu=> hi (hp.idle x ht j i U hu),?_,(fun j=> hp.invariant x ht j i),fun j=> hp.texts x ht j i,fun j => hp.measures x ht j i,PaidK h (le_add_of_le_of_nonneg P.exponent_pos.le zero_le_one) ht i⟩
  obtain ⟨f,hF,hv⟩:= hp.billed
  have hh := (Activities.summable_charge X.sites (fun i=> (hF i).rocket) (Payments.drop_reserve P _ (fun i=> (hF i).rocket) hv)); exact ⟨f,hh,fun j U=> (hF j).tasting _ _ ht i⟩
omit h hp
private def primaryP (p q : ℕ → ℝ) (κ : ℝ) : Ovens.Label → ℝ:= Sum.elim (fun i=> Real.exp κ * p i) (fun i=> 2*q i)
private def mild (κ : ℝ)(i:Ovens.Label) := Sum.elim (fun _=> Real.exp (-κ)) (fun _=>1) i
private theorem scaleInk {ι : Type*}(p : ι→Support n)(b : ι→ℝ){P : BudgetPoint} (hh:Ac.Hit p P.B b (P.supportExponent+1) v)(ha:0≤a): Ac.Hit p P.B (fun i=> a*b i) (P.supportExponent+1) (a*v):=by
   intro i; convert! budget_scale ha (hh i) using 1; ext j; by_cases hk:i∈p j <;> simp [hk,mul_assoc]
include h hp
variable (he: Payments.Rates P.B A B w κ)
include he
lemma bamboo : ∃ f : Ovens.Label → ℝ,(∀ i,0≤ f i) ∧ Ac.Hit X.patch P.B f (P.supportExponent+1) (Payments.inflation B w κ) ∧ ∀ i, Paid (fun U t j=>reach (crystal d K V t j) i U) (mild κ i*f i):= by
  obtain ⟨f,hP,hH⟩:= h.bought
  have hf i:= (hP i).rocket; obtain ⟨v,hv,hg⟩:= hp.billed
  have hh i:= (hv i).rocket
  refine ⟨primaryP f v κ,fun i=>?_, ?_,fun i=> ?_⟩
  · cases i
    · exact mul_nonneg (Real.exp_pos _).le (hf _)
    exact mul_nonneg zero_le_two (hh _)
  · exact Labels.together _ _ _ (scaleInk _ _ (P:=P) hH (Real.exp_pos κ).le) (scaleInk _ _ (P:=P) hg (show (0:ℝ)≤2 by norm_num))
  rcases i with i|i; simp only [primaryP,mild, Sum.elim_inl,Real.exp_neg,inv_mul_cancel_left₀ (Real.exp_pos κ).ne']; exact hP i
  simp only [primaryP,mild,Sum.elim_inr,one_mul]; obtain ⟨p,hp'⟩:= X.sites i
  have he' := Samples.one_le_quote (Payments.drop_reserve P _ hh hg p) i; rw [if_pos hp'] at he'
  have h': |v i| ≤ 1:= (abs_of_nonneg (hh i)).trans_le ((P.loMass _ _ (hh i)).trans (he'.trans he.soft_limit))
  have ha := Real.abs_exp_sub_one_le h'; rw [abs_of_nonneg (hh _)] at ha
  exact (cumulus _ (hv i)).weaken ((le_abs_self _).trans ha)

abbrev frozen (F : ℕ≃X.Pellet) (P:BudgetPoint)(d:Tap G n)(K V: ℝ→Finset ι→ Code G n)(t:ℝ)(i:Finset ι) := solid F P (crystal d K V t i)
local notation "Y"=> fun (F:ℕ≃X.Pellet)=> frozen F P d K V
lemma pass (F : ℕ ≃ Pellet X): Motion.Pays (fused F P d) P (frozen F P d K V) A P.supportExponent:=by
  constructor
  · intro j; unfold frozen; rw [show crystal d K V 0 j=d from ?_]; · rfl
    unfold crystal; rw [h.term,hp.off]; rfl
  · intro t j ht; obtain ⟨h,h₁,h₂,h₃,h₄,h₅,h₆⟩:= Passage.fused_forcedFamily F (Frost.kettle h hp t ht j)
    exact ⟨h,h₁,h₂,h₃,h₄,h₅,h₆⟩
  obtain ⟨f,hF,hW,hK⟩:=bamboo h hp he
  let v i:= ∏ j∈ (F i).val, f j; let M i:= Real.exp (-κ)*v i; let γ:=Payments.inflation B w κ
  have hp : 0≤ γ:= add_nonneg (mul_nonneg (Real.exp_pos _).le he.hard) (mul_nonneg zero_le_two he.soft)
  have hv i :0≤ v i:= prod_nonneg fun j _=> hF _; have hh i:0≤ M i:=mul_nonneg (Real.exp_pos _).le (hv i)
  refine ⟨M,fun i=>?_,fun x=>?_⟩
  · have hg:= Paid.prod (F i).val _ _ (fun j (_ : j∈(F i).val)=> hK j)
    refine Paid.congr ((Paid.gate (X:={U|(addr F P i).eligible P.threshold U}) (hg.weaken ?_))) (fun U t ht=> ?_)
    · rw [prod_mul_distrib]; unfold M v; apply mul_le_mul_of_nonneg_right _ (hv _)
      obtain ⟨j,hj⟩:= (F i).property.1
      have hm (i : Ovens.Label):mild κ i≤1:=by cases i; exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr he.heading); rfl
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
      unfold Ac.roots; dsimp only; rw [if_pos ⟨(F i).property.2.1,h⟩]; apply le_of_eq; change M i*_=Real.exp (-κ) *(Real.exp _* v i)
      unfold M v; ring_nf; rfl
    exact (budget_scale (Real.exp_pos (-κ)).le (budget_pull b hi hR)).1 _
omit h hp he
omit [Fintype ι] in
lemma honors (i:ι)(o: Site n)(hk:Motion.Hush i o (fun j=> (X.kernel j).support) K)
   (hW:Motion.Hush i o X.softer V)(F : ℕ≃X.Pellet) : Hush i o (fun j=> (addr F P j).support) (frozen F P d K V):= by
   intro j t p hp; funext U; unfold frozen solid; split
   · refine prod_congr rfl fun u hu=>?_; have hs : o∉ X.patch u:= fun h=> hp (subset_biUnion_of_mem X.patch hu h); rcases u with j'|j'
     · exact congr_fun (hk _ _ _ hs) U
     exact congr_arg (fun x=>Real.exp x-1) (congr_fun (hW _ _ _ hs) U)
   rfl
include h hp
lemma reconstructed (x:ℝ) (he:x∈ Icc (0:ℝ) 1) (T:Finset ι)(F:ℕ≃X.Pellet) (U:Config G n) : HasSum (fun i=>((black (fused F P d) (frozen F P d K V x T)).gasOccurrence P i U))
   (((black (X.pours d) (K x T)).gas P U)*Real.exp (∑' i, V x T i U)):= Passage.gathered (F:=F) (Frost.kettle h hp x he T) U
end YM.RGComparison01.Mood
