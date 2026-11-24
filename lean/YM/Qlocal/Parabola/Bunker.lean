import YM.Qlocal.Reclosure
import YM.Qlocal.Parabola.Stars
/-! Using StellarTree.sharp, retain margin at LAST harvest with no extra admission. For post-alignment at the true scheduled exponent (without dropping next-step admission). -/
set_option autoImplicit false
noncomputable section

namespace YM.Qlocal
open Function Filter Set Lattice Wilson RG Ovens Ovens.Pipes MeasureTheory Work.H03
open Pressure Progress.DirectedRecipe Rack ConnectedActivityE6 Finset Push Push.AbsoluteSums
open Merge PhysicalNext.Repeat Mallow Daisy Switch Motion
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {ι Ω : Type} [Fintype ι] {G : Gauge}{n : Side}
    {X:Pipes G n} {d:Tap G n} {P : BudgetPoint} {r b c δ A B κ γ w v a:ℝ}
    {Y L : Activities G n} {K : WayK Ω ι G n}

namespace UniformPays

private def privateA (p q : ℕ → ℝ) (κ : ℝ) : Ovens.Label → ℝ:= Sum.elim (fun i=> Real.exp κ * p i) (fun i=> 2*q i)
private def ownMild (κ : ℝ)(i:Ovens.Label) := Sum.elim (fun _=> Real.exp (-κ)) (fun _=>1) i
private theorem tenting {ι : Type*}(p : ι→Support n)(b : ι→ℝ){P : BudgetPoint} (hh:Ac.Hit p P.B b (P.supportExponent+1) v)(ha:0≤a): Ac.Hit p P.B (fun i=> a*b i) (P.supportExponent+1) (a*v):=by
   intro i; convert! budget_scale ha (hh i) using 1; ext j; by_cases hk:i∈p j <;> simp [hk,mul_assoc]
variable (h : UniformPays (X.pours d) P K B (P.supportExponent+1))(hp: Vapor X d P w)(he: Payments.Rates P.B A B w κ)
include h hp he
private lemma toolboxes : ∃ f : Ovens.Label → ℝ,(∀ i,0≤ f i) ∧ Ac.Hit X.patch P.B f (P.supportExponent+1) (Payments.inflation B w κ) ∧
    ∀ i, Paid (fun U : Ω×Config G n=> fun t j=>reach (spice d (K U.1 t j)) i U.2) (ownMild κ i*f i):= by
  obtain ⟨f,hP,hH⟩:= h.credit
  have hf i:= (hP i).rocket; obtain ⟨v,hv,hg⟩:= hp.funds
  refine ⟨privateA f v κ,fun i=>?_, ?_,fun i=> ?_⟩
  · cases i
    · exact mul_nonneg (Real.exp_pos _).le (hf _)
    exact mul_nonneg zero_le_two (hv.1 _)
  · exact Labels.together _ _ _ (tenting _ _ (P:=P) hH (Real.exp_pos κ).le) (tenting _ _ (P:=P) hv.2 (show (0:ℝ)≤2 by norm_num))
  rcases i with i|i; simp only [privateA,ownMild, Sum.elim_inl,Real.exp_neg,inv_mul_cancel_left₀ (Real.exp_pos κ).ne']; exact hP i
  simp only [privateA,ownMild,Sum.elim_inr,one_mul]; refine Switch.constant (reach d (Sum.inr i) ∘ Prod.snd) (mul_nonneg zero_le_two (hv.1 i)) ?_
  intro U
  change |Real.exp (d.logarithm i U.2)-1|≤2*v i
  apply (Real.abs_exp_sub_one_le ?_).trans (mul_le_mul_of_nonneg_left (hg i U.2) zero_le_two); obtain ⟨p,hp⟩:= X.sites i
  have he' := Samples.one_le_quote (Payments.drop_reserve P _ hv.1 hv.2 p) i; rw [if_pos hp] at he'
  exact (hg i U.2).trans ((P.loMass _ _ (hv.1 i)).trans (he'.trans he.soft_limit))
lemma revenue (F : ℕ ≃ Pellet X) : UniformPays (fused F P d) P (joints P d F K) A (P.supportExponent+StellarTree.spare P.B):=by
  constructor
  · intro u j; rw [joints,show spice d (K u 0 j)=d by rw [h.term]; rfl]; rfl
  · intro u t j ht; obtain ⟨h,h₁,h₂,h₃,h₄,h₅,h₆⟩:= Passage.fused_forcedFamily F (kitch (h.project u) hp t ht j)
    exact ⟨h,h₁,h₂,h₃,h₄,h₅,h₆⟩
  obtain ⟨f,hF,hW,hK⟩:=toolboxes h hp he
  let v i:= ∏ j∈ (F i).val, f j; let M i:= Real.exp (-κ)*v i; let γ:=Payments.inflation B w κ
  have hp : 0≤ γ:= add_nonneg (mul_nonneg (Real.exp_pos _).le he.hard) (mul_nonneg zero_le_two he.soft)
  have hv i :0≤ v i:= prod_nonneg fun j _=> hF _; have hh i:0≤ M i:=mul_nonneg (Real.exp_pos _).le (hv i)
  refine ⟨M,fun i=>?_,fun x=>?_⟩
  · let f':= ∏ j∈(F i).val,fun U:Ω ×Config G n=> fun t i'=>reach (spice d (K U.1 t i')) j U.2
    have hg:= Paid.prod (F i).val _ _ (fun j (_ : j∈(F i).val)=> hK j)
    refine Paid.congr ((Paid.gate (X:={U:Ω×Config G n|(addr F P i).eligible P.threshold U.2}) (hg.weaken ?_))) (fun U t ht=> ?_)
    · rw [prod_mul_distrib]; unfold M v; apply mul_le_mul_of_nonneg_right _ (hv _)
      obtain ⟨j,hj⟩:= (F i).property.1
      have hm (i : Ovens.Label):ownMild κ i≤1:=by cases i; exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr he.heading); rfl
      rw [← mul_prod_erase _ _ (Finset.mem_toLeft.mp hj)]
      exact mul_le_of_le_one_right (Real.exp_pos (-κ)).le (Finset.prod_le_one (fun i hi=> by cases i; exact (Real.exp_pos _).le; exact zero_le_one) (fun i hi=> hm i))
    ext i'; by_cases hz: (addr F P i).eligible P.threshold U.2
    · rw [Set.indicator_of_mem (show U∈_ from hz)]; simp_rw [Finset.prod_apply]; exact (if_pos hz).symm
    rw [Set.indicator_of_notMem]; exact (if_neg (show ¬ (addr F P i).eligible P.threshold U.2 from hz)).symm; exact hz
  · have hR' := StellarTree.sharp X.patch P.B P.exponent_pos.le hF hW he.capital hp x; let hR:= budget_loosen hR' (sub_le_sub_right (Real.exp_monotone (show StellarTree.keep P.B * γ ≤ γ from mul_le_of_le_one_left hp (StellarTree.keep_range _).2)) 1)
    let b (p):= (F p).val; have hi : Injective b:= Subtype.val_injective.comp F.injective
    refine budget_loosen (budget_mono (budget_scale (Real.exp_pos (-κ)).le (budget_pull b hi hR)) (fun i=>?_) (fun i=> ?_)) he.returns
    · split; · exact mul_nonneg (hh _) (Real.exp_pos _).le
      exact le_rfl
    split
    next h=>
      unfold Ac.roots; dsimp only; rw [if_pos ⟨(F i).property.2.1,h⟩]; apply le_of_eq; change M i*_=Real.exp (-κ) *(Real.exp _* v i)
      unfold M v; ring_nf; rfl
    exact (budget_scale (Real.exp_pos (-κ)).le (budget_pull b hi hR)).1 _

end UniformPays
-- strengthen witness without touching how output supports K.V.We. Need buy Ω slots always.
namespace KLink
variable {Q Q' : BudgetPoint}
structure Last (X : KLink P Y a b Q L B r): Prop where
  spare : ∀ (Ω ι : Type)[Fintype ι]{K:WayK Ω ι G n}, UniformPays Y P K a b → UniformPays L Q (X.carry K) B (r+StellarTree.spare Q.B)
-- .any prefix
lemma Last.back {d':ℝ}{Z:Activities G n}{T:KLink P Y a b Q L B r}{X:KLink Q' Z c d' P Y a b}(h:Last T): Last (together X T):= ⟨fun x z _ _ he=> h.spare _ _ (X.rolled he)⟩ -- `d'` unspecified
lemma earned {T: ℕ ≃ Pellet X}{hp:Mallow.Vapor X d P w}{hr:Payments.Rates P.B A B w κ}: Last (KLink.harvest T hp hr):= ⟨fun Ω ι _ K h=>UniformPays.revenue h hp hr T⟩
lemma collected {μ:ℝ}(V:PathData G)(W:Clip)(α:ℝ) (hp:Vapor X d P w) (he:Payments.Rates P.B A B w κ) : Last (KLink.oven (μ:=μ) V W α hp he):= Last.back earned
end KLink
end YM.Qlocal
