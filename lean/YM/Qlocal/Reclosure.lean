import YM.Qlocal.Projection
/-!
Transitions on the K ledger (with REAL masking) that allow the Step Lantern to
reuse the *same* vacuum material, and transport the costs & switch equations
simultaneously. Only real switches in here, supported and uniform, not yet
normalized. This version handles the mask/path changes made in reexpressing the
**vacuum**. These are the steps which otherwise threaten to destroy the old
marked regular/forced bounds; they must leave the marked outputs aligned on
exactly the same carrier. (When making mask changes in the marks as well, one
needs additional steps. Keyword `CapL` e.g. in another branch.)

Adapts and combines bounds from Merge.Motion, Mallow. Some of the method ported
from `Capstan` in `Comparison/Remainder/Medallion` (on another branch).
This states also the using/mixing rule and joins the ticket for the full test
family across the whole route, including padding and packing. Keeps budgets
at +1 or +1+1, e.g. when packing twice, BEFORE shrinking to `p`. We
have to *buy* these. Does NOT infer reclosure just from compatibility of the E
kernels, mask equivalence, nor equality of the evaluated gas, not even equality
for all fields.
-/
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

lemma relax (z:UniformPays L P K c r) (he:c ≤ B) (hh:a ≤ r): UniformPays L P K B a:=by
   obtain ⟨f,h₀,hH⟩:=z.credit
   refine ⟨z.term,z.licensed,f,h₀,fun i=> budget_loosen (budget_mono (hH i) (fun j=>?_) (fun j=>?_)) he⟩
   · split; exact mul_nonneg (Paid.rocket (h₀ _)) (Real.exp_pos _).le; exact le_rfl
   split; exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right hh (by positivity))) (h₀ _|>.rocket); exact le_rfl

variable {P' : BudgetPoint}
lemma geom (z:UniformPays L P K c r) (hB:P.B=P'.B) (ht:P.threshold=P'.threshold)
    (he:Y.forced=L.forced) (hK:Y.K=L.K) : UniformPays Y P' K c r:=by
  rcases P with ⟨ ⟩; rcases P' with ⟨ ⟩; rcases Y with ⟨ ⟩; rcases L with ⟨ ⟩; dsimp at he hK hB ht; cases hB; cases ht; cases he; cases hK
  refine ⟨z.term, fun x t j ht=>?_,z.credit⟩; obtain ⟨a,b,c,d,f,g,l⟩:= z.licensed x t j ht; exact ⟨a,b,c,d,f,g,l⟩

abbrev station (X:Pipes G n)(K:WayK Ω ι G n) (u:Ω)(t:ℝ)(i:Finset ι):= stuff (upK X) (K u t i)
local notation "K↑" => station X K
variable (hk : UniformPays (X.pours d) P K B a)

lemma widen (h : UniformPays (X.pours d) P K B a) :
    UniformPays ((drawer G n).pours (Rack.widen X d)) P (station X K) B a:=by
  refine ⟨fun u j=> ?_,fun u v j hv=>?_,?_⟩
  · unfold station; rw [h.term]; rfl
  · apply (Rack.preserves X (spice d (K u v j)) P).forced_family (?_) (fun _ _ _ => Iff.rfl) (fun _ => MeasurableSet.univ) (fun _ _ _ _ _ => rfl)
    exact h.licensed u v j hv
  obtain ⟨f,hv,hB⟩:=h.credit; let i:=upK X; refine ⟨stuff i f, fun k=> ?_, fun x=> ?_⟩
  · by_cases ht:k∈Set.range i
    · obtain ⟨k,rfl⟩:=ht; unfold station; simp_rw [i,stuffed]; exact hv k
    rw [blank _ _ ht];unfold i at ht; unfold station; simp_rw [blank _ _ ht];exact paidZero (ι:=ι) (U:=Ω×Config G n)
  refine transfer_budget i ?_ ?_ (hB x)
  · intro z; simp only [pours,i,stuffed]; rw [hard_up]; rfl
  intro z hz; split; rw [blank _ f hz, zero_mul]; rfl

abbrev joints (P:BudgetPoint)(d:Tap G n)(F : ℕ ≃ Pellet X)(K: WayK Ω ι G n)(u : Ω)(t:ℝ)(i:Finset ι):=
   solid F P (spice d (K u t i))

/- The price on the entire family at once. -/
private def primaryP (p q : ℕ → ℝ) (κ : ℝ) : Ovens.Label → ℝ:= Sum.elim (fun i=> Real.exp κ * p i) (fun i=> 2*q i)
private def mild (κ : ℝ)(i:Ovens.Label) := Sum.elim (fun _=> Real.exp (-κ)) (fun _=>1) i
private theorem scaleInk {ι : Type*}(p : ι→Support n)(b : ι→ℝ){P : BudgetPoint} (hh:Ac.Hit p P.B b (P.supportExponent+1) v)(ha:0≤a): Ac.Hit p P.B (fun i=> a*b i) (P.supportExponent+1) (a*v):=by
   intro i; convert! budget_scale ha (hh i) using 1; ext j; by_cases hk:i∈p j <;> simp [hk,mul_assoc]
variable (h : UniformPays (X.pours d) P K B (P.supportExponent+1))(hp: Vapor X d P w)(he: Payments.Rates P.B A B w κ)
include h hp he
private lemma wallets : ∃ f : Ovens.Label → ℝ,(∀ i,0≤ f i) ∧ Ac.Hit X.patch P.B f (P.supportExponent+1) (Payments.inflation B w κ) ∧
    ∀ i, Paid (fun U : Ω×Config G n=> fun t j=>reach (spice d (K U.1 t j)) i U.2) (mild κ i*f i):= by
  obtain ⟨f,hP,hH⟩:= h.credit
  have hf i:= (hP i).rocket; obtain ⟨v,hv,hg⟩:= hp.funds
  refine ⟨primaryP f v κ,fun i=>?_, ?_,fun i=> ?_⟩
  · cases i
    · exact mul_nonneg (Real.exp_pos _).le (hf _)
    exact mul_nonneg zero_le_two (hv.1 _)
  · exact Labels.together _ _ _ (scaleInk _ _ (P:=P) hH (Real.exp_pos κ).le) (scaleInk _ _ (P:=P) hv.2 (show (0:ℝ)≤2 by norm_num))
  rcases i with i|i; simp only [primaryP,mild, Sum.elim_inl,Real.exp_neg,inv_mul_cancel_left₀ (Real.exp_pos κ).ne']; exact hP i
  simp only [primaryP,mild,Sum.elim_inr,one_mul]; refine Switch.constant (reach d (Sum.inr i) ∘ Prod.snd) (mul_nonneg zero_le_two (hv.1 i)) ?_
  intro U
  change |Real.exp (d.logarithm i U.2)-1|≤2*v i
  apply (Real.abs_exp_sub_one_le ?_).trans (mul_le_mul_of_nonneg_left (hg i U.2) zero_le_two); obtain ⟨p,hp⟩:= X.sites i
  have he' := Samples.one_le_quote (Payments.drop_reserve P _ hv.1 hv.2 p) i; rw [if_pos hp] at he'
  exact (hg i U.2).trans ((P.loMass _ _ (hv.1 i)).trans (he'.trans he.soft_limit))
lemma harvest (F : ℕ ≃ Pellet X) : UniformPays (fused F P d) P (joints P d F K) A P.supportExponent:=by
  constructor
  · intro u j; rw [joints,show spice d (K u 0 j)=d by rw [h.term]; rfl]; rfl
  · intro u t j ht; obtain ⟨h,h₁,h₂,h₃,h₄,h₅,h₆⟩:= Passage.fused_forcedFamily F (kitch (h.project u) hp t ht j)
    exact ⟨h,h₁,h₂,h₃,h₄,h₅,h₆⟩
  obtain ⟨f,hF,hW,hK⟩:=wallets h hp he
  let v i:= ∏ j∈ (F i).val, f j; let M i:= Real.exp (-κ)*v i; let γ:=Payments.inflation B w κ
  have hp : 0≤ γ:= add_nonneg (mul_nonneg (Real.exp_pos _).le he.hard) (mul_nonneg zero_le_two he.soft)
  have hv i :0≤ v i:= prod_nonneg fun j _=> hF _; have hh i:0≤ M i:=mul_nonneg (Real.exp_pos _).le (hv i)
  refine ⟨M,fun i=>?_,fun x=>?_⟩
  · let f':= ∏ j∈(F i).val,fun U:Ω ×Config G n=> fun t i'=>reach (spice d (K U.1 t i')) j U.2
    have hg:= Paid.prod (F i).val _ _ (fun j (_ : j∈(F i).val)=> hK j)
    refine Paid.congr ((Paid.gate (X:={U:Ω×Config G n|(addr F P i).eligible P.threshold U.2}) (hg.weaken ?_))) (fun U t ht=> ?_)
    · rw [prod_mul_distrib]; unfold M v; apply mul_le_mul_of_nonneg_right _ (hv _)
      obtain ⟨j,hj⟩:= (F i).property.1
      have hm (i : Ovens.Label):mild κ i≤1:=by cases i; exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr he.heading); rfl
      rw [← mul_prod_erase _ _ (Finset.mem_toLeft.mp hj)]
      exact mul_le_of_le_one_right (Real.exp_pos (-κ)).le (Finset.prod_le_one (fun i hi=> by cases i; exact (Real.exp_pos _).le; exact zero_le_one) (fun i hi=> hm i))
    ext i'; by_cases hz: (addr F P i).eligible P.threshold U.2
    · rw [Set.indicator_of_mem (show U∈_ from hz)]; simp_rw [Finset.prod_apply]; exact (if_pos hz).symm
    rw [Set.indicator_of_notMem]; exact (if_neg (show ¬ (addr F P i).eligible P.threshold U.2 from hz)).symm; exact hz
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

end UniformPays

open UniformPays
/-- Verifiable ticket, BEFORE any test or set of marks. Covers maybe-repeated Ovens
packings after patch or hull changes; a *data* receipt to allow additional transport
(later marks proof needs algebra with the chosen masks). `geom` also subsumes harmless
relaxing or retiering reserves; B and threshold must be IDENTICAL. The `S` and `X`
passed to the main RGStep are held fixed. -/
inductive KLink {G:Gauge} {n:Side} : BudgetPoint→Activities G n→ℝ→ℝ→BudgetPoint→Activities G n→ℝ→ℝ→ Type
 | geom {B P:BudgetPoint} {X Y:Activities G n} {r w p q:ℝ} (h:P.B=B.B)(he:P.threshold=B.threshold)
       (hk:X.K=Y.K)(hr:X.forced=Y.forced)(hp:r ≤ p)(ha:q ≤ w) : KLink P X r w B Y p q
 | widen {P:BudgetPoint} (X:Pipes G n)(d:Tap G n) (r q:ℝ) : KLink P (X.pours d) r q P ((drawer G n).pours (Rack.widen X d)) r q
 | harvest {P:BudgetPoint} {X:Pipes G n} {d:Tap G n} {A B w κ:ℝ} (F:ℕ≃ Pellet X)
     (hv: Vapor X d P w)(hr: Payments.Rates P.B A B w κ) :
       KLink P (X.pours d) B (P.supportExponent+1) P (fused F P d) A P.supportExponent
 | together {P Q W:BudgetPoint} {Y X Z:Activities G n} {a b r q u v:ℝ} (h: KLink P Y a b Q X r q)(hw: KLink Q X r q W Z u v): KLink P Y a b W Z u v

namespace KLink

variable {D₀ : BudgetPoint}

variable (Z : KLink P Y a b D₀ L v w) 
abbrev SameFoot (Z:Activities G n)(Q Q': BudgetPoint)(L:Activities G n):Prop := Q.threshold=Q'.threshold ∧ Q.B=Q'.B ∧ Z.forced=L.forced
noncomputable def carry {G : Gauge} {n : Side} {P Q:BudgetPoint} {X Y:Activities G n} {a b v w:ℝ} (H:KLink (G:=G) (n:=n) P X a b Q Y v w)
    (K: WayK Ω ι G n) : WayK Ω ι G n:=
    match H with
    | .geom .. => K
    | .widen X .. => station X K
    | @KLink.harvest _ _ P X d A B w κ F hv hr => joints P d F K
    | .together u v => v.carry (u.carry K)
noncomputable def levy {G : Gauge} {n : Side} {P Q:BudgetPoint} {X Y:Activities G n} {a b v w:ℝ} (H:KLink (G:=G) (n:=n) P X a b Q Y v w)(U:Config G n) : ℝ:=
    match H with
    | .geom .. => 1
    | .widen .. => 1
    | @KLink.harvest _ _ P X d A B w κ F hv hr => Real.exp (∑' i,d.logarithm i U)
    | .together u v => u.levy U * v.levy U

include Z
lemma toll_positive (U:Config G n): 0< Z.levy U:= by
 induction Z with
 | geom => exact zero_lt_one
 | widen => exact zero_lt_one
 | harvest => exact Real.exp_pos _
 | together _ _ hx hy => exact mul_pos hx hy

theorem rolled (hk:UniformPays Y P K a b) : UniformPays L D₀ (Z.carry K) v w:= by
 induction Z generalizing K with
 | geom hx hv he hy ht hg => exact (hk.geom hx hv hy.symm he.symm).relax ht hg
 | widen => exact hk.widen
 | harvest F hf hv => exact hk.harvest hf hv F
 | together k j hk0 hk1 => exact hk1 (hk0 hk)
omit [Fintype ι] in
lemma addresses (x:Ω)(i:ι)(u:Site n) (hr:Hush i u (fun j=>(Y.forced j).support) (K x)) : Hush i u (fun j=> (L.forced j).support) (Z.carry K x):= by
 induction Z generalizing K with
 | geom hx hv he hg ht hγ => rw [← hg]; exact hr
 | widen => exact quiet_up i u hr -- order?
 | harvest F hf hv => exact quiet_fusion i u hr F
 | together k j hx hv => exact hv (hx hr)

omit Z
private lemma unchanged {D:BudgetPoint} (hp:Y.forced=L.forced)(ht:P.threshold=D.threshold)(u : Code G n) (U:Config G n): (black Y u).gas P U=(black L u).gas D U:=by
     cases Y; cases L; cases D; cases P; dsimp at hp ht; cases ht; cases hp; rfl
include Z
lemma itinerary (hk: UniformPays Y P K a b) (x:Ω) (t:ℝ) (h:t∈Icc (0:ℝ) 1) (s:Finset ι) (U:Config G n):
  (black L ((Z.carry K) x t s)).gas D₀ U= (black Y (K x t s)).gas P U* Z.levy U:= by
  induction Z generalizing K with
  | geom _ ht _ he => rw [levy,mul_one, unchanged he ht]; rfl
  | widen X d r q => rw [levy,mul_one]; exact congr_fun ((Rack.preserves X (spice d (K x t s)) _).same_gas) U
  | harvest F hF hv => exact (Passage.gathered (F:=F) (kitch (hk.project x) hF t h s) U).tsum_eq
  | together k j hx hv => dsimp only [carry,levy]; rw [hv (k.rolled hk), hx hk, mul_assoc] -- learn syntax via trace
omit Z
noncomputable def oven {μ:ℝ}(V:PathData G)(W:Clip)(α:ℝ) (hp:Vapor X d P w) (he:Payments.Rates P.B A B w κ):
     KLink P (X.pours d) B (P.supportExponent+1) P (finish V W P X d α μ).activities A P.supportExponent:=
     (.widen X d _ _ : KLink P (X.pours d) B (P.supportExponent+1) P ((drawer G n).pours (Rack.widen X d)) B _).together (KLink.harvest _ (shown hp) he)

end KLink

namespace SwitchStep

variable {c f : Side} {S:StepData c f} {R:Rep G f}{J:Type} {D:Ω→ι→ Lotus.Leaf R}
    {L:Activities G c}{L':Rep G c}{K: WayK Ω ι G c}{f₀:Config G c→ℝ} {g:ι→ℝ}
    {𝕃:Ω→J→ Config G c → Ways ι}(h : SwitchStep D S g f₀ L P K 𝕃)
    (he:UniformPays L P K A a) (Z:KLink P L A a L'.p L'.activities B w)

include h he
lemma finish_into
    (hpush : L'.eval = S.push R.beta R.eval)
    (hL : ∀ U, L'.eval U ≠ 0) :
    SwitchStep D S g (Real.exp ∘ L'.exponent) L'.activities L'.p (Z.carry K) 𝕃:= by
  refine ⟨fun x U t ht s=>?_,h.baseL,(Z.rolled he).term⟩
  have ht0 : L'.activities.gas L'.p U= L.gas P U* Z.levy U := by
       have h:=Z.itinerary he x 0 ⟨le_rfl,zero_le_one⟩ ∅ U; rw [(Z.rolled he).term, he.term] at h; exact h
  have hp : f₀ U * L.gas P U = Real.exp (L'.exponent U) * L'.activities.gas L'.p U :=
       (h.unmarked x U).symm.trans (congr_fun hpush.symm U) -- evaluate eval addr
  rw [ht0] at hp -- scalar uncertainty exact, no boundary tricks
  have hP : L.gas P U ≠ 0:= by intro hz; apply hL; rw [Rep.eval,ht0,hz]; ring
  have he : f₀ U = Real.exp (L'.exponent U) * Z.levy U:= by
    apply mul_right_cancel₀ hP; rw [hp]; ring
  rw [h.all x U t ht s, Z.itinerary (by assumption), he]
  · unfold Function.comp; ring
  exact ht
end SwitchStep
end YM.Qlocal
