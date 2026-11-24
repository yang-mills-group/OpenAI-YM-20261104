import YM.AllOrder.Rosary.Era
import YM.AllOrder.Burn.Whorl
/-!
# Combined reset with external soft & E records, actual full countable families into LAST merger (mask decisions must survive).
Symbolism separate from budgets at stated ν.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Rosary
open Function Filter Set Lattice Wilson RG Ovens
open AnalyticBridge VerifiedReset Collection Quotes Residual WilsonStartup UVNext.PricedKernels Averaging Geo Progress.DirectedRecipe Extra.Iteration Push.BetaTransport
open Till Burn
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {n : Side} {R : PathData G} {c : Clip} {p : BudgetPoint} {σ C Λ H w : ℝ}
    {X : Listing G n} {v : Collection.Source G n} {ι κ : Type}
-- extend independently
abbrev Ensemble (p:BudgetPoint) (X: Pipes G n) (t:Tap G n) (a b c:ℝ):Prop := Payments.Fittings t X p ∧ (X.pours t).EBound p a ∧
    ∃ u v:ℕ→ℝ,Payments.rooted t u v ∧ Payments.hardCost p X u b ∧ Payments.softCost p X v c
namespace Ensemble
variable {A:Pipes G n}{d:Tap G n}{C' δ μ a b ℓ:ℝ}(h:Ensemble p A d a b δ)
include h
lemma bills : (A.pours d).Valid p a b:=by obtain ⟨he,hA,u,v,hr,hk,-⟩:=h; exact ⟨he.regular,he.support,he.moves,hA,u,fun i=> ⟨hk.1 i,fun U=>(hr i U).1⟩, Payments.drop_reserve p _ hk.1 hk.2⟩
lemma digest (hu: Payments.Rates p.B w b δ μ): Ingredients A d p a w:=by obtain ⟨he,hA,u,v,hr,hk,hl⟩:=h; exact Payments.tender he hA hk hl hr hu
lemma log_paid (U:Config G n): Summable fun i=> d.logarithm i U:= by obtain ⟨-, -, u,v,hr,hk,hl⟩:=h; exact Summable.of_norm_bounded (Activities.summable_charge A.sites hl.1 (Payments.drop_reserve p _ hl.1 hl.2)) fun i=> (hr i U).2
lemma relax {a' b' δ':ℝ}(ha:a≤a')(hb:b≤b')(hd:δ≤δ'): Ensemble p A d a' b' δ':=by obtain ⟨he,hA,u,v,hr,hk,hl⟩:=h; exact ⟨he,Time.E_rises hA ha,u,v,hr,⟨hk.1,fun i=> Cost.enlarge (hk.2 i) hb⟩,⟨hl.1,fun i=> Cost.enlarge (hl.2 i) hd⟩⟩
end Ensemble
structure Herb (G:Gauge) (n:Side) (ι:Type) where
 addr : ι→ RegularAddress n
 values : ι→Pot G n
structure Cane (G:Gauge) (n:Side) (ι:Type) where
 addr : ι→Support n
 wheat : ∀ i,(addr i).Nonempty
 values : ι→Pot G n
namespace Herb
variable (h:Herb G n ι)
local notation "R"=> h.addr
local notation "V"=> h.values
abbrev occG (p : BudgetPoint) (i:ι) := masked p.threshold ((R) i|>.support) (V i)
def teller (p:BudgetPoint)(U:Config G n):=∑' i,(occG h p i) U
abbrev spins:Prop:=∀ (s:Signed)(b:Site n),∃ τ:Equiv.Perm ι, ∀ i,(R (τ i)).site=affine s b (R i).site∧ (R (τ i)).support=(R i).support.image (affine s b) ∧ V (τ i)=V i ∘ pull s b
def Knows (p:BudgetPoint)(c:ℝ):Prop:= h.spins ∧ ∃ u:ι→ℝ,(∀ i, Till.Fairness p (R i|>.site) (R i|>.support) (V i) (u i)) ∧ anchored p R u c
variable {h}
lemma Knows.weakens (H': h.Knows p C) (hh:C≤σ): h.Knows p σ:=by obtain ⟨h,u,w,v⟩:= H'; exact ⟨h,u,w,fun i=> Cost.enlarge (v i) hh⟩
variable {A:Pipes G n}{d:Tap G n}
def pumps (h:Herb G n ι) (τ:ℕ≃ι⊕ℕ) (A:Pipes G n) : Pipes G n:={ A with reg:= Sum.elim h.addr A.reg ∘ τ }
def fluid (h:Herb G n ι) (τ:ℕ≃ι⊕ℕ) (t:Tap G n) : Tap G n:={ t with regular:= Sum.elim h.values t.regular ∘ τ }
local notation "P"=> (A.pours d)
variable {δ K μ:ℝ} (hp:Ensemble p A d H K δ) (hv:h.Knows p C)(τ:ℕ≃ι⊕ℕ)
local notation "X★" => (Pipes.pours (pumps h τ A) (fluid h τ d))
include hp hv
lemma sprout : Ensemble p (pumps h τ A) (fluid h τ d) (C+H) K δ:=by
 obtain ⟨ht,⟨u,h0,hE⟩,hF⟩:=hp; obtain ⟨hh,U,hQ,hM⟩:=hv; let u':ι ⊕ ℕ→ℝ:= Sum.elim U u; let W:ℕ→ℝ:=u'∘ τ
 have he(x:ℕ): Fairness p ((X★).reg x|>.site) ((X★).reg x|>.support) ((X★).E x) (W x):= by
    dsimp only [Pipes.pours,pumps,fluid,W,comp_apply]; cases τ x with
    | inl v' => exact hQ v'
    | inr x' => exact ⟨ht.regular.smooth x', h0 x', ht.regular.at_flat x', fun he f=> ht.regular.vanish x' he _ _ ((LinearJet.isAffine ..).mpr ⟨_,rfl⟩) ((LinearJet.isAffine ..).mpr ⟨_,rfl⟩)⟩
 refine ⟨⟨⟨fun i=>(he i).ready,fun i=>(he i).one,fun i=>(he i).nth⟩,⟨ht.support.sym,ht.support.symtest,ht.support.meas,ht.support.meas_test,ht.support.reads,ht.support.reads_test,ht.support.permit⟩,fun s b=> ?_,ht.visits,ht.steady,ht.looks,ht.reads,ht.carries⟩,⟨W,fun i=>(he i).cap,fun x=> Cost.equiv τ (Cost.sum (f:=fun i=> let x':=Sum.elim h.addr A.reg i; if x'.site=x then p.mass x'.support (u' i) else 0) (hM x) (hE x))⟩,hF⟩
 obtain ⟨q⟩:= ht.moves s b; obtain ⟨r,hr⟩:= hh s b; let f:= Equiv.sumCongr r q.ep; let e':=(τ.trans f).trans τ.symm; have hy i: τ (e' i)= f (τ i):= τ.apply_symm_apply _; let a:ι⊕ℕ→RegularAddress n:= Sum.elim R A.reg; let b':ι⊕ℕ→Pot G n:=Sum.elim V d.regular; have hz i: (a (f i)).site=affine s b (a i).site∧(a (f i)).support=(a i).support.image (affine s b) ∧ b' (f i)=b' i ∘ pull s b:= by
   rcases i with i|i; · exact hr i
   exact ⟨q.reg_site i,q.reg_support i,funext (q.valuesE i)⟩
 refine ⟨⟨e',q.kp,fun i=> ?_,fun i=> ?_, q.forced_support,q.forced_inventory,q.forced_tests,fun i x=> ?_,q.valuesK⟩⟩
 all_goals dsimp only [pumps,fluid,Pipes.pours,comp_apply]
 all_goals first| (exact (hy i).symm ▸ (hz (τ i)).1)| (exact ((hy i).symm ▸ (hz (τ i)).2.1))| (exact ((hy i).symm ▸ congr_fun (hz (τ i)).2.2 x))
lemma sundial (U:Config G n) : (X★).additive p U=h.teller p U+(P).additive p U ∧ Summable (fun i=> h.occG p i U):=by
 let f(x:ι ⊕ ℕ):= x.elim (fun i=> h.occG p i U) (fun i=> (P).regularOccurrence p i U); have hS i:(X★).regularOccurrence p i U=f (τ i):= by
    simp only [Pipes.pours, Activities.regularOccurrence, pumps,fluid,comp_apply]; cases τ i <;> rfl
 have hh : Summable f:= τ.summable_iff.mp ((X★).ESeries (sprout hp hv τ|>.bills)|>.summable U|>.congr hS)
 exact ⟨(by unfold Activities.additive; simp_rw [hS]; rw [τ.tsum_eq f, Summable.tsum_sum (f:=f) (hh.comp_injective Sum.inl_injective) (hh.comp_injective Sum.inr_injective)]; rfl), hh.comp_injective Sum.inl_injective⟩
end Herb
end YM.AllOrder.Rosary
