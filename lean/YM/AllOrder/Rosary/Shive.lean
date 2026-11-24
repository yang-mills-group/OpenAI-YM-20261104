import YM.AllOrder.Rosary.Spoon
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Rosary
open Function Filter Set Lattice Wilson RG Ovens
open AnalyticBridge VerifiedReset Collection Quotes Residual WilsonStartup UVNext.PricedKernels Averaging Geo Progress.DirectedRecipe Extra.Iteration Push.BetaTransport
open Till Burn
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {n : Side} {R : PathData G} {c : Clip} {p : BudgetPoint} {σ C Λ H w : ℝ}
    {X : Listing G n} {v : Collection.Source G n} {ι κ : Type}
namespace Cane
variable {h:Cane G n ι}
def haul (h:Cane G n ι)(τ:ℕ≃ι⊕ℕ)(A:Pipes G n): Pipes G n:={ A with
    softer:= Sum.elim h.addr A.softer ∘ τ
    sites:=fun i=>by dsimp only [Function.comp_apply]; cases τ i with | inl x=> exact h.wheat x| inr x=> exact A.sites x }
def sap (h:Cane G n ι)(τ:ℕ≃ι⊕ℕ)(t:Tap G n): Tap G n:= { t with logarithm:= Sum.elim h.values t.logarithm ∘ τ }
local notation "S"=>h.addr
local notation "V"=>h.values
-- function before h to include h
abbrev wiggles:Prop:=∀ (t:Signed)(b:Site n), ∃ τ:Equiv.Perm ι, ∀ i,S (τ i)=(S i).image (affine t b)∧V (τ i)=V i∘pull t b
variable (h) in
abbrev Ready (p:BudgetPoint)(u:ℝ):Prop:= wiggles (h:=h)∧(∀ i:ι,GaugeInvariant (V i)∧ UsesFinal p.threshold (S i) (V i) ∧ Measurable (V i)∧∀ U,V i U≠0→¬ Healthy p.threshold (S i) U)∧(∃ v:ι→ℝ,(∀ i,∀ U, ‖V i U‖≤v i)∧ Ac.Hit S p.B v (p.supportExponent+1) u)
variable {A:Pipes G n}{d:Tap G n}
variable {δ K μ:ℝ} (hp:Ensemble p A d H K δ) (hv:h.Ready p C)(τ:ℕ≃ι⊕ℕ)
local notation "T"=> haul h τ A
local notation "B"=> sap h τ d
local notation "X★"=> Pipes.pours (T) (B)
include hp hv
lemma out (u:Config G n) : Ensemble p (T) (B) H K (C+δ):=by
 obtain ⟨ht,hE,H'⟩:=hp; obtain ⟨hh,hQ,y,hu,hM⟩:=hv; have he i: GaugeInvariant ((B).logarithm i) ∧ UsesFinal p.threshold ((T).softer i) ((B).logarithm i) ∧ Measurable ((B).logarithm i) ∧ (∀ U,(B).logarithm i U≠0→ ¬ Healthy p.threshold ((T).softer i) U):=by
   simp only [sap,haul,Function.comp_apply]; cases τ i with
   | inl x=> exact hQ x
   | inr x=> exact ⟨ht.steady x,ht.looks x,ht.reads x,ht.visits x⟩
 refine ⟨⟨ht.regular,ht.support,ht.moves,fun i=>(he i).2.2.2,fun i=>(he i).1,fun i=>(he i).2.1,fun i=>(he i).2.2.1,fun s b=>?_⟩, hE,?_⟩
 · obtain ⟨t,hr⟩:= hh s b; obtain ⟨r,hW,hc⟩:=ht.carries s b; let f:=Equiv.sumCongr t r; let e:=(τ.trans f).trans τ.symm; have hv i: τ (e i)= f (τ i):= τ.apply_symm_apply _; refine ⟨e,fun i=> ?_,fun U i=> ?_⟩
   · simp only [haul,comp_apply,hv,f]; cases τ i with | inl i=>exact (hr i).1 | inr i=>exact hW i
   simp only [sap,comp_apply,hv,f]; cases τ i with | inl i=>exact congr_fun (hr i).2 U| inr i=>exact hc U i
 obtain ⟨a,b,ha,hk,hs⟩:=H'; let q:=Sum.elim y b ∘ τ; have hy i U: ‖(B).logarithm i U‖ ≤ q i:= by dsimp only [q,sap,comp_apply]; cases τ i with | inl x=>exact hu x U | inr x=>exact (ha x U).2
 exact ⟨a,q,fun i U=> ⟨(ha i U).1, hy i U⟩,hk,fun i=>(norm_nonneg _).trans (hy i u),fun x=> Cost.equiv τ (Cost.sum (f:=fun i:ι⊕ℕ=> let z':Support n:=Sum.elim S A.softer i; if x∈z' then (Sum.elim y b i)*Real.exp ((p.supportExponent+1)*coverNumber p.B z') else 0) (hM x) (hs.2 x))⟩
lemma mellow (U:Config G n): (∑' k,(B).logarithm k U)=(∑' i,V i U)+∑' i,d.logarithm i U:= by
 let g'(i:ι⊕ℕ):=Sum.elim V d.logarithm i U; have hv:= (out hp hv τ U).log_paid U; have he:Summable g':=τ.summable_iff.mp hv; change ∑' i,g' (τ i)=_; exact (Equiv.tsum_eq τ g').trans (Summable.tsum_sum (f:=g') (he.comp_injective Sum.inl_injective) (he.comp_injective Sum.inr_injective))
end Cane
end YM.AllOrder.Rosary
