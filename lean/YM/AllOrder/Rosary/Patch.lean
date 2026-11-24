import YM.AllOrder.Rosary.Lumen
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Rosary
open Function Filter Set Lattice Wilson RG Ovens
open AnalyticBridge VerifiedReset Collection Quotes Residual WilsonStartup UVNext.PricedKernels Averaging Geo Progress.DirectedRecipe Extra.Iteration Push.BetaTransport
open Till Burn
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {n : Side} {R : PathData G} {c : Clip} {p : BudgetPoint} {σ C Λ H w : ℝ}
    {X : Listing G n} {v : Collection.Source G n} {ι κ : Type}
/- Can use virtual ledger compare β on all good, with exact but not clone labels. Keep affine calibration.Hyp bought later. -/
namespace Herb
variable {t:Herb G n ι}
variable (t) in
abbrev Proto (p:BudgetPoint)(C:ℝ):Prop:= t.spins ∧ ∃ (u:ι→ℝ),
    (∀ i, p.Regular (t.addr i).support (t.values i)∧p.supBounds (t.addr i).site (t.addr i).support (t.values i) (u i))∧ Quotes.early p t.addr u C
variable (τ:ℕ≃ι⊕ℕ)
def deck (t:Herb G n ι)(A:Listing G n): Listing G n:= { A with reg:= Sum.elim t.addr A.reg ∘ τ }
def ink (t:Herb G n ι)(v:Collection.Source G n): Collection.Source G n:={ v with logRead:=Sum.elim t.values v.logRead ∘ τ }
local notation "R"=> deck τ t X
local notation "A"=> ink τ t v
local notation "Ω"=> Listing.read (R) (A)
variable (h:Collection.Local X p v H w) (g:G.Simple)(hb:t.Proto p C)
include h hb
lemma why : Collection.Local (R) p (A) (C+H) w:=by
 obtain ⟨he,u,hv,hy⟩:= hb; obtain ⟨b,h0,hB⟩:= h.cheap; let f:= Sum.elim u b; have hh i : p.Regular (((R).reg i).support) ((A).logRead i) ∧ p.supBounds (((R).reg i).site) (((R).reg i).support) ((A).logRead i) (f (τ i)):= by dsimp only [deck,ink,comp_apply]; cases τ i with| inl j=>exact hv j| inr j=> exact ⟨h.smooth j,h0 j⟩
 refine ⟨fun i=>(hh i).1,⟨h.family.sym,h.family.symtest,h.family.meas,h.family.meas_test,h.family.reads,h.family.reads_test,h.family.permit⟩,fun s b=> ?_,⟨f ∘ τ,fun i=>(hh i).2,fun x=> Cost.equiv τ (Cost.sum (f:=fun i : ι⊕ℕ=> let d:= Sum.elim t.addr X.reg i; if d.site=x then f i*Real.exp (preExponent p*coverNumber p.B d.support) else 0) (hy x) (hB x)) ⟩, h.expensive⟩
 obtain ⟨Y⟩:= h.transforms s b; obtain ⟨q,hR⟩:= he s b; let f':= Equiv.sumCongr q Y.ep; let k:=(τ.trans f').trans τ.symm; have he i: τ (k i)= f' (τ i):= τ.apply_symm_apply _; refine ⟨⟨k,Y.kp,fun i=> ?_,fun i=>?_,Y.forced_support,Y.forced_inventory,Y.forced_tests,fun i U=>?_,Y.valuesK⟩⟩
 all_goals (simp only [deck,ink,Listing.read,comp_apply,he]; cases τ i with
   | inl i=> first| exact (hR i).1| exact (hR i).2.1| exact congr_fun (hR i).2.2 _
   | inr i=> first| exact Y.reg_site i| exact Y.reg_support i| exact Y.valuesE i U)
lemma sums (U:Config G n) : Summable (fun i=>(X.read v).regularOccurrence p i U):=by
 obtain ⟨f,hf,hQ⟩:= (X.read v).E_total h.unweighted; refine Summable.of_norm_bounded hf ?_; intro i; unfold Activities.regularOccurrence; by_cases hp: Healthy p.threshold (((X.read v).reg i).support) U; · rw [masked_eq _ _ _ _ hp]; exact (hQ i).2 U hp [] (by simp) (by simp)
 rw [masked_ne _ _ _ _ hp,norm_zero]; exact (hQ i).1
lemma showS (U:Config G n) : (Ω).additive p U= t.teller p U+(X.read v).additive p U∧ Summable fun i=> t.occG p i U:= by
 let f:= Sum.elim (fun i=> t.occG p i U) (fun i=>(X.read v).regularOccurrence p i U); have he i:(Ω).regularOccurrence p i U=f (τ i):=by dsimp only [Listing.read, deck,ink,comp_apply,Activities.regularOccurrence]; cases τ i <;> rfl
 have hℓ:=sums (why τ h hb) hb U; have hT:Summable f:=τ.summable_iff.mp (hℓ.congr he); refine ⟨?_, hT.comp_injective Sum.inl_injective⟩; unfold Activities.additive; simp_rw [he]; rw [τ.tsum_eq f]; exact Summable.tsum_sum (f:=f) (hT.comp_injective Sum.inl_injective) (hT.comp_injective Sum.inr_injective)
include g
variable (t)
def shofar (i:ι):= if (t.addr i).site=0 then projection (t.addr i) (t.values i) axes01 axes01 else 0
abbrev mu:=∑' i,t.shofar i
variable {t}
omit h hb g in
private lemma funnelS (τ:ℕ≃ι⊕ℕ)(f:ℕ→ℝ)(a:ι→ℝ)(b:ℕ→ℝ)(h:∀ i,f i=Sum.elim a b (τ i))(H:Summable f) : (∑' i,f i)=(∑' i,a i)+ (∑' i,b i) ∧ Summable a:=by 
 let v':= Sum.elim a b; have ht:Summable v':=τ.summable_iff.mp (H.congr h); exact ⟨(tsum_congr h).trans ((τ.tsum_eq v').trans (Summable.tsum_sum (f:=v') (ht.comp_injective (@Sum.inl_injective ι ℕ)) (ht.comp_injective (@Sum.inr_injective ι ℕ)))), ht.comp_injective (@Sum.inl_injective ι ℕ)⟩
lemma pull_δ : delta (Ω)=mu t+delta (X.read v) ∧ Summable t.shofar:= by
 let f':= Sum.elim t.shofar (censusAt (X.read v) 0 axes01 axes01); have he i:censusAt Ω 0 axes01 axes01 i= f' (τ i):= by simp only [censusAt, Listing.read,deck,ink,comp_apply]; cases τ i <;> rfl
 exact funnelS τ (censusAt Ω 0 axes01 axes01) t.shofar (censusAt (X.read v) 0 axes01 axes01) he ((why τ h hb).projects.seriesAt g axes01 axes01 0)
omit h hb g
lemma still (h:∀ i,Nonwrapping ((t.addr i).support) (t.addr i).site → ∀ x:LinearJet G,logHessian (t.values i) (x.field (t.addr i).site) (x.field (t.addr i).site)=0): mu t=0:= by
   have h0 i:t.shofar i=0:= by
     unfold shofar; split; unfold projection; split_ifs with hp; exact h i (fun x hx=> hp x (Finset.mem_union_left _ hx)) _; rfl; rfl
   unfold mu; simp [h0]
end Herb
end YM.AllOrder.Rosary
