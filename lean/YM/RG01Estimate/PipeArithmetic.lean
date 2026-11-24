import YM.RG01Estimate.LeasePipe
/-! # evaluator algebra for Δ. The discrepancy quantum, deliberately not hiding direct-scalar. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG01Estimate.Censor.Fresco
open Function Filter Set Lattice Wilson RG Progress.DirectedRecipe AnalyticBridge VerifiedReset Collection Averaging Ovens Ovens.Pipes
   Payments Extra.Iteration Pilgrim Push.BetaTransport
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {G:Gauge}{n:Side}{p:BudgetPoint}{hn:20<n.val}(Q:Pilgrim p n hn)
   {L:Pipes G n}{X: Listing G n}{a:Collection.Source G n}{e v: Collection.Source G n} {d c b : Tap G n}
   {δ w ε γ τ σ H C Λ δ' β Δα Δ' : ℝ}{R:PathData G}{c':Clip}

section jets
variable (g:G.Simple) (h:Local X p v H w) (hw:Local X p a δ' δ)
include g h hw
lemma polarized_gain (he : e.logRead=v.logRead-a.logRead) : delta (X.read e)=delta (X.read v)-delta (X.read a):=by
   unfold Averaging.delta Averaging.total; rw [← (h.projects.seriesAt g ..).tsum_sub (hw.projects.seriesAt g ..)]; apply tsum_congr; intro i
   simp only [censusAt,Listing.read]; split
   · rw [he,Pi.sub_apply, projection_sub (X.reg i) (h.smooth i) (hw.smooth i)]
   simp

omit g in
lemma regular_sub (S:PathData G)(C:Clip)(α v₀ q₀:ℝ) (he:e.logRead=v.logRead-a.logRead) :
    (fill X S C p v α v₀).regular = (fill X S C p a α q₀).regular + (fill X S C p e 0 (v₀-q₀)).regular:=by
    ext i U
    simp only [fill,comp_apply,Pi.add_apply]
    rcases numbering (EKey n) i with i|⟨x,y⟩|⟨x,y⟩
    · change Residual.rebate (X.reg i) (v.logRead i) U= _ + Residual.rebate (X.reg i) (e.logRead i) U
      rw [he,Pi.sub_apply,(Residual.label_sub (X.reg i) (v.logRead i) 0 (a.logRead i) p (h.smooth i) (hw.smooth i)).1]
      simp only [Pi.sub_apply,archive,Sum.elim_inl]; ring
    · change y.fresh S C 0 (factor*v₀) _= y.fresh S C 0 (factor*q₀) _ + y.fresh S C 0 _ _; unfold Low.fresh; ring
    change y.fresh S 0 (factor*α) _ _=y.fresh S 0 _ (factor*q₀) _ + y.fresh S 0 _ _ _; unfold High.fresh; ring

omit hw in
lemma residual (U:Config G n) (hn:20<n.val)(hc:R.Bounds c' σ C Λ)(hC: WilsonStartup.Decent c' p)(hs:Geo.Width p c' σ) (α Δ':ℝ):
    let t:= fill X R c' p v α Δ'; let Y:= shelves X R p; let T:= trunk R c' p Y t (β+α+Δ') (vac v τ)
    T.exponent U + (∑' i,t.logarithm i U) + (Δ'-delta (X.read v))* (∑ o:Site n,heads p o U)= (frozen X R c' p v β τ).exponent U-α*receipt R c' p U:=by
    intro t Y T
    change vac v τ*UVNext.CouplingReset.sites n-R.inChannels c' p (β+α+Δ') U-_+_+_= (τ*UVNext.CouplingReset.sites n -R.inChannels c' p β U-_) - _
    rw [vac,sub_mul,div_mul_cancel₀ _ (UVNext.CouplingReset.sites_pos n).ne', channels_split U (β+α+Δ'), channels_split U β]
    have hh:= h.first_split g hn U
    have he:=h.additive g hc α Δ' U; have ht:=h.throw_sum g hc hC hs α Δ' U
    have hz:= path_split hc hs hC α Δ' U
    dsimp only [T,trunk,t,Y,branch,receipt,frozen]
    linarith only [hh,he,ht,hz]
end jets

-- Tap algebra
set_option maxHeartbeats 500000 in
lemma assigned_gain (Δ : ℝ) (Y:Config G n) (hd:(L.pours d).EBound p ε)(he:(L.pours c).EBound p γ)
    (hb:b.regular=d.regular+c.regular)(hx:Summable (fun i=> b.logarithm i Y)):
    ((L.pours b).additive p Y) + (∑' i, (pour Q Δ d c b).logarithm i Y) = (((combine Q L).pours (pour Q Δ d c b)).additive p Y) + (∑' i,b.logarithm i Y) + Δ*(∑ o,heads p o Y):=by
    let N:= numbering (Main n); let W:= numbering (Soft n)
    let f i:= masked p.threshold (allot L.reg L.reg Q.X Q.anchored i).support (ink d.regular c.regular (tea G Δ) i) Y
    have hp (i : ℕ): (L.pours b).regularOccurrence p i Y=f (.inl i)+f (.inr (.inl i)):=by
        unfold f; dsimp only [ink,allot,Sum.elim_inl,Sum.elim_inr]; unfold Activities.regularOccurrence; simp only [pours,hb,Pi.add_apply]; by_cases h:Healthy p.threshold (L.reg i).support Y
        · rw [masked_eq _ _ _ _ h,masked_eq _ _ _ _ h,masked_eq _ _ _ _ h]; rfl
        rw [masked_ne _ _ _ _ h,masked_ne _ _ _ _ h,masked_ne _ _ _ _ h,add_zero]
    unfold Activities.additive
    change (∑' i,(L.pours b).regularOccurrence p i Y) + (∑' i, iced Q Δ b (W i) Y) = (∑' i, f (N i)) + (∑'i,b.logarithm i Y) + _
    have hQ:Summable (f ∘ Sum.inl):= YM.Next.Rank.Alarm.ante p _ hd _
    have hE:Summable (f ∘ Sum.inr ∘ Sum.inl):= YM.Next.Rank.Alarm.ante p _ he _
    rw [show (∑' i, iced Q Δ b (W i) Y)=∑' i, iced Q Δ b i Y from W.tsum_eq (fun i=> iced Q Δ b i Y), hx.tsum_sum Summable.of_finite]
    rw [N.tsum_eq f, hQ.tsum_sum (Summable.sum (f:=f ∘ Sum.inr) hE Summable.of_finite),hE.tsum_sum Summable.of_finite]
    simp_rw [hp]
    have hv:= hQ.tsum_add hE; simp only [Function.comp_apply] at hv; rw [hv]; simp_rw [tsum_fintype (β:=Seat n)] -- names check
    dsimp only [f,allot,ink,iced,Sum.elim_inr,Sum.elim_inl,Seat.reg]
    linarith only [Q.head_pay G Δ Y]
end YM.RG01Estimate.Censor.Fresco
