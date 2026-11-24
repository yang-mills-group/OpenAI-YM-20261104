import YM.Juniper.Cinch.Pillow
set_option autoImplicit false
noncomputable section
namespace YM.Juniper.Cinch
open Function Filter Metric Lattice Wilson RG PhysicalNext PhysicalNext.Repeat
open Push Push.AbsoluteSums AnalyticBridge VerifiedReset Collection Averaging
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G: Gauge}{c:Side}{X:Support c}{W:BudgetPoint}
/-!
# Strong Winding shift of β with PRE envelope and required aperture

THIS fixes Cart ambiguity! Any version earning the precursor Same β-in and
term bounds can now be used in next steps for the real β trajectory, not
assuming that differing nonlinear reps have the same β in their own
extractions. This is different when they use OTHER PathData and other
normalization conventions. Pre<- Cart both. Strong χ. Transit masks Point.
 -/
open Quotes Finset Ovens Ovens.Pipes Progress.DirectedRecipe Payments Further.LogJets Pressure
open Extra.Iteration Song
set_option quotPrecheck false
variable {X:Pipes G c}{A B:Tap G c}{δ ε b v w τ σ t u : ℝ}(T:Pylon W c)
local notation "N"=> badge c
section lamp
variable {q:ℕ→ℝ}
lemma splitE (t:ℝ)(h:(X.pours A).EBound W b)(U:Config G c): ((adobe X T).pours (flint T t A)).additive W U=(X.pours A).additive W U + ∑ i:Seat c,masked W.threshold (T.map i).support (Pylon.gap t i) U:= by
   let f(i:Gains c):= masked W.threshold (spread X.reg T.map i).support (spread A.regular (Pylon.gap t) i) U; change (∑' i, f (N i))= _; rw [(N).tsum_eq f]; obtain ⟨k,hk,hL⟩:= (X.pours A).E_total h
   have he:Summable (fun i=> f (.inl i)):= Summable.of_norm_bounded hk (fun i=>?_); rw [Summable.tsum_sum (f:=f) he (show Summable (fun i=>f (.inr i)) from Summable.of_finite),tsum_fintype (f:=fun i:Seat c=> f (.inr i)) ]; rfl -- adjust syntax mvars
   change ‖masked W.threshold (X.reg i).support (A.regular i) U‖≤ _; by_cases hz: Healthy W.threshold (X.reg i).support U; rw [masked_eq _ _ _ _ hz]; exact (hL i).2 U hz [] (by simp) (by simp); rw [masked_ne _ _ _ _ hz,norm_zero]; exact (hL i).1
lemma splitL (t:ℝ)(h: softCost W X q b) (he:∀ i U, ‖A.logarithm i U‖≤ q i)(U:Config G c): (∑' i, (flint T t A).logarithm i U)=(∑' i,A.logarithm i U)+ ∑ i:Seat c, T.graft t i U:= by
   let f(i:Gains c):= spread A.logarithm (Pylon.graft T t) i U; change ∑' i,f (N i)=_; have hh:Summable (fun i=>f (.inl i)):= Summable.of_norm_bounded (Activities.summable_charge X.sites h.1 (Payments.drop_reserve W _ h.1 h.2)) (fun i=> he i U)
   rw [(N).tsum_eq f,Summable.tsum_sum (f:=f) hh (show Summable (fun i=> f (.inr i)) from Summable.of_finite),tsum_fintype (f:=fun i:Seat c=> f (.inr i)) ]; rfl
end lamp
variable {Y Y': Listing G c} {f g : Collection.Source G c} (h : Collection.Local Y W f b v) (hB:Collection.Local Y' W g b ε) {α r Δ η φ Λ θ : ℝ}
   {R:PathData G} {clip:Clip} (hG:G.Simple)(hw: Geo.Width W clip σ)(hv:R.Bounds clip σ φ Λ)(hf:WilsonStartup.Decent clip W) (hu: W.threshold^2 * |Δ| ≤ b)
  (hk:20<c.val)
local notation "Λ'"=> shelves Y R W
local notation "δ'"=> (Averaging.delta (Y.read f) - Δ)
local notation "X'"=> adobe Λ' T
local notation "F"=> Collection.fill Y R clip W f α Δ
local notation "F'"=> flint T δ' F
local notation "P"=> finish
local notation "C"=> forecastW G c W δ'
local notation "d"=> regularNeed G W clip σ φ α b
local notation "q"=> softNeed G W clip σ φ α b
local notation "β"=> r+α+Δ
local notation "χ"=> vac f τ
include h hG hw hv hf hu
-- strong +1 Hard/Soft at This tap exactly. Paid before turns.
lemma huts : ∃ k l:ℕ→ℝ, ((Λ').pours F).EBound W d ∧ hardCost W (Λ') k v ∧ softCost W (Λ') l q ∧ rooted F k l := by
    obtain ⟨u,hu',hb⟩ := h.cheap
    obtain ⟨k,hk,hK⟩ := h.expensive
    obtain ⟨he,hL⟩ := Collection.Local.quote_family hv hf hw α (X:=Y) _ hu' hb hu -- verify
    have hQ(i : ℕ) := Collection.Local.quote_soft (R:=R) (c:=clip) hG α Δ hu' h.smooth (numbering (Collection.LKey c) i)
    exact ⟨k, quoteL R W clip α Δ u∘ numbering _, ⟨_,fun i=> Collection.Local.quote_regular hG hv hf α Δ hu' h.smooth (numbering _ i),fun x=> Cost.equiv (numbering _) (he x)⟩, ⟨fun i=> (hk i).1,hK⟩, ⟨fun i=>(norm_nonneg _).trans (hQ i 1),fun x=> Cost.equiv (numbering _) (hL x)⟩,fun i U=> ⟨(hk i).2 U,hQ i U⟩⟩
include hk
-- paid by carrot. Use W.cost ring not external.
lemma fueled (ha: regularNeed G W clip σ φ α b + forecastW G c W (delta (Y.read f)-Δ) ≤ w)
     (he:Rates W.B δ v (softNeed G W clip σ φ α b + forecastW G c W (delta (Y.read f)-Δ)) θ): Ingredients X' F' W w δ:= by
   obtain ⟨k,l,hR,hK,hL,hW⟩:= Cinch.huts (α:=α) h hG hw hv hf hu
   obtain ⟨p,hp,hP⟩:= Cinch.fledged _ T δ' hR; let H(i:ℕ):= spread l (fun _ :Seat c=> Pylon.droop G W δ') (N i)
   refine Payments.tender (Cinch.gates Λ' T _ (h.fittings hG hv hf hk α Δ)) ⟨p,hp,fun i=> budget_loosen (hP i) ha⟩ (show hardCost W _ k _ from hK) (Cinch.soften _ T δ' l hL) (fun i u=> ⟨(hW i u).1,?_⟩) he
   change ‖spread ((F).logarithm) _ (N i) u‖ ≤ H i; unfold H; cases N i; exact (hW _ u).2; exact (Pylon.vessel T δ' _|>.2 u) -- spot q

lemma beauty (U:Config G c): let E:= trunk R clip W X' F' (r+α+Δ) χ
    E.eval U * Real.exp (∑' i,(F').logarithm i U)= earlyValue Y R clip W f r τ α U:= by
   intro E; obtain ⟨k,l,hR,hK,hL,hW⟩:= Cinch.huts (α:=α) h hG hw hv hf hu
   have he:E.activities.additive W U=((Λ').pours F).additive W U + ∑ i:Seat c, masked W.threshold (T.map i).support (Pylon.gap δ' i) U:= splitE T _ hR U
   have hz:E.exponent U + (∑' i, (F').logarithm i U)=(frozen Y R clip W f r τ).exponent U -α*receipt R clip W U:= by
      change (χ)*UVNext.CouplingReset.sites c - R.inChannels clip W (β) U-E.activities.additive W U + _= ((τ*UVNext.CouplingReset.sites c - R.inChannels clip W r U)-_)-_
      rw [vac,sub_mul,div_mul_cancel₀ _ (UVNext.CouplingReset.sites_pos c).ne', Push.BetaTransport.channels_split U (β),Push.BetaTransport.channels_split U r,he,splitL T (δ') hL (fun i U=> (hW i U).2)] -- channels namespace
      have ht:= h.first_split hG hk U; have hh:=h.additive hG hv α Δ U; have hΩ:=h.throw_sum hG hv hf hw α Δ U; have hz:=path_split hv hw hf α Δ U; have hY:= Pylon.wires T δ' U; dsimp only [receipt,frozen]; linarith
   rw [Rep.eval,mul_right_comm _ (E.activities.gas E.p U),← Real.exp_add,hz, earlyValue, Rep.eval,mul_right_comm _ ((frozen Y R clip W f r τ).activities.gas (frozen Y R clip W f r τ).p U),← Real.exp_add,neg_mul,sub_eq_add_neg]; rfl -- adjust

-- packs all if aligned. No equality assumption on label permutations. F' retained for E comparison.
abbrev lacquer (f:Collection.Source G c)(Y:Listing G c)(R:PathData G)(clip:Clip)(α τ r Δ:ℝ) := P R clip W (adobe (shelves Y R W) T) (flint T (Averaging.delta (Y.read f)-Δ) (Collection.fill Y R clip W f α Δ)) (r+α+Δ) (vac f τ)
lemma velvet (ha: regularNeed G W clip σ φ α b + forecastW G c W (delta (Y.read f)-Δ) ≤ w)
     (he:Rates W.B δ v (softNeed G W clip σ φ α b + forecastW G c W (delta (Y.read f)-Δ)) θ): let y:= lacquer T f Y R clip α τ r Δ; y.eval= earlyValue Y R clip W f r τ α∧ y.activities.Valid W w δ:= by
    intro y; have hl:= fueled T h hG hw hv hf hu hk ha he
    exact ⟨funext (fun i=> (hl.unshifted R clip (r+α+Δ) χ i).trans (beauty T h hG hw hv hf hu hk i)),hl.gates ..⟩
end YM.Juniper.Cinch
