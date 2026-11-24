import YM.GradedFar.Sunbeam
/-!
# Booked continuum derivative assertion through all orders in G9

After matching to same elected W/H. Field budget even `g^{-1}`. Horizon assumption
`Λ>0,B>0` and T constant lower threshold per ticket. All costs at exact
fields & layouts of continuum statements. This does **not** estimate the *cutoff*
`m` or estimators at ``actual reports'', separate question.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Batch
open Function Filter Set PowerSeries
open Extraction Table Spec PhysMS Trace.Pilot OPE OPE.Orbits
open FVA2 XSpace XSpace.Normalize XSpace.Structure1 FVA2.Scale FVA2.Scale.Facets FVA2.Scale.Equator FVA2.Dframe FVA2.O.Score FVA2.Register FVA2.GradedFar FVA2.O.Enh
open MS MS.Native MS.Land MS.Fleet Neighbor Tariff Tariff.Playbill Tariff.Crosser Tariff.Billboard Tariff.Sunshine Tariff.Tickets
open Fork (Sold Safe)
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)
   (R:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) (J P:ℝ→tower S) (Z:WilsonPrescription G)(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
   {hG:G.Simple}{σ:MS.Land.Prescription (Press.portDeck G)} (H:Main.Match Z hG M σ true) (ν:ℝ)
    {t:ℝ→ℝ}(Ht:Pose F J Z t)(hF:Prepared F J P Z t)(Hq:LogTrace F R.port)
variable {n m h p:ℕ} {K:Set (Points n)}{N:Set (Points m)} {U B:ℝ}
local notation "g∴"=> strength G
local notation "X"=> Scale.Measure.outlook Z.scheme Z.criterion
local notation "P∥" => moving G U B
-- derivative version includes derivative observations in r units of layout (x,Ty) positions; relative to same center o.
-- ordinary interpretation of word, includes repeats. price in ∞ coordinate basis norm.
variable {a:Fin (n+m)→ℕ}
def RoundFull (t:ℝ→ℝ)(U B:ℝ)(K:Set (Points n))(N:Set (Points m))(L:TraceOrder (n+m))(p q:ℕ)(ha:AppointedH140Through h a):Prop:=
    ∃ D:ℝ,0≤ D ∧ ∃ j:ℕ,∃ T₀:ℝ,2 ≤ T₀ ∧ ∀ᶠ r in trail, ∀ T:ℝ,T₀≤T→ T≤U*(g∴ r)^(-B) → ∀ z, Fits K N T z → ∀ o (V:Viewers F),∀ u:AppointedH140Inputs G a,Box u 1 →
        let Y:= δ L (fun x=> TrueCompact F P V r o x u) z
        let Q:= jetCost L X h (GradedFar.raised ha u) z
        ‖Y-appointedH140Crop p (t r) Q‖ ≤ D*(1+Real.log T)^j*(g∴ r)^(p+1) ∧
        ‖Y‖≤ D*(g∴ r)⁻¹ ∧ ‖coeff q Q‖ ≤ D*(1+Real.log T)^j
set_option linter.unusedVariables false in
private abbrev Ω (K:Set (Points n))(N:Set (Points m))(a:Fin (n+m)→ℕ):=
    E4 × Viewers F × Points (n+m) × {u:AppointedH140Inputs G a//Box u 1}
private lemma trip {Iota:Type*}{W:Calendar→Iota→Prop}
    {f:Calendar→Iota→ℂ}{Gx:Calendar→Iota→PowerSeries ℂ}(hU:0<U)(hB:0<B)(ht:Coupling G t)
    (hf:WithTax p (moving G U B) W (fun i _=>Δlog i) (t∘Prod.fst) f Gx)(hG:G.Simple)(q:ℕ): ∃ D:ℝ,0≤D ∧ ∃ j:ℕ, ∀ᶠ i in P∥,∀ x,W i x→
    ‖f i x-appointedH140Crop p (t i.1) (Gx i x)‖ ≤ D*Δlog i^j*g∴ i.1^(p+1) ∧ ‖f i x‖ ≤ D*(g∴ i.1)⁻¹ ∧ ‖coeff q (Gx i x)‖ ≤ D*Δlog i^j:=by
    obtain ⟨l,c,hc,hf'⟩:= hf.error; obtain ⟨n,b,hb,H⟩:= hf.cost q; let T:=max (c*2^(p+1)) b
    obtain ⟨i,d,hd,hh⟩:= hf.total (show Coins (moving G U B) W (fun i _=> Δlog i) (t∘Prod.fst) from ⟨Road.safety, (Coupling.conforms hG ht).comp rising⟩)
    have hk:0≤T:= hb.trans (le_max_right ..); refine ⟨T+d,add_nonneg hk hd, max l n,?_⟩
    filter_upwards [H,hf',hh,moneySafe,poses (clock_budget hG ht),poses (pay_log (hG:=hG) hU hB i),ifWide] with i' h H' Ht hm hs hD he x hh
    obtain ⟨hv,_,ha⟩:=hs; specialize hD i'.2 he; specialize Ht x hh; specialize h x hh; rw [mul_one] at Ht h
    refine ⟨(H' x hh).trans ?_,Ht.trans ?_,h.trans ?_⟩
    · refine le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) ha _) (by positivity)) (le_trans (le_of_eq
        (show c*Δlog i'^l*(2*g∴ i'.1)^(p+1)=c*2^(p+1)*Δlog i'^l*g∴ i'.1^(p+1) from by ring)) ?_); gcongr; exacts [(le_max_left ..).trans (le_add_of_nonneg_right hd),le_max_left ..]
    · rw [← div_eq_mul_inv, le_div_iff₀ hv, mul_assoc]; refine (mul_le_mul_of_nonneg_left hD hd).trans_eq (mul_one _) |>.trans (le_add_of_nonneg_left hk)
    gcongr; exacts [(le_max_right ..).trans (le_add_of_nonneg_right hd),le_max_right ..]
variable (hU:0<U)(hB:0<B)(hK:IsCompact K)(hx:K⊆conf n)(hN:IsCompact N)(hz:N ⊆ Outside m)
include hK hx hN hz H Ht hF hU hB Hq ν
theorem roundFull (ha:AppointedH140Through h a)(L:TraceOrder (n+m))(p q:ℕ): RoundFull F P Z t U B K N L p q ha := by
    let I:= Ω F K N a; let W:=fun (i:Calendar)(x:I)=> Fits K N i.2 x.2.2.1; let z:= fun (_:Calendar) (x:I)=> x.2.2.1; let v:=fun (_:Calendar)(x:I)=>x.2.1
    obtain ⟨D,hD,j,H'⟩:= trip (p:=p) hU hB Ht.running (tribute F R J P Z M H ν Ht hF Hq hU hB hK hx hN hz (z:=z) (fun _ _ (h:W _ _)=> h) ha L
       (fun _ (x:I)=> x.2.2.2.val) (fun _ x _=> x.2.2.2.property) v (fun _ (x:I)=> x.1)) hG q
    obtain ⟨T,hT,H'⟩:= physicalOnsets.mp H'
    exact ⟨D,hD,j,T,hT,H'.mono fun r hr T' h hp z hw o V u hc=> hr T' h ⟨one_le_two.trans (hT.trans h),hp⟩ ((o,V,z,⟨u,hc⟩):I) hw⟩
end YM.Integration.GradedFar.Batch
