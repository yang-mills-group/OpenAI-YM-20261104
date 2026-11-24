import YM.GradedFar.Literal
import YM.GradedFar.Shine
/-!
# Setup budgets for displacement (the real continuum part of RoundMeter(ii))

Also point variations for both r and s(r,T)-normalized H rows; exercise on
real grid & authentic original `m_N` reads exactly at these offsets. Using `Spec.Final.xxx`,
calendar before moving. Doesn't pay the separate filed estimator substitutes.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Auth
open Function Filter Set PowerSeries
open Extraction Table Spec PhysMS Trace.Pilot OPE OPE.Orbits Lattice
open FVA2 XSpace XSpace.Normalize XSpace.Structure1 FVA2.Scale FVA2.Scale.Facets FVA2.Scale.Equator FVA2.Dframe FVA2.O.Score FVA2.Register FVA2.GradedFar FVA2.O.Enh
open MS MS.Native MS.Land MS.Fleet Neighbor Tariff Tariff.Playbill Tariff.Crosser Tariff.Billboard Tariff.Sunshine Batch
open Fork (Sold Safe)
open scoped Topology BigOperators Classical ContDiff
local instance {n:ℕ} : ContinuousSMul ℝ (Points n):= IsBoundedSMul.continuousSMul
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)
   (R:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) (J P:ℝ→tower S) (Z:WilsonPrescription G)(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
   {hG:G.Simple}{σ:MS.Land.Prescription (Press.portDeck G)} (H:Main.Match Z hG M σ true) (ν:ℝ)
    {t:ℝ→ℝ}(Ht:Pose F J Z t)(hF:Prepared F J P Z t)(Hq:LogTrace F R.port)
variable {n m h p:ℕ} {K K':Set (Points n)}{N N':Set (Points m)} {U B:ℝ}
local notation "g∴"=> strength G
local notation "X"=> Scale.Measure.outlook Z.scheme Z.criterion
local notation "S•"=> moving G U B
local notation "Y"=> Points (n+m)
open Metric
-- ready any grid placement within trajectory. include common scales even if both slots Far unit.
-- Lipschitz on *physical actual moment* from first coordinate derivative bound for constant-frame args
variable {d:Fin (n+m)→ℕ}(ha:AppointedH140Through h d)
lemma atCompact (u:AppointedH140Inputs G d)(r:ℝ)(hr:0<r){x:Points (n+m)} (hx:x∈conf _) : TrueCompact F P none r 0 x u=nl P d (fun _=>r) (r•x) u:= Eq.symm (atTable_within F P none d u 0 hr hx)
include F in
private lemma at_rule (u:AppointedH140Inputs G d)(L:Fin (n+m)→ℝ){r:ℝ}(hr:0<r): ContDiffOn ℝ ∞ (fun x:Points (n+m)=> nl P d L (r•x) u) (conf _):= kernel_smooth F none hr (fun i=>⟨_,assign P (L i) (d i) (u i)⟩)

abbrev appointment {n m:ℕ}(K:Set (Points n))(N:Set (Points m))(p:Calendar)(x:Points (n+m)):= Fits K N p.2 x
variable (hU:0<U)(hB:0<B)(hK:IsCompact K)(hx:K⊆conf n)(hN:IsCompact N)(hz:N ⊆ Outside m)
include H Ht hF hU hB hK hx hN hz Hq ν
include ha in
private lemma warm (i:Fin (n+m)×Axis): ∃ b:ℝ,0≤b ∧ ∀ᶠ p in S•,∀ y, Fits K N p.2 y→∀ u:AppointedH140Inputs G d, Box u 1→
    ‖Points.gradient i.1 i.2 (fun x:Points (n+m)=> nl P d (fun _=>p.1) (p.1•x) u) y‖ ≤ b * (g∴ p.1)⁻¹:=by
    obtain ⟨b,hb,_,T,hT,H'⟩:= roundFull F R J P Z M H ν Ht hF Hq hU hB hK hx hN hz ha [i] 0 0
    refine ⟨b,hb,?_⟩; filter_upwards [ (show ∀ᶠ p in S•,∀ x,Fits K N p.2 x → ∀ u:AppointedH140Inputs G d,Box u 1 → ‖δ [i] (fun x=> TrueCompact F P none p.1 0 x u) x‖≤ b * (g∴ p.1)⁻¹ from physicalOnsets.mpr ⟨T,hT,H'.mono fun (r:ℝ) hr T he h x hx u hu=>(hr T he h.2 x hx 0 none u hu).2.1⟩), Road.funded_forms
        hK hx hN hz (W:=appointment K N) (z:=fun p x=>x) (fun _ _ h=> h), poses (show ∀ᶠ r in trail,0<r from self_mem_nhdsWithin)]
        with p hr hc hp y hy u hu
    rw [← show δ [i] (fun x=> TrueCompact F P none p.1 0 x u) y= Points.gradient _ _ _ _ from δ_congr (conf_open _) (fun x h=>atCompact F P u p.1 hp h) [i] (hc _ hy)]
    exact hr y hy u hu
-- use on line-bits travelling. G9 bound H derivatives; ~ D* focus after making lighting leases
include ha in
private lemma sun_y : ∃ b:ℝ,0≤b ∧ ∀ᶠ p in S•,∀ x y, Crosser.segment K N p (x,y) → ∀ u:AppointedH140Inputs G d, Box u 1 →
    ‖nl P d (fun _=>p.1) (p.1•y) u - nl P d (fun _=>p.1) (p.1•x) u‖ ≤ b * (g∴ p.1)⁻¹*‖y-x‖:=by
    choose B hb hb' using warm F R J P Z M H ν Ht hF Hq ha hU hB hK hx hN hz; let b:= ∑ i,B i
    refine ⟨b, Finset.sum_nonneg (fun i _=>hb i),?_⟩
    filter_upwards [eventually_all.mpr hb', poses (show ∀ᶠ r in trail,0<r from self_mem_nhdsWithin), safely hK hx hN hz, poses (strength_positive hG)]
       with p hp hr hT he x y h u hu
    let f(x:Points (n+m)):= nl P d (fun _=>p.1) (p.1•x) u; let f':= fderiv ℝ f; let Y':= slopePath x (y-x); let v:=y-x; have H:= at_rule F P u (fun _=> p.1) hr
    have H₀ : ContinuousOn f' (conf _) := (H.fderiv_of_isOpen (conf_open _) (m:=0) (by simp)).continuousOn
    have hV:MapsTo Y' (uIcc (0:ℝ) 1) (conf _):=hT _ h; have hh: IntervalIntegrable (fun j=> f' (Y' j) v) MeasureTheory.volume 0 1:= ((H₀.comp (walking_cont x _).continuousOn hV).clm_apply continuousOn_const).intervalIntegrable
    change ‖f y-f x‖≤ _; rw [ show f y-f x=(∫ j in (0:ℝ)..1, f' (Y' j) v) from (by
         rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f:=f ∘ Y') _ hh]; simp [Y']
         intro i hi; exact slope_chain x v i ((H.contDiffAt ((conf_open _).mem_nhds (hV hi))).differentiableAt (by simp))) ]
    apply int_budget; intro i hi; rw [evaluate]; simp_rw [b, Finset.sum_mul]; exact (norm_sum_le ..).trans (Finset.sum_le_sum
        (fun j _=> by rw [norm_mul]; exact (mul_le_mul (shift_cost v j) (hp j (Y' i) (h i hi) u hu) (norm_nonneg _) (norm_nonneg _)).trans_eq (mul_comm ..)))
-- all centers, z,y comparison with hypotheses of RoundMeter enlargement
omit hU hB H Ht hF Hq ν in
set_option linter.unusedSectionVars false in
lemma exact_grows (h₁ : K⊆ interior K')(h₂:N⊆ interior N'): ∃ e:ℝ,0<e ∧ ∀ T:ℝ,1≤T → ∀ x, Fits K N T x→
    ∀ y, ‖y-x‖<e → Fits K' N' T y ∧ Crosser.segment K' N' (0,T) (x,y):=by
 obtain ⟨e,he,H⟩:= enlargement hK hN h₁ h₂
 refine ⟨e,he,fun T ht x hx y hy=> ⟨H T ht _ hx _ hy,fun i hi=>?_⟩⟩; dsimp only; rw [uIcc_of_le zero_le_one] at hi
 apply H T ht _ hx; unfold slopePath; rw [add_sub_cancel_left,norm_smul, Real.norm_eq_abs,abs_of_nonneg hi.1]; exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) hi.2) hy
include ha in
lemma rounding (hK':IsCompact K')(hx':K'⊆conf n)(hN':IsCompact N')(hz':N' ⊆ Outside m)(h₁ : K⊆ interior K')(h₂:N⊆ interior N'):
    ∃ b ε:ℝ,0≤b ∧ 0<ε ∧ ∀ᶠ p in S•,∀ x,Fits K N p.2 x→∀ (y:Points (n+m)), ‖y-x‖< ε → Fits K' N' p.2 y ∧
    ∀ u:AppointedH140Inputs G d, Box u 1 →‖ (nl P d (fun _=> p.1) (p.1•y)) u -(nl P d (fun _=> p.1) (p.1•x)) u‖ ≤ b*(g∴ p.1)⁻¹*‖y-x‖:=by
 obtain ⟨e,he,Hc⟩:= exact_grows hK hx hN hz h₁ h₂; obtain ⟨b,hb,hs⟩:= sun_y F R J P Z M H ν Ht hF Hq ha hU hB hK' hx' hN' hz'
 exact ⟨b,e,hb,he,(ifWide.and hs).mono fun p hp x hx y hy=>⟨(Hc p.2 hp.1.1 _ hx _ hy).1, hp.2 x y (Hc p.2 hp.1.1 x hx y hy).2⟩⟩
end YM.Integration.GradedFar.Auth
