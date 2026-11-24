import YM.GradedFar.Telex
import YM.GradedFar.Coffer
import YM.GradedFar.Foresight
/-!
# The formal H trial on the compact aperture

Read at s=rT. Uniform on T; no moving geometry. Supplies the polynomial quality inside
field/clock identification. Same unselected field path of `ClassExpansion`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Tariff.Billboard
open Function Filter Set PowerSeries
open Extraction Table Spec PhysMS Trace.Pilot OPE OPE.Orbits
open FVA2 XSpace XSpace.Normalize XSpace.Structure1 FVA2.Scale FVA2.Scale.Facets FVA2.Scale.Equator FVA2.Dframe FVA2.O.Score FVA2.Register FVA2.GradedFar FVA2.O.Enh
open MS MS.Native MS.Land MS.Book MS.Book.Program MS.Book.Convolve MS.Fleet MS.Menus
open YM.Integration.GradedFar.Neighbor YM.Integration.GradedFar.Tariff.Playbill FVA2.GradedFar.Cart
open Tickets
open Fork (Sold Safe)
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)(J:ℝ→tower S)
    (Z:WilsonPrescription G)(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) (ν:ℝ){hG:G.Simple}{σ:MS.Land.Prescription (Press.portDeck G)} (H:Main.Match Z hG M σ true)
local notation "Post" => Scale.Measure.outlook (WilsonPrescription.scheme Z) (WilsonPrescription.criterion Z)
local notation "KΛ" => GroupS.gaugeN (WilsonPrescription.scheme Z) (WilsonPrescription.criterion Z) M ν
local notation "KΣ" => conversion (GroupS.gaugeN (WilsonPrescription.scheme Z) (WilsonPrescription.criterion Z) M ν)
local notation "Θ" => GroupS.ψ (WilsonPrescription.criterion Z) M ν
local notation "γ" => fun (T:ℝ)=> -Real.log T
variable {p q n h:ℕ}
local notation "V"=> Sec G h
variable {t:ℝ→ℝ}(ht:Coupling G t) (hC:ClassExpansion F J (Scale.Measure.outlook Z.scheme Z.criterion) t n h)
local notation "τ"=> t ∘ Prod.fst -- annotate via Θ arguments
local notation "TT"=> fun (i:Route)=> Θ (γ (stretch i))

include hG ht in
lemma safeC : Coins clock (fun (_:Route) (_:Unit)=>True) (fun _ _=>1) (t ∘ Prod.fst):= ⟨ Eventually.of_forall (fun _ _ _=> ⟨le_rfl,zero_le_one⟩),
    (Coupling.conforms hG ht).comp running⟩
include ht hG
-- use g=sqrt weighting and Pose for comparable s; note compact ratios choose ≥1 else inverse.
lemma fees : ∀ᶠ i in clock, |t (next i)| ≤ 4*strength G i.1:= by
 let g:= strength G
 have hi:= Neighbor.funded_mono (hG:=hG); have hs:= Neighbor.fund_up (U:= (2:ℝ)) (B:= (1:ℝ)) (hG:=hG) (by norm_num) zero_lt_one
 have hv: ∀ᶠ i in trail,2 ≤ (2:ℝ)*g i ^ (-(1:ℝ)):= by
   filter_upwards [strength_positive hG,(Coupling.conforms hG (strength_coupling hG)).eventually_le_const zero_lt_one] with r hr h'
   rw [ Real.rpow_neg_one ]; exact le_mul_of_one_le_right (by norm_num) ((one_le_inv₀ hr).2 h')
 filter_upwards [nextPath.eventually (clock_budget hG ht), running.eventually (hi.and (hs.and hv)), running.eventually
    (self_mem_nhdsWithin (s:=Ioi 0)), strength_positive hG |> running.eventually]
    with i htp hh hp hs
 have hp':0 < i.1:=hp; obtain hS:= stretch_pos i.2; obtain h₀|h₀:= le_total 1 (stretch i)
 · have he:= (hh.2.1 _ ⟨h₀,i.2.property.2.trans hh.2.2⟩).2; change g (next i) ≤ 2*(strength G i.1) at he; unfold g at he; linarith only [he,htp.2.2]
 have he: g (next i) ≤ strength G i.1:= (hh.1 _ ⟨mul_pos hp' hS,mul_le_of_le_one_right hp'.le h₀⟩).2
 unfold g at he; linarith only [he,hs,htp.2.2]
private lemma over_p (p:ℕ){K:Route→ℂ}{A:Route→PowerSeries ℂ}(h:WithTax p clock
    (fun _ (_:Unit)=>True) (fun _ _=>1) (t ∘ Prod.fst) (fun i _=>K i) (fun i _=> A i)):
    ∃ b:ℝ,0≤b ∧ ∀ᶠ i in clock, ‖K i-appointedH140Crop p (t i.1) (A i)‖ ≤ b*(strength G i.1)^(p+1):= by
 obtain ⟨j,b,hb,H⟩:= h.error; refine ⟨b*2^(p+1),by positivity,?_ ⟩
 filter_upwards [running.eventually (clock_budget hG ht),H] with i hi hx; specialize hx () trivial
 simp only [Function.comp_apply,one_pow,mul_one] at hx; exact hx.trans ((mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (abs_nonneg _) hi.2.2 _) hb).trans_eq (by ring))
include H

local instance {n:ℕ} : ContinuousSMul ℝ (Points n) := IsBoundedSMul.continuousSMul
include hC in
omit hG ht H in
lemma location (x:Stage n)(u:ListInput G n h)(p:ℕ) : WithTax p clock
    (fun (_:Route) (_:Unit)=>True) (fun _ _=>1) (t ∘ Prod.fst) (fun i _=> frank F J none h i.1 (stretch i • x.val) u)
    (fun i _=>sent Post h (stretch i • x.val) u):= by
 letI : CompactSpace Joggle:= isCompact_iff_compactSpace.mp isCompact_Icc; let z (i:Joggle):=(i.val:ℝ) • x.val; let K:=z '' univ
 have hc:IsCompact K:= IsCompact.image isCompact_univ (continuous_subtype_val.smul continuous_const); have hx: K ⊆ conf n:=by rintro v ⟨i,_,rfl⟩; exact Work.A05.smul_conf (stretch_pos i) x.property
 obtain H:= hC K hc hx u
 refine ⟨ ?_,?_⟩
 · intro j; obtain ⟨C,hC,H⟩:=no_drag (H.cost j); exact Fork.Sold.bounded hC (Eventually.of_forall
     fun i _ _=> by rw [mul_one]; exact H ⟨_, mem_image_of_mem z (mem_univ i.2)⟩)
 obtain ⟨C,hC,H⟩:=(H.good p).cost; exact Fork.Sold.bounded hC ((running.eventually H).mono (fun i h _ _=>h ⟨_, mem_image_of_mem z (mem_univ i.2)⟩))
-- ψ leading real
omit ht in
lemma real_ψ (u:ℂ)(t:ℝ)(p:ℕ)(s:ℝ)(hu:u=appointedH140Crop p t (Θ s)): (u.re:ℂ)=u:= by
    have h(k:ℕ): starRingEnd ℂ (coeff k (Θ s))=coeff k (Θ s):= by
       have h:= congr_arg (coeff k) (((H.dilation ν).check.led s).real); simpa only [PowerSeries.coeff_map] using h
    rw [hu]; let A:= appointedH140Crop p t (Θ s); have ht: starRingEnd ℂ A=A:= by unfold A; rw [crop_eq,map_sum]; exact Finset.sum_congr rfl (fun i _=>by rw [map_mul,map_pow,h i,Complex.conj_ofReal]);
    obtain ⟨r,hr⟩:= Complex.conj_eq_iff_real.mp ht; change (A.re:ℂ)=A; rw [hr]; rfl
omit H ht hG in
lemma insert_value (v:V)(a: Toon G h)(p:ℕ)(s T:ℝ): coord a (cropK KΛ (γ T) p s h v)= appointedH140Crop p s (gateColumn Z M ν T v a) := by
    simp only [cropK,gateColumn,crop_eq,LinearMap.sum_apply,LinearMap.smul_apply,map_sum,map_smul,coeff_mk,smul_eq_mul]
omit ht in
lemma K_price (u:V)(a:Toon G h): Prospects clock (fun _ (_:Unit)=>True) (fun _ _=>1) (fun i _=> gateColumn Z M ν (stretch i) u a):= by
 intro k; obtain ⟨C,hC,hv⟩:= no_drag (gatesPaid Z M ν H u a k); exact Fork.Sold.bounded hC
   (Eventually.of_forall (fun i _ _=> by rw [mul_one]; exact hv i.2 ))
include hC
lemma prepaid (x:Stage n)(u:ListInput G n h)(p:ℕ): ∃ b:ℝ,0≤b ∧ ∀ᶠ i in clock,
    ‖frank F J none h i.1 (stretch i • x.val) (fun a=> cropK KΛ (γ (stretch i)) p (t i.1) h (u a)) -
       appointedH140Crop p (t i.1) ((sent Post h x.val u).subst (TT i))‖ ≤ b*(strength G i.1)^(p+1):=by
 apply over_p (hG:=hG) ht p; let L:= location F J Z hC x (p:=p) (h:=h)
 let k:=safeC ht (G:=G) (hG:=hG)
 simp_rw [travel_bill Z M ν H x u (stretch_pos _), basis_sum (frank F J none _ _ _) (fun a=> cropK KΛ _ p _ _ (u a)),smul_eq_mul, multipliers,votes]; apply WithTax.sum k; intro i _
 apply WithTax.mul k _ (L (basisWord i)); apply WithTax.product k; intro j _; simp_rw [insert_value]; exact WithTax.crop_later k le_rfl (K_price Z M ν H (u j) _)
end YM.Integration.GradedFar.Tariff.Billboard
