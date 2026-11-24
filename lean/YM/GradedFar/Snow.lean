import YM.GradedFar.Poll
import YM.GradedFar.Settle
/-!
# Use Store tickets to buy the C.5 valued prediction on this session's profile

Then derive the signed thermometer price *at these points & labels* without new hypotheses.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Tariff.Ballot
open Function Filter Set PowerSeries MeasureTheory
open Extraction Table Spec PhysMS Trace.Pilot OPE OPE.Orbits
open FVA2 XSpace XSpace.Normalize XSpace.Structure1 FVA2.Scale FVA2.Scale.Facets FVA2.Scale.Equator FVA2.Dframe FVA2.O.Score FVA2.Register FVA2.GradedFar FVA2.O.Enh
open MS MS.Native MS.Land MS.Book MS.Book.Program MS.Book.Convolve MS.Fleet MS.Menus
open Fork (Sold Safe)
open Playbill Tickets Week
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)(J:ℝ→tower S)
variable {Z: WilsonPrescription G}(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
variable {hG:G.Simple}{σ:MS.Land.Prescription (Press.portDeck G)} (H: Main.Match Z hG M σ true)
variable {n h p q:ℕ}
local notation "A"=>Scale.Measure.start (WilsonPrescription.scheme Z) (WilsonPrescription.criterion Z)
local notation "B"=>Scale.Measure.outlook (WilsonPrescription.scheme Z) (WilsonPrescription.criterion Z)
local notation "g∴"=> strength G
local notation "KX"=> WilsonPrescription.criterion Z
local notation "Sat"=> (Z.store.measure h)
structure Stamps (F:Final C f S)(J:ℝ→tower S) (Z:WilsonPrescription G)(p q h:ℕ)(D:Fray (Z.store.measure h))(U:ℝ→Normalize.Change G h)
    (τ:ℝ→ℝ):Prop where
    buy : p ≤ q
    base : Tendsto (fun r=>guide G h (U r)) trail (𝓝 0)
    -- measured t'ℓ at this booking (NOT actual t)
    posted : Tendsto (fun r=>τ r/ strength G r) trail (𝓝 1)
    trial : ∀ i:Fin D.n, Session F J Z (D.scope i).t p q h τ U
variable (D:Fray ((WilsonPrescription.store Z).measure h))
   (Y:ℝ→Normalize.Change G h)(τ:ℝ→ℝ)
local notation "X"=> guide G h
variable (hS:FitsSat F J Z h) (HP:Stamps F J Z p q h D Y τ) (φ:Test n)
private abbrev FrameSupport (φ:Test n):= ↥(tsupport φ)
local notation "v*" => FrameSupport φ
private def loc (v:Sec G h)(a:Toon G h):MoveSpace G h →L[ℝ] ℂ:= LinearMap.toContinuousLinearMap {
    toFun p:= coord a (((guide G h).symm p).val v)
    map_add' _ _:=by rw [map_add]; exact map_add (coord a) ..
    map_smul' a x:=by rw [map_smul]; exact map_smul ((coord _).restrictScalars ℝ) ..
}
private lemma locus (v:Sec G h)(a:Toon G h)(p:Change G h):loc v a (X p)= coord a (p.val v):= by
 change coord a (((guide G h).symm (guide _ _ _)).val v) = _; rw [LinearEquiv.symm_apply_apply]
include H hS HP
set_option linter.unusedSectionVars false in
lemma Stamps.exp : Coupling G τ := Trial_coupling (hG:=hG) τ HP.posted
lemma Stamps.pose (hφ: Session F J Z φ p q h τ Y):
    Chosen F J Z trail (fun (_:ℝ) (_:v*)=>True) id (fun _ x=>x.val) τ h p q τ (fun r=> stand (Y r)):= by
 let ht:= Coupling.conforms hG (Stamps.exp F J M H D Y τ hS HP)
 obtain ⟨a,ha,h⟩:= forecast F J M H D Y τ hS ht HP.base HP.trial
 refine ⟨HP.buy,ht,⟨0,by simp⟩,?_, fun v=>?_⟩
 · intro v w; refine ⟨‖loc v w‖*a, by positivity,?_⟩; filter_upwards [h] with r hr
   rw [stood,map_add, add_sub_cancel_left, ← locus]; exact ((loc v w).le_opNorm _).trans ((mul_le_mul_of_nonneg_left hr (norm_nonneg _)).trans_eq (mul_assoc ..).symm)
 obtain ⟨c,hc,H'⟩:= hφ v; exact ⟨c,hc,H'.mono fun i hi j _=> hi _ j.property⟩
lemma Stamps.income (hφ:Session F J Z φ p q h τ Y)(v:ListInput G n h): WithTax p trail (fun (_:ℝ) (_:v*)=>True) (fun _ _=>1) τ
    (fun r x=>frank F J none h r x.val v) (fun _ x=>sent A h x.val v):=by
 let W:=fun (_:ℝ)(_:v*)=> True; have he:Safe trail W (fun _ _=>1) (fun _ _=> (1:ℝ)) := Eventually.of_forall (fun _ _ _=> ⟨le_rfl,zero_le_one⟩)
 have hZ (u: ListInput G n h): Prospects trail W (fun _ _=>1) (fun (_:ℝ) (x:v*)=> sent B h x.val u):= by
    intro i; obtain ⟨c,hc⟩:= IsCompact.exists_bound_of_continuousOn φ.hasCompactSupport ((kernel_continuous Z M H u i).mono φ.tsupport_subset)
    exact Fork.Sold.bounded (c:=max 0 c) (le_max_left ..) (Eventually.of_forall fun p (x:v*) _=>by change ‖coeff i (sent B h x.val u)‖ ≤ (max 0 c)*1; rw [mul_one,sent,coeff_mk]; exact le_trans (hc _ x.property) (le_max_right ..))
 exact paidW F Z M H tendsto_id (Stamps.exp F J M H D Y τ hS HP) he ⟨q,τ,_,Stamps.pose F J M H D Y τ hS HP φ hφ⟩ hZ v

omit HP hS H
private lemma subtraction {V:Type*}{f g:ℝ→V→ℂ}{x y:ℝ→V→PowerSeries ℂ} (H:Tendsto τ trail (𝓝 0))
   (hf:WithTax p trail (fun _ (_:V)=>True) (fun _ _=>1) τ f x) (hg:WithTax p trail (fun _ (_:V)=>True) (fun _ _=>1) τ g y):
    WithTax p trail (fun _ (_:V)=>True) (fun _ _=>1) τ (fun i j=> f i j-g i j) (fun i j=> x i j-y i j):= by
    have hx : Coins trail (fun _ (_:V)=>True) (fun _ _=>1) τ:=⟨Eventually.of_forall (fun _ _ _=>⟨le_rfl,zero_le_one⟩),H⟩
    simp_rw [sub_eq_add_neg]; apply WithTax.add hx hf; simpa only [map_neg,map_one, neg_mul, one_mul] using
      (WithTax.constant (φ:=trail) (t:=τ) (W:=fun _ (_:V)=>True) (p:=p) (-1)).mul hx hg
abbrev rated (F:Final C f S)(J:ℝ→tower S)(x:Points 3)(r:ℝ)(s:Rose.Badge):ℂ:= frank F J none 6 r x (MASK (G:=G) s)
-- b3 on numeric, actual log read position of Clock upon composition later
def readingLog (r:ℝ)(x:Points 3):ℂ:=
    let K:= rated F J x r; K Finset.univ - (K {0,1}*K {2}+K {0,2}*K {1}+K {1,2}*K {0}) + 2*(K {0}*K {1}*K {2})
lemma log_stable (r:ℝ)(hr:0<r): ContinuousOn (readingLog F J r) (conf 3):=by
 have ht(i):= (true_views F J none hr (MASK (G:=G) i)).continuousOn; unfold readingLog; --
 exact ((ht _).sub ((((ht _).mul (ht _)).add ((ht _).mul (ht _))).add ((ht _).mul (ht _)))).add ((((ht _).mul (ht _)).mul (ht _)).const_mul _)
section
local notation "peak"=> Select.Single (A 6)
local notation "pulse"=> Rose.test KX
local notation "c*"=> Rose.cT (Rose.Pick.cut (WilsonPrescription.criterion Z)) G (Rose.Pick.image (WilsonPrescription.criterion Z))
variable (D:Fray ((WilsonPrescription.store Z).measure 6))(Y:ℝ→Change G 6)(H₆:FitsSat F J Z 6)
   (H₁:Stamps F J Z p q 6 D Y τ) (hφ:Session F J Z (Rose.test (WilsonPrescription.criterion Z)) p q 6 τ Y)
local notation "r*"=> FrameSupport pulse
include H hφ H₁ H₆
lemma log_price : WithTax p trail (fun (_:ℝ) (_:r*)=> True) (fun _ _=> 1) τ (fun i x=> readingLog F J i x.val) (fun _ x=> peak x.val):= by
 let W:= fun (_:ℝ)(_:r*)=>True; have ht:=Coupling.conforms hG (Stamps.exp F J M H D Y τ H₆ H₁); have hx : Coins trail W (fun _ _=>1) τ:= ⟨Eventually.of_forall (fun _ _ _=>⟨le_rfl,zero_le_one⟩),ht⟩
 have he (i:Rose.Badge): WithTax p trail W (fun _ _=>1) τ (fun r (x:r*)=> rated F J x.val r i) (fun _ (x:r*)=> Rose.batchT
    (Jury.fxt (A 6) x.val) i):= by
    have H' := Stamps.income F J M H D Y τ H₆ H₁ pulse hφ (MASK (G:=G) i); exact H'.tran (Eventually.of_forall (fun _ _ _=>rfl))
        (Eventually.of_forall (fun i' (x:r*) _=> (extinct_mask Z M H i ((Rose.test KX).tsupport_subset x.property)).symm))
 dsimp only [readingLog, Select.Single]; simp_rw [Rose.b3,two_smul ℂ,two_mul]
 let m:= (((he {0}).mul hx (he {1})).mul hx (he {2}))
 exact (subtraction τ ht (he _) ((((he _).mul hx (he _)).add hx ((he _).mul hx (he _))).add hx ((he _).mul hx (he _)))).add hx (m.add hx m)
theorem tested_continuum (hp:1≤p):
    ∃ C:ℝ,0≤C ∧ ∀ᶠ r in trail, ‖(Rose.test KX).applyTo (readingLog F J r) - ((c*:ℝ):ℂ)*(τ r:ℂ)‖ ≤ C*g∴ r^(p+1):=by
 obtain ⟨j,a,ha,H'⟩:= (log_price F J M H τ D Y H₆ H₁ hφ).error; simp only [one_pow,mul_one] at H'
 let b:= (∫ x,‖pulse x‖)*a; have hb:b≥0:= mul_nonneg (integral_nonneg fun x=> norm_nonneg _) ha
 refine ⟨b*2^(p+1),by positivity,?_⟩; filter_upwards [H', (show ∀ᶠ r in trail,0<r from self_mem_nhdsWithin), clock_budget hG (Stamps.exp F J M H D Y τ H₆ H₁)] with r hr hp' hh
 have heP: ContinuousOn (fun x:Points 3=> appointedH140Crop p (τ r) (peak x)) (conf 3):= by
    simp_rw [crop_eq]; exact continuousOn_finsetSum _ (fun i _=> (Select.steady _ (k:=i) (Billboard.till_reports Z M H).light).const_mul _)
 rw [← signal_position Z M H p hp (τ r)]; exact (apply_gap pulse (log_stable F J r hp') heP
    (fun x hx=> hr (⟨x,hx⟩:r*) trivial)).trans (by rw [← mul_assoc]; exact (mul_le_mul_of_nonneg_left
       (pow_le_pow_left₀ (abs_nonneg _) hh.2.2 _) hb).trans_eq (show b*(2*g∴ r)^(p+1) =_ by rw [mul_pow]; unfold b; ring))
end
end YM.Integration.GradedFar.Tariff.Ballot
