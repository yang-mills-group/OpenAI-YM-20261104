import YM.GradedFar.Collar
/-!
# Use the previous C5.S material (and F2)

Strength budget source here stated strictly earlier on compact r-units (T clock used by C5,
NOT the measured t yet). Works for all W/home slots of the requested price.
Use same T & cash limit point on all these, exactly these included, from PoseFit inputs.
No need to feed first part of F.3 or Frame prices into this bridge.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Tariff.Ballot
open Function Filter Set PowerSeries MeasureTheory
open Extraction Table Spec PhysMS Trace.Pilot OPE OPE.Orbits
open FVA2 XSpace XSpace.Normalize XSpace.Structure1 FVA2.Scale FVA2.Scale.Facets FVA2.Scale.Equator FVA2.Dframe FVA2.O.Score FVA2.Register FVA2.GradedFar FVA2.O.Enh
open MS MS.Native MS.Land MS.Book MS.Book.Program MS.Book.Convolve MS.Fleet MS.Menus
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)(J:ℝ→tower S)
variable {Z: WilsonPrescription G}(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
variable {hG:G.Simple}{σ:MS.Land.Prescription (Press.portDeck G)} (H: Main.Match Z hG M σ true)
variable {n h p q:ℕ}
local notation "A"=>Scale.Measure.start (WilsonPrescription.scheme Z) (WilsonPrescription.criterion Z)
local notation "g∴"=> strength G
-- simple TV even for real coupling and probability mass sign
lemma apply_gap (t:Test n) {f g:Points n→ℂ}{c:ℝ}(hf:ContinuousOn f (conf n))(hg:ContinuousOn g (conf n))(hc:∀ i∈tsupport t, ‖f i-g i‖≤c):
    ‖t.applyTo f - t.applyTo g‖ ≤ (∫ x, ‖t x‖)*c:= by
 unfold Test.applyTo; rw [← integral_sub (t.smearing hf) (t.smearing hg),← integral_mul_const]; simp_rw [← mul_sub]
 refine norm_integral_le_of_norm_le (((t.continuous.integrable_of_hasCompactSupport t.hasCompactSupport).norm).mul_const _) ?_
 filter_upwards with i; rw [norm_mul]; by_cases h:i∈ tsupport t
 · exact mul_le_mul_of_nonneg_left (hc i h) (norm_nonneg _)
 simp [show t i=0 from by_contra fun w=> h (subset_closure w)]

variable (Z)
/-- Point hypotheses of Store tests in C.5 for the same purchase.
Viewers not in this hypothesis; `none`, S is the hypothesis of these true continuum estimates.
Positions & fields in P order (constant budget by each fixed v, including varying through hp by
usual multilinearity). C5 previous conclusions mean these estimates directly on fixed separated compacta.
Using particular vote/regulator forecasts would need supplying this *unchanged W* predecessor.
-/
def Session (φ:Test n)(p q h:ℕ)(τ:ℝ→ℝ)(U:ℝ→Change G h):Prop:= ∀ v:ListInput G n h, ∃ C:ℝ,0≤C ∧ ∀ᶠ r in trail,∀ x∈ tsupport φ,
     ‖frank F J none h r x v - appointedH140Crop q (τ r) (sent A h x (stand (U r) ∘ v))‖ ≤ C*g∴ r^(p+1)
-- property of the tower W (exercised by actual using prescription fit from Leading, not an infinite-stock budget)
def FitsSat (h:ℕ) : Prop:= ∀ᶠ r in trail, ∃ W: Prediction G h, (Z.store.measure h).D W=(Z.store.measure h).D (reference G h) ∧
    ∀ n (s:Test n)(v:ListInput G n h), s.applyTo (fun x=> frank F J none h r x v)= W n s v
local notation "Sat"=> Z.store.measure h
variable {Z}
variable (D:Fray ((WilsonPrescription.store Z).measure h))
   (Y:ℝ→Change G h)(τ:ℝ→ℝ)
local notation "X"=> guide G h
local notation "m*"=> fun (r:ℝ)=> Normalize.recruit (stand (Y r)) (goal Z M h q (τ r))
include H
private lemma front (i:Fin D.n)(H₀: Session F J Z (D.scope i).t p q h τ Y):∃ C:ℝ,0≤C ∧ ∀ᶠ r in trail, ‖watch (D.scope i) (m* r)- (D.scope i).t.applyTo
    (fun x=> frank F J none h r x (D.scope i).p)‖ ≤ C*g∴ r^(p+1):= by
 let t:=(D.scope i).t; let v:= (D.scope i).p; let b:= (∫ x,‖t x‖); have ha:b≥0:= integral_nonneg fun x=> norm_nonneg _
 obtain ⟨c,hc,H'⟩:= H₀ v; refine ⟨b*c, mul_nonneg ha hc,?_⟩; filter_upwards [H', (show ∀ᶠ r in trail,0<r from self_mem_nhdsWithin)] with r hr hf
 let P(x):= appointedH140Crop q (τ r) (sent A h x (stand (Y r) ∘ v))
 have he:watch (D.scope i) (m* r)=t.applyTo P:= usable Z M H ..
 rw [he, mul_assoc,norm_sub_rev]; exact apply_gap t (true_views F J none hf v).continuousOn (sheltered Z M H _ _ _) hr

lemma forecast (H₀: FitsSat F J Z h) (ht:Tendsto τ trail (𝓝 0))(hx:Tendsto (fun r=>X (Y r)) trail (𝓝 0))
    (HP: ∀ i:Fin D.n, Session F J Z (D.scope i).t p q h τ Y): ∃ C:ℝ,0≤C ∧ ∀ᶠ r in trail, ‖X (Y r)‖≤ C*g∴ r^(p+1):= by
 choose c hc H' using fun i=> front F J M H D Y τ i (HP i); let u : ℝ:= ∑ i,c i; have hh:0≤u:= Finset.sum_nonneg (fun i _=> hc i)
 refine ⟨2*(‖D.stamps‖*u),by positivity,?_⟩; filter_upwards [sensation M H D q τ Y ht hx,H₀, eventually_all.mpr H',strength_positive hG] with r hr hf hP hp
 obtain ⟨M',h',hb⟩:= hf; let W:=fun j=> watch (D.scope j) ((m*) r)- watch (D.scope j) M'; let v:= (g∴ r)^(p+1); have hv:0≤v:= by apply pow_nonneg hp.le
 have he: D.stamps W= X ((Sat).D ((m*) r))-X ((Sat).D (reference G h)):=by
    change X (D.tally W) = _; rw [show W=(fun i=> watch (D.scope i) ((m*) r))-(fun i=> watch (D.scope i) M') from rfl,map_sub,map_sub,D.equal,D.equal,h']
 rw [← he] at hr; have hA : ‖W‖ ≤ u*v:= by
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg hh hv)).2; intro i; have := hb (D.scope i).n (D.scope i).t (D.scope i).p; specialize hP i; rw [this] at hP; exact hP.trans (mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun i _=> hc i) (Finset.mem_univ _)) hv)
 refine hr.trans ( (mul_le_mul_of_nonneg_left ((D.stamps.le_opNorm W).trans (mul_le_mul_of_nonneg_left hA (norm_nonneg _))) (show (0:ℝ)≤2 by norm_num)).trans_eq (by simp only [mul_assoc,v]))

-- strengthen to actual first estimate of (F.3) and price on Dcash when needed
omit H
include hG in
lemma Trial_coupling (τ:ℝ→ℝ)(ht:Tendsto (fun r=> τ r/g∴ r) trail (𝓝 1)): Coupling G τ:= by
 have hf : ∀ᶠ r in trail,0 < τ r:=by
    filter_upwards [strength_positive hG, ht.eventually_const_lt zero_lt_one] with r hr h; exact (lt_of_lt_of_le (mul_pos h hr) (by rw [div_mul_cancel₀ _ hr.ne']))
 refine ⟨hf,?_⟩
 have hv:= (strength_coupling hG).running.mul (ht.pow 2); rw [one_pow,mul_one] at hv
 refine hv.congr' ((strength_positive hG).mono (fun r hr=>?_)); field_simp
end YM.Integration.GradedFar.Tariff.Ballot
