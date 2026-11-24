import YM.GradedFar.Placard
import YM.GradedFar.Detector
/-!
# Gram at the derivative insertion (not the receding one)

Use length normalization between 0 and 1 in averaging. The FTC variant of the first-derivative
payment avoids introducing weak derivatives, attains the same shape derivative identity and its
application to point estimates. Take none viewpoint & both fields in common cap.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Tariff
open Function Filter Set PowerSeries MeasureTheory
open Climb Extraction Table Spec PhysMS Trace.Pilot OPE OPE.Orbits
open FVA2 XSpace XSpace.Normalize FVA2.Scale FVA2.Dframe FVA2.O.Score FVA2.Register FVA2.GradedFar FVA2.O.Enh
open MS MS.Native MS.Land MS.Fleet
open Matrix
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)(J:ℝ→tower S)
   (Z:WilsonPrescription G)(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
   {hG:G.Simple}{σ:MS.Land.Prescription (Press.portDeck G)} (H:Main.Match Z hG M σ true)
local notation "X" => Scale.Measure.outlook (WilsonPrescription.scheme Z) (WilsonPrescription.criterion Z)
variable (h:ℕ) (a:Axis)
def slopePath {n:ℕ}(x v:Points n)(s:ℝ) := x+s•v
local instance {n:ℕ} : ContinuousSMul ℝ (Points n) := IsBoundedSMul.continuousSMul
lemma slopeDeriv {n:ℕ}(x v:Points n)(s:ℝ) : HasDerivAt (slopePath x v) v s:=by
 exact HasDerivAt.congr_deriv (((hasDerivAt_id' s).smul_const v).const_add x) (one_smul ℝ v)
lemma slope_chain {n:ℕ}{f:Points n→ℂ}(x v:Points n)(s:ℝ)(hf:DifferentiableAt ℝ f (slopePath x v s)) : HasDerivAt (fun s=>f (slopePath x v s))
    (fderiv ℝ f (slopePath x v s) v) s:= hf.hasFDerivAt.comp_hasDerivAt s (slopeDeriv x v s)

local notation "Σ0"=> outgoing RootG
def paving (δ s:ℝ) := slopePath Σ0 (δ • Points.direction 0 a) s
lemma track (δ:ℝ): Continuous (paving a δ):= by unfold paving slopePath; fun_prop
abbrev Street (P:Points (1+1)→ Prop) (a:Axis)(δ:ℝ):= ∀ s:ℝ,s∈uIcc (0:ℝ) 1→ P (paving a δ s)
lemma even {P:Points 2→Prop}(hp:∀ᶠ x in 𝓝 Σ0,P x): ∀ᶠ δ:ℝ in trail, Street P a δ:=by
 obtain ⟨ε,he,h⟩:= Metric.mem_nhds_iff.mp hp; let d:Points 2:=Points.direction 0 a; let L:=‖d‖+1
 have ht:0<L:=by dsimp only [L]; positivity
 filter_upwards [(gt_mem_nhds (div_pos he ht)).filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with δ hδ (hv:0<δ) s hs
 apply h; rw [uIcc_of_le zero_le_one] at hs; rw [Metric.mem_ball, paving,slopePath,dist_eq_norm,add_sub_cancel_left,norm_smul,norm_smul,Real.norm_of_nonneg hv.le,Real.norm_of_nonneg hs.1]; calc
   _ ≤ 1*(δ*L):= mul_le_mul hs.2 (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) hv.le) (by positivity) zero_le_one
   _ < _:=by rw [one_mul]; exact (lt_div_iff₀ ht).mp hδ
abbrev Paved (δ:ℝ):= Street (· ∈ conf _) a δ
lemma clear_paving : ∀ᶠ δ:ℝ in trail, Paved a δ:= even a ((conf_open _).mem_nhds ok_wall)
def carpet (u v:Sec G h): ListInput G 2 h:= combo h u v
lemma carpet_update (u v: Sec G h): carpet h u v= update (carpet h 0 v) 0 u:= by
    funext i; fin_cases i; exact (update_self (0:Fin 2) u (carpet h 0 v)).symm; exact (update_of_ne (by decide:(1:Fin 2)≠0) u (carpet h 0 v)).symm

local notation "Leg"=> Toon G h
variable (A:Arenas G)
def accounted (A:Arenas G)(h:ℕ) (x:Points 2) (i j:Toon G h):PowerSeries ℂ:= sent A h x (carpet h (theory j) (Bank.detector i))
def avenue (A:Arenas G)(h:ℕ)(a:Axis)(δ:ℝ): Matrix (Toon G h) (Toon G h) (PowerSeries ℂ) := Matrix.of (fun i j=> operand 0 1 (fun s=>accounted A h (paving a δ s) i j))
def leadGram (A:Arenas G)(h:ℕ): Matrix (Toon G h) (Toon G h) ℂ := Matrix.of (fun i j=>constantCoeff (accounted A h Σ0 i j))
include H
omit H in
lemma leading_shape (i j:Leg) : leadGram X h i j= Bank.place h (Bank.initial X h) (theory j) i := by
    rw [Bank.placed]; apply Eq.trans _ (towall h X (theory j) (Bank.detector i) 0).symm
    simp only [leadGram,accounted,carpet,sent,Matrix.of_apply,crop_eq, ← coeff_zero_eq_constantCoeff_apply,
        FormalCompact, coeff_mk]; rw [declared,dif_pos (show Σ0∈conf 2 from ok_wall)]; simp; rfl
lemma redeem : IsUnit (leadGram X h) := by
    have he (t:Sec G h) : leadGram X h *ᵥ (columns G h t)= Bank.place h (Bank.initial X h) t:= by
       let B:= Bank.place h (Bank.initial X h); conv_rhs=>rw [← all_sig t];
       funext i; unfold mulVec dotProduct; simp only [map_sum,_root_.map_smul, Finset.sum_apply,leading_shape Z,Pi.smul_apply,smul_eq_mul,columns_coord]; exact Finset.sum_congr rfl fun j _=> mul_comm ..
    refine Matrix.mulVec_injective_iff_isUnit.mp ?_
    intro x y he'; obtain ⟨x,rfl⟩:=(columns G h).surjective x; obtain ⟨y,rfl⟩:=(columns G h).surjective y
    rw [he,he] at he'; rw [Bank.detected ((H.separatedOPE 0).wilson.wardRank) he']
lemma approaches : Tendsto (fun δ=> (avenue X h a δ).map constantCoeff) trail (𝓝 (leadGram X h)) := by
    refine tendsto_pi_nhds.mpr (fun i=> tendsto_pi_nhds.mpr (fun j=> ?_))
    let v:= carpet h (theory j) (Bank.detector i); let p:= fun x:Points 2=>declared X h x 0 v
    change Tendsto (fun r=> constantCoeff (operand 0 1 (fun s=>accounted X h (paving a r s) i j))) trail _
    simp_rw [leadGram, Matrix.of_apply, ← coeff_zero_eq_constantCoeff_apply,accounted, sent,operand, coeff_mk]
    have hp:= kernel_continuous Z M H v 0; refine Metric.tendsto_nhds.mpr (fun ε hε=>?_)
    obtain hv:= even a (((hp.continuousAt ((conf_open _).mem_nhds ok_wall)).tendsto).eventually
        (Metric.ball_mem_nhds _ (half_pos hε)))
    filter_upwards [clear_paving a,hv] with δ hδ H
    have he: IntervalIntegrable (fun s=>p (paving a δ s)) volume 0 1 := (hp.comp (track a δ).continuousOn (show MapsTo (paving a δ) (uIcc (0:ℝ) 1) (conf 2) from fun _ h=>hδ _ h)).intervalIntegrable (μ:=volume)
    rw [dist_eq_norm]; change ‖(∫ s in (0:ℝ)..1,p (paving a δ s))-p Σ0‖ < _; nth_rw 1 [show p Σ0= (∫ _ in (0:ℝ)..1,p Σ0) from (by simp)]
    rw [← intervalIntegral.integral_sub he intervalIntegrable_const]; exact lt_of_le_of_lt (intervalIntegral.norm_integral_le_of_norm_le_const (C:=ε/2)
        (fun i hi=> by simpa only [Metric.mem_ball,dist_eq_norm, p] using ((H i (uIoc_subset_uIcc hi)).le))) (by rw [sub_zero, abs_one]; linarith)
lemma refunded : ∀ᶠ δ:ℝ in trail, IsUnit ((avenue X h a δ).map constantCoeff):= by
    have hx:= (show Continuous (Matrix.det (n:=Toon G h) (R:=ℂ)) from continuous_id.matrix_det).continuousAt.tendsto.comp (approaches Z M H h a); simp_rw [Matrix.isUnit_iff_isUnit_det]
    have he:= (Matrix.isUnit_iff_isUnit_det _).mp (redeem Z M H h); exact (hx.eventually (isOpen_compl_singleton.mem_nhds
       (isUnit_iff_ne_zero.mp he))).mono fun x h=>isUnit_iff_ne_zero.mpr h
end YM.Integration.GradedFar.Tariff
