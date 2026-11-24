import YM.GradedFar.Physical.Actual
import YM.GradedFar.Physical.Homet

/-! Other η in (G.1): recover all the compact steps.
-/
namespace YM.FVA2.GradedFar.Physical.ScaleBudget
noncomputable section
open Filter Function Real PowerSeries Set Asymptotics
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Score O.Enh Moving Growth Pose Books Scale Dframe
open Continuation Continuation.Window
open scoped Topology BigOperators Classical ContDiff
variable {G : Gauge} {n m d h p : ℕ} {I:Type} (N : WilsonPrescription G)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) {simple : G.Simple} {A : MS.Land.Prescription (Press.portDeck G)} (H : Main.Match N simple M A true)
local notation "τ"=>𝓝[>] (0:ℝ)
local notation "g"=>gYM G
local notation "ν"=>Teller.logNu 1
local notation "ψ"=> GroupS.ψ N.criterion M ν
variable {R : Family G} {f : Extraction.Order} {P : Table R.book}
    (U : Spec.Final R f P) (J K : FramesH P) (θ:ℝ→ℝ) (Q:Earned N M U J K θ)
    (T : Filter I) {r z:I→ℝ} (hr:Tendsto r T (𝓝[>] (0:ℝ)))
local notation "L"=> g∘ r
local notation "W"=> fun i=>resize (r i) (z i)
local notation "Z"=>fun d=> Zenith (next K d)
local notation "KP"=> fun d y=> names (Kseries N M d (-y))

variable {C:ℝ} {s:Set ℝ}(hs:IsCompact s) (hz : ∀ᶠ i in T,z i∈s)
include H hz hs
lemma point_ψ : Till T (fun i=> tells (ψ (-z i))) (gYM G∘r) p := by
   intro j hj
   obtain ⟨D,hD⟩:= hs.exists_bound_of_continuousOn (continuous_rhythm (psi_rhythm N M H j)).continuousOn
   exact budget T (hz.mono (fun i hi=> hD _ hi))
lemma point_frame : Till T (fun i=> KP d (z i)) (gYM G∘r) p :=by
   intro j hj
   obtain ⟨D,hD⟩:= hs.exists_bound_of_continuousOn (Kcontinuity N M H j d).continuousOn
   exact budget T (hz.mono (fun i hi=> hD _ hi))
omit H hs hz in
private lemma app {E:Type}[NormedAddCommGroup E] [NormedSpace ℂ E]{F:I→E}{Ax:I→Portion E}{t:I→ℂ}{l:I→ℝ}(hq:p≤d)
     (hl:Tendsto l T (𝓝 0))(ht:Buys T t l 1) (h:Till T Ax l d) (he:Buys T (fun i=> F i-blend (Ax i) d (t i)) l (p+1)):
     Pays T F Ax l p t := by
   refine ⟨fun j hj=> h j (hj.trans hq),?_⟩; have hp : Buys T (fun i=> blend (Ax i) d (t i) - blend (Ax i) p (t i)) l (p+1):= by
      unfold blend; simp_rw [← Finset.sum_Ico_eq_sub _ (Nat.succ_le_succ hq)]; apply IsBigO.sum; intro j hj; have hh:= Finset.mem_Ico.mp hj; exact budget_times_smul T (budget_growth T (budget_pow T ht j) _ hh.1 (jet_level T hl)) (h _ (Nat.lt_succ_iff.mp hh.2))
   exact (he.add hp).congr_left (fun i=> by abel)

section positive
omit hs hz
variable (hζ:∀ᶠ i in T, z i∈Icc 0 C)

include hr hζ Q
-- ensure log of width.
set_option linter.unusedSectionVars false in
lemma window_pass : ∀ᶠ i in T, exp (z i) ≤ 1*g (r i)^ (-(1:ℝ)) :=by
    filter_upwards [hr.eventually (has_room simple 1 1 zero_lt_one zero_lt_one (exp C)), hζ] with i hi hζ
    exact (exp_le_exp.mpr hζ.2).trans hi
lemma arriving : Loft.Mid (timespan (G:=G) T r hr) z := by
    filter_upwards [window_pass N M H U J K θ Q T hr hζ, hζ,hr.eventually (positive_g simple)] with i hi he hx
    refine ⟨he.1, exp_le_exp.mp (le_trans hi ?_)⟩; unfold Loft.height; rw [exp_log]; exacts [le_rfl,(show 0<1*g (r i)^ (-(1:ℝ)) from by positivity)]
lemma going : (Pays T (fun i=>(θ (W i):ℂ)) (fun i=>tells (ψ (-z i))) L p (fun i=>(θ (r i):ℂ))) ∧
      Pays T (fun i=> Z d (r i) (z i)) (fun i=> KP d (z i)) L p (fun i=>(θ (r i):ℂ)) := by
    obtain ⟨q,hq,H'⟩ := ((eventually_ge_atTop p).and (Q.main (p+1) d zero_lt_one zero_lt_one).1).exists
    have hh : Buys T (fun i=> theta_err N M θ q (r i) (z i) + frame_err N M (Z d) θ q (r i) (z i)) L (p+1) := by
       refine IsBigO.of_bound 1 ?_; filter_upwards [hζ,hr.eventually H',window_pass N M H U J K θ Q T hr hζ,hr.eventually (positive_g simple)] with i he h hx ht
       rw [Real.norm_of_nonneg (add_nonneg (show 0 ≤ theta_err .. from norm_nonneg _) (show 0≤frame_err .. from norm_nonneg _)),Real.norm_of_nonneg (pow_nonneg (show 0 ≤ L i from ht.le) _),one_mul]; exact h _ he.1 hx
    have he:=measuring T N M r hr H θ Q.clock; have hp :=(shrink simple).comp hr
    constructor
    · refine app T hq hp he (point_ψ N M H T isCompact_Icc hζ) (passes_cost T hh ?_); filter_upwards with i; rw [Real.norm_of_nonneg (add_nonneg (show 0 ≤ theta_err .. from norm_nonneg _) (show 0≤frame_err .. from norm_nonneg _))]; exact le_add_of_nonneg_right (show 0 ≤ frame_err .. from norm_nonneg _)
    refine app T hq hp he (point_frame N M H T isCompact_Icc hζ) (passes_cost T hh ?_); filter_upwards with i; rw [Real.norm_of_nonneg (add_nonneg (show 0 ≤ theta_err .. from norm_nonneg _) (show 0≤frame_err .. from norm_nonneg _))]; exact le_add_of_nonneg_left (show 0 ≤ theta_err .. from norm_nonneg _)
end positive
end
end YM.FVA2.GradedFar.Physical.ScaleBudget
