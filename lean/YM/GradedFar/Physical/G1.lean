import YM.GradedFar.Physical.Reverse

/-!
 State (G.1) on any fixed log span, no extra PoseFit orientation hypothesis needed.
-/
namespace YM.FVA2.GradedFar.Physical.ScaleBudget
noncomputable section
open Filter Function Real PowerSeries Set Asymptotics
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Score O.Enh Moving Growth Pose Books Scale Dframe
open Continuation Continuation.Window
open MS.Book.Program
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

variable {C:ℝ} (hz:∀ᶠ i in T, z i∈Icc 0 C)
local notation "δ"=>fun i=>resize (r i) (-(z i))
include H Q hr hz
lemma reversed_at (hp:1≤p) : Buys T (fun i=>theta_err N M θ p (r i) (-z i)) L (p+1) ∧ Buys T (fun i=>frame_err N M (Z d) θ p (r i) (-z i)) L (p+1) := by
    let v i:=δ i; have he:Tendsto v T τ:= by
       have hf:∀ᶠ i in T,0< v i := (hr.eventually self_mem_nhdsWithin).mono fun i h=> mul_pos (show 0 < r i from h) (exp_pos _)
       refine tendsto_nhdsWithin_iff.mpr ⟨squeeze_zero' (hf.mono fun i h=>h.le) ?_ ((tendsto_nhdsWithin_iff.mp hr).1),hf⟩
       filter_upwards [hr.eventually self_mem_nhdsWithin,hz] with i (hi:0<r i) hz
       apply mul_le_of_le_one_right hi.le; exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr hz.1)
    have hv i:resize (v i) (z i)=r i:=by unfold v resize; rw [mul_assoc,← exp_add,neg_add_cancel,exp_zero,mul_one]
    have h0 (a:ℕ): (fun i=>g (v i)^a)=O[T] (fun i=> L i^a) := by
       have h : Tendsto (fun i=> g (r i) / g (v i)) T (𝓝 1) := by
         have hA:=Loft.gskin _ simple (arriving N M H U J K θ Q T he hz); refine hA.congr (fun i=>?_)
         change g (resize (v i) (z i)) /_= _; rw [hv]; rfl
       apply IsBigO.of_bound (2^a); filter_upwards [h.eventually (lt_mem_nhds (show (1/2:ℝ)<1 from by norm_num)),he.eventually (positive_g simple), hr.eventually (positive_g simple)] with i hi hr ht
       simp only [Real.norm_of_nonneg (pow_nonneg (show 0≤ L i from ht.le) a),Real.norm_of_nonneg (pow_nonneg hr.le a)]; rw [← mul_pow]; gcongr; apply le_of_lt; exact (show g (v i) < 2* g (r i) by linarith only [(lt_div_iff₀ hr).1 hi])
    obtain ⟨hx,hR⟩:= reversing (d:=d) N M H U J K θ Q T he hz hp; simp_rw [hv] at hx hR
    exact ⟨IsBigO.norm_left (hx.trans (h0 (p+1))), IsBigO.norm_left (hR.trans (h0 (p+1)))⟩

set_option linter.unusedVariables false in
lemma onward (hp:1≤p): Buys T (fun i=> theta_err N M θ p (r i) (z i)) L (p+1) ∧ Buys T (fun i=> frame_err N M (Z d) θ p (r i) (z i)) L (p+1):= by
   obtain ⟨hx,hr⟩:= going (p:=p) (d:=d) N M H U J K θ Q T hr hz; exact ⟨hx.2.norm_left,hr.2.norm_left⟩
def money (p d:ℕ)(r s:ℝ):= theta_err N M θ p r s + frame_err N M (Z d) θ p r s
omit H Q hr hz in
private lemma positive_cost (p d:ℕ)(r s:ℝ):0 ≤ money N M K θ p d r s := add_nonneg (show 0≤theta_err .. from norm_nonneg _) (show 0≤frame_err .. from norm_nonneg _)
omit hr hz in
/-- QScale (G.1) all fixed compact log apertures, whether r or s is larger. Represent
 `s=r exp z`, i.e. `z=-η`, can choose L to cover any compact interval of η.
 Keep this same `Measure.start` and `K`, matrix norm in Chair. Other order demands (including
 for *all* powers up to given p), intersect eventual onsets for such finite billing. -/
theorem G1_other (v:ℝ)(p d:ℕ)(hp:1≤p): ∃ C:ℝ,0<C ∧ ∀ᶠ r in τ, ∀ s:ℝ,|s|≤v → money N M K θ p d r s ≤ C*g r^(p+1) := by
   let I:= ℝ × ↥(Icc 0 v); let r : I → ℝ:=Prod.fst; let z (i:I):=i.2.val; let f:=comap r τ
   obtain ⟨hr,hζ⟩ : Tendsto r f τ ∧ (∀ᶠ i in f,z i∈ Icc 0 v) := ⟨tendsto_comap, Eventually.of_forall (fun i=> i.2.property)⟩
   obtain ⟨hx,hR⟩:=reversed_at (d:=d) N M H U J K θ Q f hr hζ hp; obtain ⟨hx',hR'⟩:= onward (d:=d) N M H U J K θ Q f hr hζ hp
   obtain ⟨C,hC,H⟩:= (hx.add hR).exists_pos; obtain ⟨D,hD,P⟩:= (hx'.add hR').exists_pos
   refine ⟨max C D, lt_max_of_lt_left hC,?_⟩; filter_upwards [eventually_comap.mp H.bound,eventually_comap.mp P.bound,positive_g simple] with i h hp hg s hs
   by_cases h0: 0 ≤ s
   · have hz:= hp ((i,⟨s,h0,(le_abs_self s).trans hs⟩):I) rfl
     change ‖money N M K θ p d i s‖ ≤ D*‖g i^(p+1)‖ at hz
     rw [Real.norm_of_nonneg (by positivity : 0 ≤ (g i)^(p+1)), Real.norm_of_nonneg (positive_cost ..)] at hz; exact hz.trans (mul_le_mul_of_nonneg_right (le_max_right C D) (by positivity))
   rw [abs_of_neg (not_le.mp h0)] at hs
   have hi:= h ((i,⟨-s,(by linarith),hs⟩):I) rfl
   change ‖money N M K θ p d i (- -s)‖≤ C*‖g i^(p+1)‖ at hi
   rw [neg_neg,Real.norm_of_nonneg (positive_cost ..), Real.norm_of_nonneg (by positivity)] at hi
   exact hi.trans (mul_le_mul_of_nonneg_right (le_max_left C D) (by positivity))
end
end YM.FVA2.GradedFar.Physical.ScaleBudget
