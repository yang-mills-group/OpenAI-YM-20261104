import YM.GradedFar.Growth.Lips

/-!
# Keep estimates over a chain of bona fide homes and frame operators

Input for now: compact-step assertion, any p≥1, before even choosing B.
-/
namespace YM.FVA2.GradedFar.Growth
noncomputable section
open Filter Function Real PowerSeries Set Asymptotics
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Score O.Enh O.Canon Scale Dframe Jury
open Continuation
open scoped Topology BigOperators Classical ContDiff
open MS.Book.Program
variable {G : Gauge} {n d : ℕ} {I J E : Type} (N : WilsonPrescription G)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
local notation "τ"=>𝓝[>] (0:ℝ)
local notation "g"=>gYM G

-- r argument remains at original meter in these operators. Define without re-expression!
abbrev Coven (G : Gauge) d := ℝ → ℝ → Maps G d
abbrev travels (Z : Coven G d) := (∀ r, Z r 0=1) ∧ ∀ r s t, Z r (s+t)=Z r s * Z (r*exp s) t

section
variable (Z : Coven G d) (θ : ℝ→ℝ) (p : ℕ)
def theta_err (r s : ℝ) := ‖(θ (r*exp s):ℂ)-bend N M s p (θ r:ℂ)‖
def frame_err (r s : ℝ) := ‖Z r s-crank N M d s p (θ r:ℂ)‖
def PTheta := ∃ C:ℝ, 0 < C ∧ ∀ᶠ r in τ,∀ s∈Small, theta_err N M θ p r s≤ C*g r^(p+1)
def PFrame := ∃ C:ℝ, 0 < C ∧ ∀ᶠ r in τ,∀ s∈Small, frame_err N M Z θ p r s≤ C*g r^(p+1)
def Kind (Y : ℝ) := ∀ᶠ r in τ, ∀ s∈Small,‖Z r s‖≤Y
end

variable {simple : G.Simple} {A : Prescription (Press.portDeck G)} (H : Main.Match N simple M A true)
variable (Z : Coven G d) (θ : ℝ→ℝ) (ht : Tendsto (fun r=>θ r/gYM G r) τ (𝓝 1))
    (Q : Loft G I) (s z : I → ℝ) (hs : Q.Mid s) (hz : ∀ᶠ i in Q.path, z i∈Small)
local notation "W"=> Q.board simple
include H ht
-- Need Kind constant fixed independently of p for the iteration count
lemma kind_choice (h : PFrame N M Z θ 1) : ∃ Y : ℝ, 1≤Y ∧ Kind Z Y := by
  obtain ⟨C,hC,h⟩:=h
  have hρ : Continuous (fun v:ℝ × ℝ => crank N M d v.1 1 (v.2:ℂ)) := by
    unfold crank blend
    refine continuous_finsetSum _ (fun i _=> ?_); exact ((Complex.continuous_ofReal.comp continuous_snd).pow i).smul
      ((Kcontinuity N M H i d).comp continuous_fst)
  obtain ⟨D,hD⟩:= (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn (s:=Small ×ˢ Icc (0:ℝ) 1) hρ.continuousOn
  refine ⟨max 1 (C+D),le_max_left ..,?_⟩
  filter_upwards [h,paid_reading simple _ ht, (shrink simple).eventually_lt_const zero_lt_one] with r h ⟨hp,hg,ha,_⟩ hc
  intro s hs; have hi:= h s hs; have hh : ‖crank N M d s 1 (θ r:ℂ)‖ ≤ D:= hD (s,θ r) ⟨hs,hg.le,(le_abs_self _).trans ha⟩
  let B:=crank N M d s 1 (θ r:ℂ); apply le_trans _ (le_max_right ..); rw [← sub_add_cancel (Z r s) B]
  exact (norm_add_le ..).trans (add_le_add (hi.trans ((mul_le_mul_of_nonneg_left (pow_le_one₀ hp.le hc.le) hC.le).trans_eq (mul_one _))) hh)

lemma start_theta : Bill W 1 0 (fun i=> (θ (Q.r i):ℂ)) := by
  cases H
  refine ⟨2,by norm_num,0,?_⟩; filter_upwards [Q.nearing.eventually (paid_reading simple θ ht)] with i hi
  rw [Complex.norm_real,Real.norm_eq_abs,post,neg_zero,zero_mul,exp_zero,pow_one,pow_zero,mul_one,mul_one]
  exact hi.2.2.2

include hs
lemma theta_nears : Tendsto (fun i=> ((θ (Q.r i * exp (s i)):ℂ))) Q.path (𝓝 0) := by
  have h := Complex.continuous_ofReal.continuousAt.tendsto.comp ((Pose.tainted N M θ H ht).comp (Q.soon simple hs))
  rw [Complex.ofReal_zero] at h; exact h
lemma partial_nears (p : ℕ) :
    Tendsto (fun i=> ((θ (Q.r i * exp (s i)):ℂ), bend N M (s i) p (θ (Q.r i):ℂ))) Q.path (𝓝 0) :=
   (theta_nears N M H θ ht Q s hs).prodMk_nhds (lofty N M H Q (bend_paid N M H Q s hs _ (start_theta N M H θ ht Q) p) (by simp))
include hz
omit ht in
lemma mid_case : Q.Mid z := by
  cases H
  exact (hs.and (hz.and ((Q.climbs simple).eventually_ge_atTop doubling))).mono
    (fun i ⟨_,hi,h⟩=>⟨hi.1,le_trans (show z i≤doubling from hi.2) h⟩)
omit ht in
private lemma through_cost (p : ℕ) [NormedAddCommGroup E] {P : ℝ→ℝ→E} (C : ℝ) (hc : 0 < C)
    (h : ∀ᶠ r in τ, ∀ s∈Small, ‖P r s‖ ≤ C*g r^p) : Bill W p 0 (fun i=> P (Q.r i*exp (s i)) (z i)) := by
    cases H
    refine ⟨C*2^p,by positivity,0,?_⟩
    have hA:= Q.soon simple hs
    filter_upwards [hA.eventually h,hA.eventually (positive_g simple),hz,Q.nearing.eventually (positive_g simple),
      (Q.gskin simple hs).eventually_lt_const one_lt_two] with i h hf hz hg hq
    rw [post,neg_zero,zero_mul,exp_zero,pow_zero,mul_one,mul_one]
    apply (h (z i) hz).trans
    exact ((mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hf.le ((div_lt_iff₀ hg).mp hq).le p) hc.le)).trans_eq (by rw [mul_pow,← mul_assoc]; rfl)
omit ht in
lemma through_theta (p : ℕ) (h : PTheta N M θ p) : Bill W (p+1) 0 (fun i=> theta_err N M θ p (Q.r i*exp (s i)) (z i)) := by
    obtain ⟨C,hC,h⟩:=h; unfold theta_err; exact through_cost N M H Q s z hs hz _ (P:=theta_err N M θ p) C hC (h.mono fun r h s hp=>by rw [theta_err,Real.norm_of_nonneg (norm_nonneg _)]; exact h s hp)
omit ht in
lemma through_frame (p : ℕ) (h : PFrame N M Z θ p) : Bill W (p+1) 0 (fun i=> frame_err N M Z θ p (Q.r i*exp (s i)) (z i)) := by
    obtain ⟨C,hC,h⟩:=h; unfold frame_err; exact through_cost N M H Q s z hs hz _ (P:=frame_err N M Z θ p) C hC (h.mono fun r h s hp=>by rw [frame_err,Real.norm_of_nonneg (norm_nonneg _)]; exact h s hp)
end
end YM.FVA2.GradedFar.Growth
