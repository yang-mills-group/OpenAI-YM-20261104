import YM.MS.Drops.Mint
import YangMills.WilsonProof.NativeSupport.YM.MS.Rake.Sequence
/-! Radian to MS chart.
Dimension fixed=4. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Drops
open Set Function Filter Finset Metric MeasureTheory Real
open Tensor Koszul Plane Landau Detect Detect.Mark Local.BV InnerProductSpace Submodule Momentum Local Woven Color Physical Menus
open Analysis Labels Maxwell Theater Next Next.Rank Next.Rank.Beamer Tone High Rake Osc Snap
open Complex (I)
open scoped Topology ContDiff BigOperators RealInnerProductSpace
open City Latch
open Next.Rank.Radian
variable {G:Gauge}
-- note opened Radian. enforce ℕ∞
lemma left_M {p:ℝ}(hp:0<p)(k:ℕ) : Integrable (fun w:E4=> ‖w‖^k * ‖major p w‖):= by
   obtain ⟨C,hc,hC⟩:= warmth k p hp; have hz(s q:ℝ): ‖( ↑(exp (-s*q^2)):ℂ)‖=exp (-s*q^2):= Eq.trans (Complex.norm_real _) (Real.norm_of_nonneg (exp_pos _|>.le))
   refine ((glowing (show 0<p/2 by positivity)).norm.const_mul C ).mono' ((continuous_norm.pow k).aestronglyMeasurable.mul (( glowing hp ).aestronglyMeasurable.norm)) ?_; exact Eventually.of_forall (fun w=>by rw [Real.norm_of_nonneg ( by positivity )]; unfold major; simp only [hz]; exact hC w) -- p implicit
lemma majorM {p:ℝ}(hp:0<p): Radian.Moment (major p):=⟨glowing hp,fun _=> left_M hp _⟩
variable (L K:Degree G)
local notation "U" => xy (fax L) (fax K)
def dark_s (p:FourP)(s:ℝ) : ℂ := (Landau.low (exp s) p / Momentum.sq p:ℝ)
abbrev Pay (s:ℝ):= exp s ^2 * τ^2
def leaseTax (s:ℝ) (w:E4):= major ( Pay s ) w
lemma sq_LP (s:ℝ)(w:E4) : leaseTax s w=(exp (-(exp s)^2 * Momentum.sq (ν w)):ℝ):= by rw [ ν_sq ]; unfold leaseTax major Pay; congr 2; ring -- ensure levels ℝ
abbrev wearΦ (s:ℝ)(w:E4): ℂ:= U ( ν w ) * dark_s (ν w) s
abbrev stage0 (s:ℝ)(w:E4) : ℂ:= -2 * Cdeg (fax L) (fax K) s (ν w)
lemma stage_v (s:ℝ)(w:E4): stage0 L K s w= U (ν w)* ( (-2*(exp s)^4*Momentum.sq (ν w):ℝ):ℂ )*leaseTax s w:= by
    unfold stage0; rw [ vertical (wholeℓ _) (wholeℓ _),sq_LP ]; unfold Rad City.brush; push_cast; simp only [neg_mul]; ring -- fax binds
lemma dark_out (w:FourP)(s:ℝ): HasDerivAt (dark_s w) (((-2 :ℝ)* Rad s w* Momentum.sq w:ℝ):ℂ) s:= by
    obtain hT:= City.xH (exp s) w; let q:= Momentum.sq w; convert! (((hT.comp s ( hasDerivAt_exp s )).div_const q ).ofReal_comp) using 1; change _= (((-2 * _ * _ * _) / q:ℝ):ℂ); unfold Rad; by_cases h:q=0; · change ( ( ( (-2:ℝ)*_* q ):ℝ ):ℂ )=_; change (↑(((-2:ℝ)* _) * q):ℂ)=_; simp [h]
    unfold q at *; push_cast; field_simp
lemma dark_w (w:E4)(s:ℝ): HasDerivAt (fun t=> wearΦ L K t w) (stage0 L K s w) s := by
    unfold stage0; rw [ vertical ( wholeℓ .. ) ( wholeℓ .. ) (ν w) ]; convert! (dark_out (ν w) s).const_mul ( U ( ν w ) ) using 1; push_cast; ring
lemma lease_s (s:ℝ)(w:E4)(hw:w≠0): wearΦ L K s w= U (ν w)*liturgy (Pay s) w + exp s^2 • ( U (ν w)* major (Pay s) w ):= by
    unfold wearΦ dark_s; rw [ show Landau.low (exp s) (ν w) = _ from (show _= (1+( exp s )^2* Momentum.sq ( ν w ))* exp ( -(exp s)^2 * Momentum.sq ( ν w ) ) by unfold Landau.low coat; simp only [scaling] <;> ring ) ]; -- cast order
    let Q:= Momentum.sq (ν w); have hQ: Q≠0:= by unfold Q; rw [ ν_sq ]; unfold τ; have h:=norm_pos_iff.mpr hw; positivity
    rw [Complex.ofReal_div, Complex.ofReal_mul, show (↑(exp (- exp s^2 * Momentum.sq (ν w))):ℂ) = leaseTax s w from (sq_LP ..).symm ] -- after push cast
    have ht: Maxwell.normal=(τ^2)⁻¹:= by unfold Maxwell.normal τ; ring_nf
    unfold liturgy leaseTax; rw [ν_sq,ht]; unfold τ; have he:= Real.pi_pos; have hv:= norm_pos_iff.mpr hw; have hh:(‖w‖:ℂ) ≠ 0 := by exact_mod_cast hv.ne'
    have hx:(↑π:ℂ)≠0:= by exact_mod_cast he.ne'
    push_cast [Complex.real_smul]; field_simp <;> ring
lemma downE (L K:Degree G){φ:E4→ℂ}(h:Radian.Moment φ): Radian.Moment (fun w:E4=> xy (fax L) (fax K) (ν w)*φ w):= by rw [show (fun w:E4=> _)=_ from funext (front L K φ) ]; exact Moment.assemble L K _ fun i j=> Moment.pressed _ h
end YM.MS.Drops
