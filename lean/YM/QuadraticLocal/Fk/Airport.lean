import YM.QuadraticLocal.Fk.Clear
import YM.QuadraticLocal.Fk.RadialS
/-!
# Integrable presidency. Assemble TRUE `Bulk.Colors` for countably-supported mark loads

Purely finite-period legitimacy. Not pricing a volume norm from a pointwise supremum!
Here kernels carry their exponential stencil costs in `Offers`; `Air.Season.Scope` may
be supplied on any tight array before sending. `Well` used in analytic comparison to check
same coupling factors, all gauge invariance readings and trajectory extension. Arrival still
needs Fk boolean charge and summability of its coefficients with the alias budget separately.

No finite cutoff in these constructions. Some proofs support any Type.Card, but nilpotent
interaction created on `Fintype V` native board. Don't use `Powers` to vary ι without
including actual mask predicates.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Earn
open Function Filter Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis Bid Planned.JetPort
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open AbsoluteSums Org Poll
open AllOrder AllOrder.Ker AllOrder.Ker.Start AllOrder.Haiku AllOrder.Haiku.Coat AllOrder.Fire PertExtension.Series Radial
open AllOrder.Laplace AllOrder.Laplace.SigmaP Response AllOrder.Ink AllOrder.Ink.Method AllOrder.Ink.Money Laurent Stationary
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open PositionX.Jet Extra.Iteration AllOrder.Catch AllOrder.Catch.Clock AllOrder.Floe AllOrder.Plateau
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {V:Type}{G:Gauge} {n c:Side} {k j d r:ℕ} {a b σ :ℝ}
open Aperture Poetry Echo Work.G05 Toggle Aux Aux.Name Marker Multi
open QuadraticLocal.Sunrise
variable {ι α : Type} [DecidableEq V] {P:Passport n V} {R:Census V}
variable (M:ι→ Row P R G α)
namespace Air
variable (q:ι→ℂ)(w:V→ℕ)
set_option quotPrecheck false
abbrev total (σ:ℝ)(x:ι): ℝ:= ‖q x‖ * (M x).atom.budget σ
local notation "Ω"=> Air.total M q
-- any width may use. need positivity.S families.
structure Staff (a:ℝ)(J:ℕ):Prop where
    entering : 0 < a
    written : ∀ i, (M i).lamp.toll= Launch.index R w (M i).mode
    lamps : ∀ i, (M i).lamp.r ≤ J
    couplings : ∀ i, (M i).lamp.stamp ≤ J
    payment : Summable (Air.total M q a)
variable (U:Staff M q w a k)
local notation "R₁"=> Work.F02.radius a
open Comparison.RG02 Comparison.RG02.Bulk Work.F02
variable (v:ι)
local notation "R₀"=> (M v)
local notation "Xn"=> Config G n
local notation "J"=> Work.F02.Ambient G n

def prepared (i:ι)(z:ℂ × Work.F02.Ambient G n):ℂ:= q i * ( z.1^(M i).lamp.stamp * Work.F02.atomExt (M i).atom (M i).center z.2 )
local notation "F"=> ScatterR.familyAt M q
local notation "D"=> Air.prepared M q
local notation "A"=> ℂ × Work.F02.Ambient G n
variable (P':Config G n)(x:ℝ)
lemma recognizable : prepared M q v (Complex.ofReal x,physical P')=ScatterR.familyAt M q v x P' := by unfold prepared ScatterR.familyAt Loan.letter; rw [atomExt_physical]; push_cast; rfl -- pow syntax
lemma smooth : ContDiff ℂ ω (Air.prepared M q v) := contDiff_const.mul ( (contDiff_fst.pow _).mul ((atomExt_contDiff _ _).comp contDiff_snd))
local notation "T₀"=> Work.F02.radius a
local notation "P₀"=> Work.F02.physical P'
def allowance (G:Gauge)(r:ℝ) (Jp:ℕ)(x:ℝ):ℝ := |(1+|x|+ Work.F02.radius r)^Jp * (1+|Work.F02.slotConst G|)^Jp|
local notation "λ₁"=> Air.allowance G a k x
local notation "A0" x:max=> 1 +|x| + Work.F02.radius a
variable {z:ℂ}{M0:Work.F02.Ambient G n}
include U
lemma fare {g:ℂ×Work.F02.Ambient G n} (he:g ∈ ball ( Complex.ofReal x,Work.F02.physical P') (Work.F02.radius a)): ‖ Air.prepared M q v g‖≤ (Air.total M q a v)* allowance G a k x:= by
 let θ:=Work.F02.radius a; let v₀:=Work.F02.slotConst G; let Y:= ‖q v‖; let b:= (R₀).atom.budget a; let P:ℝ:= 1+ |x|+θ; have hP : 1≤ P:=by unfold P θ; linarith only [abs_nonneg x,(Work.F02.radius_pos U.entering)]
 let L:= (1+|v₀|); have hL:1≤L:= le_add_of_nonneg_right (abs_nonneg _)
 let k' := min k ((R₀).lamp.r); unfold prepared; rw [norm_mul,norm_mul,norm_pow]; have hy : |v₀^ ( (R₀).lamp.r)| ≤ L^k:= by rw [abs_pow]; apply le_trans (pow_le_pow_left₀ (abs_nonneg _) (b:=1+|v₀|) (le_add_of_nonneg_left zero_le_one) _) (pow_le_pow_right₀ hL (U.lamps v))
 have hp:0 ≤ b:= Plateau.paid_nonneg ..; have hM : ‖atomExt (M v).atom (M v).center g.2‖≤ b* L^k:= le_trans (atomExt_bound _ P' U.entering g.2 ((le_max_right (dist g.1 (Complex.ofReal x)) (dist g.2 P₀)).trans (show _ ≤ _ from he.le)) _) (mul_le_mul_of_nonneg_left ((le_abs_self _).trans hy) hp) -- replace
 have hg:g.1∈ball (Complex.ofReal x) θ:=by
    change dist _ _ < _; exact (le_max_left (dist _ _) (dist g.2 P₀)).trans_lt he
 have hp' : ‖g.1‖ ≤ P:= by
    have h₁:= norm_le_norm_add_norm_sub' g.1 (Complex.ofReal x); rw [Metric.mem_ball,dist_eq_norm] at hg; rw [Complex.norm_real, Real.norm_eq_abs] at h₁; unfold P; linarith
 calc _ ≤ Y* (P^k*(b*L^k)) := mul_le_mul_of_nonneg_left (mul_le_mul ( (pow_le_pow_left₀ (norm_nonneg _) hp' _).trans (pow_le_pow_right₀ hP (U.couplings v)) ) hM (norm_nonneg _) (pow_nonneg (le_trans zero_le_one hP) _)) (norm_nonneg _)
      _ = Y*b*(P^k* L^k):=by ring
      _ ≤ _:= mul_le_mul_of_nonneg_left (le_abs_self _) (mul_nonneg (norm_nonneg _) hp)
-- Sum any membership on TRUE terms (or even stamp.Auth.State ARM). price converges *modes by spelling*. choose width from caller
variable (μ : ι→Prop)
local notation "H" i:max=> (if μ i then Air.prepared M q i else 0)
def sums (g:ℝ)(x:Config G n):ℂ:= ∑' i,if μ i then ScatterR.familyAt M q i g x else 0
local notation "A₁"=> Air.sums M q μ
-- normal bounds.W.One.Page.Owner.Service.Reg.State. impulse U on any test.Memory.
lemma allowance_always : ‖(if μ v then ScatterR.familyAt M q v x P' else 0)‖ ≤ Air.total M q a v * allowance G a k x:= by
 have he:= Air.fare M q w U v P' x (g:=(Complex.ofReal x,physical P')) (Metric.mem_ball_self ( Work.F02.radius_pos U.entering )); rw [← Air.recognizable M q v P' x]; split; · exact he
 exact (le_of_eq (norm_zero: ‖(0:ℂ)‖=0)).trans ((norm_nonneg _).trans he)
local notation "Z₁"=> ∑' i, if μ i then ScatterR.familyAt M q i x P' else 0
lemma usable_all : Summable (fun i=> if μ i then ScatterR.familyAt M q i x P' else 0) := Summable.of_norm_bounded (U.payment.mul_right (Air.allowance G a k x)) (fun i=> Air.allowance_always M q w U i P' x μ)
lemma continuous : Continuous (Air.sums M q μ x) := by
 unfold Air.sums; apply continuous_tsum (f:=fun i P'=> if μ i then ScatterR.familyAt M q i x P' else 0) _ ( U.payment.mul_right (Air.allowance G a k x)) (fun i P=> Air.allowance_always M q w U i P x μ);
 intro i; by_cases h:μ i; · simp_rw [if_pos h]; exact (continuous_const.mul (Complex.continuous_ofReal.comp (Loan.conti (M i|>.lamp) _ _ x)))
 simp_rw [if_neg h]; exact continuous_const

variable {E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E]
variable (t:E→ℝ)(P₁:E→ Config G n)
local notation "fℂ"=> (fun x:E=> ( Complex.ofReal (t x),Work.F02.physical (P₁ x)))
variable (y:E)(ht:ContDiffAt ℝ ω t y)(hp:∀ i,ContDiffAt ℝ ω (fun z:E=> G.mat (P₁ z i)) y)
local notation "D₀" i:max=> (fun z:ℂ × Work.F02.Ambient G n=> if μ i then Air.prepared M q i z else 0)
include U hp ht
lemma rings (j:ℕ)(v:Fin j→E):
    ContDiffAt ℝ ω (fun x=>Air.sums M q μ (t x) (P₁ x)) y ∧ HasSum (fun i=> iteratedFDeriv ℝ j (fun x=> if μ i then ScatterR.familyAt M q i (t x) (P₁ x) else 0) y v) (iteratedFDeriv ℝ j (fun x=> Air.sums M q μ (t x) (P₁ x)) y v):= by
 let Aℂ := (fℂ); let hA : ContDiffAt ℝ ω ( fℂ ) y:= ( (Complex.ofRealCLM.contDiff.contDiffAt.comp y ht)).prodMk (Work.F02.physical_contDiffAt hp); let X i (z:ℂ × Work.F02.Ambient G n):ℂ:= if μ i then Air.prepared M q i z else 0; -- X local notation error
 have Hx i: ContDiff ℂ ω (X i) := by by_cases h:μ i; simp_rw [X,if_pos h]; exact Air.smooth ..; simp_rw [X,if_neg h]; exact contDiff_const
 have hx(i:ι)(z:ℂ×Ambient G n)(he:z∈ball (Aℂ y) (Work.F02.radius a)): ‖X i z‖ ≤ Air.total M q a i* Air.allowance G a k (t y):= by
    have hp:=Air.fare M q w U i (P₁ y) (t y) he; unfold X; split; exact hp; rw [norm_zero]; exact (norm_nonneg _).trans hp
 let v' t':= ∑' i,X i (Aℂ t'); let u i (x:E):ℂ:= if μ i then ScatterR.familyAt M q i (t x) (P₁ x) else 0; have he i: u i=X i ∘ Aℂ:= by ext1 z; unfold X u Function.comp Aℂ; simp only [recognizable]
 have hv: (fun z=> Air.sums M q μ (t z) (P₁ z))=v':= funext (fun z=> tsum_congr (fun i=> congr_fun (he i) z))
 rw [hv]; have hV:= ( U.payment.mul_right (Air.allowance G a k (t y))); refine ⟨Brilliant.path (Aℂ) y hA (Work.F02.radius_pos U.entering) hV Hx hx,(Brilliant.attends Aℂ y hA (Work.F02.radius_pos U.entering) hV Hx hx j v).congr_fun fun i=>?_⟩; exact congr_arg (fun x=> iteratedFDeriv ℝ j x y v) (he i)
end Air
end YM.QuadraticLocal.Earn
