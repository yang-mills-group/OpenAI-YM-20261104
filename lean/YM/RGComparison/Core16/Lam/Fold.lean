import YM.RGComparison.Core16.Lam.Score
import YM.RGComparison.Core16.Silk.Hill
/-!
# Tag-aware polynomial & critical points reading rotor
On same unnormalized FULL moment Φ support. Hear Theta connections in posterior even where
branch potentials nonsmooth sliding θ. Restriction renderer mask supports still encrypted elsewhere;
this is actual-output intrinsic calculus.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Lam
open Function Filter Lattice RG Tree Wilson MeasureTheory Metric Lumen Lumen.Planet Forge
open PertExtension PertExtension.Series Tested Radial Gravity Finset
open Precision Push.BetaTransport Next.Fluctuations Pressure
open Parcel Parcel.Oven Forge.Hut
open scoped Topology ContDiff BigOperators Classical InnerProductSpace Matrix.Norms.Frobenius
variable {G:Gauge}{c f:Side}(S:StepData c f)(T : Forest S.ratio)
variable {P:Oven S.patch}{X:Shelf G (PlaqAxes⊕Axis) P.Xways}
local notation "M"=> skillet G T.Free

-- pinned at UNIT output; no replacing denominator of Recomputed packet.
def intake (P:News G c→ℝ)(g:ℝ)(u:Sky G T.Free):=
   ∑ k:S.Choices, bonnet S T k g 0 u*P (fire S T k u)
def scoop (P:News G c→ℝ)(g:ℝ)(u:Sky G T.Free) := intake S T P g u / (Hut.seam S T (1: Config G c)).output g u

def gear (X:Shelf G (PlaqAxes ⊕ Axis) P.Xways):= Spool.lens (S:=S) 0 X T
lemma record (g:ℝ)(x:Sky G T.Free) : (gear S T X).bureau g x= (Hut.seam S T (1: Config G c)).output g x:=by
    change (Hut.seam S T (slice (0: Directions G c) g)).output g x =_; rw [show slice (0:Directions G c) g= _ from (by ext1 i; rw [Oven.slice, Pi.zero_apply, smul_zero,G.mat_lieExp_zero]; rfl : slice (0:Directions G c) g=1)] -- binder check
lemma paint {P:Oven S.patch}{X:P.Form G}(he:P.Offers X S.kernel)(hS:Bid.Larger (G:=G) S): (gear S T X).Steady := paints T he (fun i=> by simp [he.good.thick.1.le]) hS

variable (hX:P.Offers X S.kernel) (H:Bid.Larger (G:=G) S) {K:News G c→ℝ}{g:ℝ}
variable (hK:ContDiff ℝ ∞ K) (e:amen X g)
include hX H e
local notation "W"=> gear S T X
omit hX H e in
lemma occupation (x: Sky G T.Free) : (W).bureau g x=∑ k:S.Choices, bonnet S T k g 0 x:= by -- unused assurances?
    rw [record,← Lam.statue]; exact ceremony ..

include hK
lemma turned_bill : Measurable (scoop S T K g) ∧ port S T g K= (W).expect g (scoop S T K g):= by
    let u:= Lam.collects (G:=G) S T g 0
    have h t:=huts S T t H.1
    have hv t : Integrable (bonnet (G:=G) S T t g 0) M := by change Integrable (fun x=> leaf S g (fire S T t x) (0:Directions G c)) _; simpa only [Pi.one_apply,mul_one] using Lam.at_helm S T t H.1 (F:= 1) contDiff_const g -- up to mul_one
    have hk: (∫ x, (W).bureau g x∂M)=u:=by simp_rw [occupation S T (X:=X) (g:=g)]; rw [integral_finsetSum _ (fun i _=>hv i)]; rfl
    have hx v:(W).bureau g v*scoop S T K g v=intake S T K g v:=by
         unfold scoop; rw [←record (X:=X)]; exact mul_div_cancel₀ _ (bureau_pos (paint S T hX H) e v|>.ne') -- check
    constructor
    · refine (Finset.measurable_fun_sum _ (fun t _=>?_)).div ?_
      · -- product news on compact sweep
        have h : Measurable (fire S T t (G:=G)):= (h t).choose_spec.2.2
        have he:Continuous (fun t:News G c => leaf S g t 0) := (flavor S g).continuous.comp (f:=fun t:News G c => (0,t)) (continuous_const.prodMk continuous_id)
        exact ((he.measurable.comp h).mul ((show Continuous K from hK.continuous).measurable.comp h))
      rw [show (Hut.seam S T (1:Config G c)).output g= _ from (funext (record (X:=X) S T g)).symm]; exact (bureau_env (paint S T hX H) e).meas
    unfold Planet.expect Planet.pot; rw [hk]; simp_rw [hx, Lam.intake]; simp_rw [bonnet]; rw [integral_finsetSum _ (fun t _=> at_helm S T t H.1 hK g)]; rfl

omit hK in
lemma bounded {x:Sky G T.Free}{v:ℝ}(h:∀ t, |K (fire S T t x)| ≤ v):|scoop S T K g x| ≤ v:=by
    unfold scoop; rw [← record (X:=X)]; have hp:= bureau_pos (paint S T hX H) e x; rw [abs_div,abs_of_pos hp,div_le_iff₀ hp,occupation S T (X:=X) (g:=g),mul_sum]; refine (abs_sum_le_sum_abs ..).trans (sum_le_sum fun i _=>?_); rw [abs_mul, abs_of_nonneg (show 0≤bonnet S T i g 0 x from ?_)]; apply (mul_le_mul_of_nonneg_left (h i) ?_).trans (le_of_eq (mul_comm ..)); all_goals rw [leaflet]; apply mul_nonneg (S.likelihood_pos ..) (Base.cash_pos ..|>.le)

omit hK in
lemma pure {x:Sky G T.Free}{v:ℝ}(h:∀ t, K (fire S T t x)=v):scoop S T K g x=v:=by
    unfold scoop intake; simp_rw [h,←sum_mul]; rw [← occupation S T (X:=X) (g:=g), ← record (X:=X), mul_comm, mul_div_cancel_right₀ _ (bureau_pos (paint S T hX H) e x|>.ne')]
end YM.RGComparison.Core16.Lam
