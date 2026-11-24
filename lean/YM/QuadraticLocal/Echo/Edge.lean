import YM.QuadraticLocal.Echo.Opine
/-!
 # Endpoint Frame-term accounting on aperture.Heterogenous rank held slots.Payment.We.Lift.Fixed toll only
 Does not assume exponential in SUN.Spent.Support shape.Frame representation budgets must still be settled.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Echo
open Function Filter Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis Bid Planned.JetPort
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open AbsoluteSums Org Poll
open AllOrder AllOrder.Ker AllOrder.Ker.Start AllOrder.Haiku AllOrder.Haiku.Coat AllOrder.Fire PertExtension.Series Radial
open AllOrder.Laplace AllOrder.Laplace.SigmaP Response AllOrder.Ink AllOrder.Ink.Method AllOrder.Ink.Money Laurent Stationary
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open PositionX.Jet Extra.Iteration AllOrder.Catch AllOrder.Catch.Clock AllOrder.Floe AllOrder.Plateau
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {ι:Type*} {V:Type}[Fintype V][DecidableEq V]{G:Gauge} {k j e d i:ℕ} {a σ Z τ A:ℝ} {n:Side}
open Aperture Poetry Work.G05 Toggle Aux Aux.Name
namespace Trace
variable (q:V)(W:V→Site n)(X: Lantern G V)(h:X.Bears (univ:Finset V) q k)(b:ℝ) (x:Apex n G)
local notation "ζ"=> X.atom
local notation "f"=> setX X.atom (W q)
local notation "E"=> Apex n G
local notation "Λ"=> Kinetic.Port.exteriorL G n
-- rank j≤e maybe.
def offered (e:ℕ) : Config G n→ℝ:= ratioW b e X.r • (fun A=> X.atom.unmasked A (W q))
def palette (k e:ℕ) : E→ℝ:= ratioW b e X.r • blockTaylor (k-e+X.r) (setX X.atom (W q))
local notation "r"=> X.r
lemma cloaked : Helmet.frame X.atom (W q)=setX X.atom (W q) ∘ Λ := rfl
lemma slept : f= Helmet.frame X.atom (W q) ∘ (Λ).symm := by rw [cloaked]; ext1 x; simp only [Function.comp_apply,ContinuousLinearEquiv.apply_symm_apply]
lemma virtues : Comparison.RG02.Assembly.GradeAt X.r (f):= by rw [slept]; let he: ContDiffAt ℝ ω (Λ).symm 0:= (Λ).symm.contDiff.contDiffAt (x:=0); exact Comparison.RG02.Assembly.GradeAt.coarse (Helmet.frameGrade ..) he (_root_.map_zero _)
lemma flights (v:Link G n)(j:ℕ): Radial.jet (Helmet.frame X.atom (W q)) j v=Radial.jet (f) j (Λ v):= by rw [cloaked]; exact Kinetic.pivot (Λ).toContinuousLinearMap (f) _ (virtues q W X).smooth j
-- Aggregate explicit Ticket.S.Unit on each row, filtered in charter by reader
lemma sail (hb:0<b)(he:e≤j):
 ∑ d∈ Finset.range (j+1), b^d * (if e≤d then Radial.jet (Helmet.frame X.atom (W q)) (d-e+X.r) (bend b x) else 0) = palette q W X b j e x := by
 let k':= X.r; have hh(i:ℕ)(hi:i< X.r) : Local.Pure.chip f i (Λ (bend b x))=0 := (virtues q W X).jet_z _ hi -- edit
 change _= ratioW b e X.r *blockTaylor (j-e+X.r) f x; conv_rhs=> right; right; rw [← unbend b x hb]
 rw [Local.Pure.bill_insert, show j+1=e+(j-e+1) by omega,show j-e+X.r+1 = X.r+(j-e+1) by omega,sum_range_add _ e,sum_range_add _ r];
 have he₁ : ∑ i∈ Finset.range e,b^i*(if e≤ i then Radial.jet (Helmet.frame X.atom (W q)) (i-e+X.r) (bend b x) else 0)=0:= Finset.sum_eq_zero fun i hi=> by rw [if_neg (not_le_of_gt (Finset.mem_range.mp hi))]; simp
 have he₂ : ∑ i∈ Finset.range k',b^i*Local.Pure.chip (f) i (Λ (bend b x))=0:= Finset.sum_eq_zero fun i hi=> by rw [hh i (Finset.mem_range.mp hi),mul_zero]
 rw [he₁,he₂,zero_add,zero_add,Finset.mul_sum]; apply Finset.sum_congr rfl; intro i hi; rw [if_pos (by omega),flights q W X]
 rw [show e+i-e+X.r=X.r+i by omega]; unfold ratioW; change b^ _ * _ = _ * (b^_ * Radial.jet (setX X.atom (W q)) (k'+i) _); rw [pow_add,pow_add]; field_simp; rfl
variable (ha:0<σ) (hp:PaintSupply G i Z) (e j)
local notation "V₁"=> offered q W X b e
local notation "V₂"=> palette q W X b j e
local notation "µ"=> X.money σ
local notation "D"=> branch G Z σ i X.r
local notation "θ"=> ratioW b e X.r
include hp ha
lemma ratio_nn (hb:0 < b): 0≤ ratioW b e X.r:=mul_nonneg (pow_nonneg hb.le _) (inv_nonneg.mpr (pow_nonneg hb.le _))
lemma weather (hv:0<τ)(he:τ≤1)(hb:0<b)(hx:‖x‖≤τ)(hI:j-e+X.r< i): Brush i (µ *D*θ*τ^(j-e+X.r+1)) τ⁻¹ ((offered q W X b e ∘ Desk.night)-palette q W X b j e) x:=by
 have hh(y:E)(h:‖y‖≤1): Allows i f y (µ * D):= Trace.cash X y ha hp (W q) h
 have hQ := AllOrder.Local.Taylor.forecast hv he hI (fun i hi=> Brush.offer.mpr ⟨(hh i (hi.trans he)).analytic.of_le le_top,(hh i (hi.trans he)).norm_le⟩) hx; rw [show ((offered q W X b e ∘ Desk.night)-palette q W X b j e)= θ • (f - blockTaylor (j-e+X.r) f) from (by unfold palette; rw [smul_sub]; rfl)]; have hk := hQ.smul θ; rw [Real.norm_of_nonneg (ratio_nn e X b ha hp hb)] at hk; exact hk.climb (le_of_eq (by ring)) le_rfl
-- available for infinite omitted jets at each pi value, bypass Actor.Nelm exists by using W^Cut all values. Pay enough on long kernels owner distance μ.El
lemma snips (l:ℕ)(hl:l≤ i) : |Radial.jet (f) l x| ≤ µ*D*‖x‖^l:= by
 have he := Trace.cash X (0:E) ha hp (W q) (by simp); let Z':=(iteratedFDeriv ℝ l (f) (0:E)); unfold Radial.jet; rw [abs_mul]; refine (mul_le_of_le_one_left (abs_nonneg _) (show _≤(1:ℝ) from ?_)).trans ?_
 · rw [abs_of_pos (by positivity)]; exact inv_le_one_of_one_le₀ (mod_cast Nat.factorial_pos l)
 exact (Z'.le_opNorm (fun i=>x)).trans ((mul_le_mul_of_nonneg_right (he.norm_le _ hl) (Finset.prod_nonneg fun _ _=>norm_nonneg _)).trans_eq (by simp))
end Trace
end YM.QuadraticLocal.Echo
