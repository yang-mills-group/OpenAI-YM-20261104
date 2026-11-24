import YM.FVA2.Lambda.Neuron
/-!
# ∫ p Z(p)^m ∏ components. radial recurrence independent of positivity of perturbative target words. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Lambda.Gaussian
open Function Filter Set Finset MeasureTheory Real Metric Lattice
open MS MS.Plane MS.Momentum MS.Arts MS.Koszul MS.Landau MS.Landau.Detect
open MS.Wind MS.Wind.Modeled MS.Heat MS.Heat.Signal MS.High MS.Tone MS.Tone.Frame MS.Color MS.Native
open MS.Book MS.Book.Convolve MS.Dock MS.Emit MS.Pearl
open MS.City MS.Plane.Flux
open Area Shells Pages
open Lathe (γ)
open Complex (I)
open scoped Topology ContDiff BigOperators Classical InnerProductSpace ENNReal NNReal
variable {G:Gauge}{a:ℝ}
local notation "Z"=> Momentum.sq (A:=Axis)
variable (ha:0≤a)(α:Axis→ℕ)(i:Axis)(n:ℕ)
def S (α:Axis→ℕ):ℝ:= ∑ i,(α i:ℝ)
lemma wings : S (shift α i)= S α+2:= by
    unfold Gaussian.S; have he(k:Axis): (Gaussian.shift α i k:ℝ)= ↑(α k)+( if k=i then 2 else 0):= by unfold shift; split <;> simp [*]
    simp_rw [ he, Finset.sum_add_distrib ]; simp
abbrev b₀ :ℝ:= ( (2*π)^4 )⁻¹ * π^2
abbrev norm_a (a:ℝ):ℝ:= capμ*(π/(1+a))^2
lemma b0 : b₀=(16*π^2)⁻¹:= by unfold b₀; field_simp; ring
lemma Szero : S (fun _=>0)=0:= by unfold S; simp
lemma γ_norm (q:QP): ar (fun _=>0) q=1:= by unfold ar; simp
include ha
lemma basis₀ : tide (fun _=>0) a 0= ( b₀ / (1+a)^2 ):= by simp_rw [base0,pin₀]; simp only [ Finset.prod_const, Finset.card_univ, Axis, Fintype.card_fin ]; rw [show (Real.sqrt (π/(1+a)))^4=(( Real.sqrt (π/(1+a)))^2 )^2 from ( by ring ), Real.sq_sqrt (by positivity) ]; unfold b₀ capμ; field_simp
lemma tideV : tide (shift α i) a 0 = ( ( α i+1:ℕ ):ℝ ) / (2*(1+a)) * tide α a 0:= by
    rw [ base0,base0 ]; have he(k:Axis): pin a ( shift α i k )= if k=i then pin a (α k)*(( (α i+1:ℕ):ℝ )/(2*(1+a))) else pin a (α k):= by unfold shift; split <;> next h=> first| rfl| (subst k; rw [nextPin ha,mul_comm])
    simp_rw [ he,slotR (fun k:Axis=>pin a (α k)) _ _ ]; ring
lemma gram : Integrable ( rock α a n ) μq:= by
    induction n generalizing α with | zero=> exact rustic0 ha α| succ n ih=> rw [ funext (fun q=> horizon n q α a) ]; exact integrable_finsetSum _ (fun i _=> ih _)
lemma matrix : tide α a (n+1)= ∑ i,tide (shift α i) a n:= by
    unfold tide; simp_rw [ horizon n ]; exact integral_finsetSum _ (fun i _ => gram ha _ n )
lemma jump : tide α a (n+1)= ( 4+S α+2*(n:ℝ) )/(2*(1+a))*tide α a n:= by
    induction n generalizing α with
    | zero=> rw [matrix ha]; simp_rw [tideV ha]; push_cast; rw [← Finset.sum_mul, ← Finset.sum_div, Finset.sum_add_distrib]; simp only [Finset.sum_const,Finset.card_univ,Axis, Fintype.card_fin]; change (S α+ (4:ℕ) • (1:ℝ))/_ * _=_; ring
    | succ n ih => conv_lhs=> rw [matrix ha α (n+1)]
                   simp_rw [ ih (shift α _), wings ]; rw [← Finset.mul_sum, ← matrix ha]; push_cast; ring
end YM.FVA2.Lambda.Gaussian
