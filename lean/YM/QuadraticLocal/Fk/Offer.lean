import YM.QuadraticLocal.Earn.Blend
import YM.QuadraticLocal.Fk.Airport
/-!
# Volume-legal for the native Fk interpretation of any participating `Scene`

Sum all exponent-model exposures.Occupant heights on arbitrary policy
 of true tours. Allow per-tested-t coordinate. No real-uniform payload
 or manuscript Primary estimated beyond supplied. The pricing certificate
 is already only at native weighted unit fields (in `w`).

For later iteration don't confuse the cost of the unmasked countable reading
 established here with a bound on its broken mask. Using this receipt before
 period-weighted alias charge still requires taking the exponential costs.
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
variable {V:Type}{G:Gauge} {n c:Side} {k j e d r:ℕ} {a b σ :ℝ}
open Aperture Poetry Echo Work.G05 Toggle Aux Aux.Name Marker Multi
open QuadraticLocal.Sunrise
variable {ι α : Type} [DecidableEq V] {P:Passport n V} {R:Census V}
variable (M:ι→ Row P R G α)
namespace Air
variable (q:ι→ℂ)(w:V→ℕ)(w':V→ℝ)
set_option quotPrecheck false
abbrev united (n:Side)(b:ℝ) := (n.val:ℝ)^4*b
local notation "F"=> Air.united n b
local notation "Q" i:max=> (Poly.toll w' (M i).mode * (M i).height a)
local notation "t_q" x:max => (fun i:ι=> if (M i).center=x then (Poly.toll w' (M i).mode * (M i).height a) else 0)
variable (H: Scene.Armada M w' w a b j k d)(he:0<a)
local notation "x₀"=> (0: Site n)
include H
lemma receipts : SumBudget (fun i:ι=> Poly.toll w' (M i).mode * (M i).height a) (Air.united n b):= by
 let h(i:ι):= Q i; let s x:= t_q x; have hp : ( fun i:ι=> Poly.toll w' (M i).mode * (M i).height a ) = fun i=> ∑ x: Site n, s x i:= by ext1 i; simp only [s,sum_ite_eq]; simp -- orientation
 rw [hp]; refine budget_loosen (budget_over (Finset.univ: Finset (Site n)) s (fun (_:Site n)=>b) (fun i _=> H.suggests i)) ?_; apply Eq.le; unfold united; simp [site_card]
include he
lemma heel (i:ι): (M i).salary ≤ (M i).height a:= by
   unfold Row.height; exact le_mul_of_one_le_right ( M i|>.sound.le) (Real.one_le_exp (mul_nonneg he.le (Nat.cast_nonneg _)))
lemma crew : ∃ p:ℝ, SumBudget (fun i=> (M i).salary) p:= by
 let V' (t:R.Mode):= Poly.toll w' t; letI : Nonempty R.Mode:= ⟨R.quiet⟩; obtain ⟨i,-,hi⟩:= Finset.exists_min_image univ V' univ_nonempty
 let ε:=V' i; have hh:0< ε:= Poly.worth H.positive _; have hp := receipts M w w' H; refine ⟨_, budget_mono (budget_scale (inv_nonneg.mpr hh.le) hp) (fun i=> (M i).sound.le) fun j=> ?_⟩; rw [← div_eq_inv_mul]; apply (le_div_iff₀ hh).mpr; have hJ: ( Q j )=( Poly.toll w' ( M j ).mode * ( M j ).height a ):= rfl; rw [mul_comm]; exact mul_le_mul (hi _ (Finset.mem_univ _)) (Air.heel M w w' H he j) (M j).sound.le (Poly.worth H.positive _).le
variable (hy:∀ i, ‖q i‖ ≤ (M i).salary)
include hy
lemma license : Air.Staff M q w a (j+d+1):= by
 have hv i:= Scene.Armada.degreeR w H.toMinistry (M i) (H.purchases.usable i); obtain ⟨p,hp⟩:= Air.crew M w w' H he
 refine ⟨he,fun i=> H.purchases.usable i |>.2,(fun i=> (hv i).2.2),fun i=> ?_, (budget_mono hp (g:= Air.total M q a) (fun i=>?_) ?_).2.1⟩;
 · unfold Loan.stamp; have hx:= hv i |>.1; have hz:= (hv i).2.1; omega
 · exact mul_nonneg (norm_nonneg _) ( Plateau.paid_nonneg ..)
 intro i; exact (mul_le_mul (hy i) ( H.purchases.spend i) ( Plateau.paid_nonneg ..) ( M i ).sound.le).trans_eq (mul_one _)
-- Helpers: regroup costs in non-η.H.Price weight. microscope. Later Charge total aliases across ANY publication tier. note root cost .inside with volume polynomial by dearth.
end Air
end YM.QuadraticLocal.Earn
