import YM.QuadraticLocal.Echo.Edge
/-!
 # Rendering on AUX Lie blocks receipts.Every era.

 Select ANY subset of answer photons with full marks and authorized predicates, leave omitted
 at marker tails. Comparison *on the chart* also needs Fk vs cover proofs. We estimate Taylor jets
 of chosen Roll full path atom, not just curvature abelian corners. No Loom pushing here; scaling at
 `b=gStep true`. At the intellectual layer valuation bounds for production vs real selected
 Debts. Holds before choosing real mask.Support costs and aligns not AuroraΦ.H τ.Scope.Shorts.
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
variable (q:V)(W:V→Site n)(X: Roll G V)(h:X.Faith (univ:Finset V) q k σ A)(x:Apex n G)
local notation "ζ"=> X.Ty
local notation "F"=> X.leg
local notation "E"=> Apex n G
local notation "Λ"=> Kinetic.Port.exteriorL G n
variable (hp:PaintSupply G i Z)(b:ℝ)(hb:0 < b)(hx:0<σ)
variable (he:e≤j)
local notation "Ω"=> Spot.label q W X
-- scope bounds
variable (hi:j-e+k ≤ i)
local notation "D" i=> branch G Z σ _ i -- fill
include h hp hi hx hb
def tilt (d:ℕ)(p:X.Ty):= Spot.label q W X e d (bend b x) p
local notation "χ" z:max => ‖((b⁻¹:ℝ) • z)‖
local notation "G₀"=> tilt q W X b x -- argument order. d
lemma lumen (d:ℕ)(hd:d≤j)(p:X.Ty): |Spot.label q W X e d (bend b x) p| ≤ ((X).leg p).money σ * (∑ v∈ Finset.range (k+1), Trace.branch G Z σ i v) * (1+χ x) ^ i:= by
 have hs := h.pinned p; have he':(X.leg p).r ≤ k:= le_trans (Nat.le_add_right ..) hs.tall; let L:= X.leg p; let a':=d-e+L.r; let K':= (∑ v∈ Finset.range (k+1), Trace.branch G Z σ i v); have hK i':0≤ branch G Z σ i i':=by unfold branch; have h:=Uniform.pathPrice_pos hp (mul_pos two_pos hx); positivity
 have hK':0≤K':=Finset.sum_nonneg fun t _=>hK t; have ha:= L.fee_nn σ
 have h:a'≤ i:=by unfold a' L; omega
 let P(x:E):= x; unfold Spot.label; split
 next h'=> rw [flights q W, bend, ContinuousLinearEquiv.apply_symm_apply]; refine (snips q W L _ hx hp _ h).trans ?_; apply mul_le_mul _ _ (by positivity) (mul_nonneg ha hK');
           · exact mul_le_mul_of_nonneg_left (Finset.single_le_sum (fun i _=> hK i) (Finset.mem_range.mpr (show L.r<k+1 from Nat.lt_succ_of_le he'))) ha
           exact (pow_le_pow_left₀ (norm_nonneg _) (b:=1+χ x) (le_add_of_nonneg_left zero_le_one) _).trans (pow_le_pow_right₀ (le_add_of_nonneg_right (norm_nonneg _)) h)
 next h'=> rw [abs_zero]; exact mul_nonneg (mul_nonneg ha hK') (by positivity)
-- Keep terms only when support matches.Loc, this is not an API for arbitrary Mark polynomial on tiny tuples (still attach)
def castable (j e:ℕ)(b:ℝ)(i:X.Ty)(x:Apex n G) := if Spot.Entails (X.leg i) q W then palette q W (X.leg i) b j e x else 0
local notation "J"=> castable q W X
include he
lemma sum_turn : ∀ i:X.Ty, castable q W X j e b i x = ∑ d∈Finset.range (j+1), b^d*Spot.label q W X e d (bend b x) i:= by
 intro u; unfold castable; split; next ht=> rw [← sail q W _ _ _ hb he]; apply Finset.sum_congr rfl; intro d _; simp only [Spot.label,ht,true_and]
 next h=> simp only [Spot.label,h,false_and,ite_false,mul_zero,sum_const_zero]
lemma cali (d:ℕ)(hd:d≤j): Summable (fun p=> b^d*Spot.label q W X e d (bend b x) p):= by
 let K':= (∑ v∈ Finset.range (k+1), Trace.branch G Z σ i v); apply Summable.mul_left (b^d); refine Summable.of_norm_bounded ((h.price.2.1.mul_right K').mul_right ((1+χ x)^i)) ?_ -- signature
 exact fun p=> lumen q W X h x hp b hb hx hi d hd p
-- assemble ℓ register
lemma telescopeE : ∑ d∈ Finset.range (j+1), b^d * ∑ a:Site n, ∑' i,Lantern.gleam (X.leg i) a (Bunch.mapC W) e d (bend b x) = ∑' i,castable q W X j e b i x:= by
 simp_rw [Spot.anthem q W X h, ← tsum_mul_left]; refine (Summable.tsum_finsetSum (fun i hi'=> cali q W X h x hp b hb hx he hi i (Nat.le_of_lt_succ (mem_range.mp hi')))).symm.trans ?_
 · apply tsum_congr; intro i; exact (sum_turn q W X h x hp b hb hx he hi i).symm
end Trace
end YM.QuadraticLocal.Echo
