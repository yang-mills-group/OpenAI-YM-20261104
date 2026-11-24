import YM.QuadraticLocal.Rebirth.Tag
import YM.QuadraticLocal.Rebirth.Reprints
/-!
# Reitter the entire unmasked connected kernel through a bend of its chart.
 Finite budgets on concerned sources. Cauchy merging (no differentiated volume exchange!).
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Rebirth
open Function Filter Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis Bid Planned.JetPort
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open AbsoluteSums Org Poll
open AllOrder AllOrder.Ker AllOrder.Ker.Start AllOrder.Haiku AllOrder.Haiku.Coat AllOrder.Fire PertExtension.Series Radial
open AllOrder.Laplace AllOrder.Laplace.SigmaP Response AllOrder.Ink AllOrder.Ink.Method AllOrder.Ink.Money Laurent Stationary
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open PositionX.Jet Extra.Iteration AllOrder.Catch AllOrder.Catch.Clock AllOrder.Floe AllOrder.Plateau
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
open QuadraticLocal.Sunrise Marker Earn
variable {ι V α:Type} [DecidableEq V] {R:Census V} {G:Gauge} {n:Side} {P:Passport n V}
open Comparison.RG02 Comparison.RG02.Adjacent
namespace Sleeve
local notation "A"=> (Stationary.Link G n)
variable (X: Row P R G α) (t:α) (w:V→ℕ)
local notation "u★"=> X.lamp.lag
local notation "xρ"=> X.lamp.r
local notation "τ"=> X.lamp.e
variable (M:ι→Row P R G α)
set_option quotPrecheck false
local notation "X'"=> (Stationary.arm G n 1)
local notation "K"=> (Q.Clock.Art.Texture) -- placeholder
variable (Kp:R.Mode)

local notation "V'"=> (fun i:ι=>Sleeve.coin (M i) t Kp)
-- membership must cover all.Label budgets complete.Edge.St.Frame.Consumer.Stock.*
variable (S:Finset ℤ) (hS:∀ i,(M i).lamp.lag∈ S)
variable {a b:ℝ} {u v:ℕ}
variable (Q:Pace.Coin)(h:Q 0=0)(L j:ℕ)
variable [Fintype V]
set_option quotPrecheck false
local notation "PΩ"=> (fun i:ι=>(M i).paint t)
variable (ha: Air.Staff M (fun i:ι=>(M i).paint t) w a u)
local notation "Z"=> (Mutation.stamp M Q h L j)
variable (T:Finset Age)(B:AllOrder.Floe.Layout G)
local notation "k'"=> (Sleeve.coin)
local notation "Y" => Air.craft M (fun i:ι=>(M i).paint t) w B T
abbrev currency (i:ℕ) (y:Stationary.Link G n):ℂ:= ( Air.discharge (Y) i (Stationary.arm G n 1 y)).part Kp
abbrev treasury (k:ℕ)(s:ℤ)(y:Stationary.Link G n):ℂ:=∑' i, if (M i).lamp.lag=s then (V' i) k y else 0
local notation "Φ"=> (currency t w M Kp T B) -- order?
local notation "q"=> ( treasury t M Kp )
include ha
lemma real_income (i:ℕ)(y:Stationary.Link G n): HasSum (fun j:ι=> (V' j) i y) ( currency t w M Kp T B i y ):= (Pi.hasSum.mp (Air.compared M PΩ w ha B T y i)) Kp
include B T
lemma funding (z:ℤ)(x:A)(k:ℕ) : HasSum (fun i:ι=> if (M i).lamp.lag=z then Sleeve.coin ( M i ) t Kp k x else 0) (q k z x):= by
    have hm:=(real_income t w M Kp ha T B k x).summable; apply Summable.hasSum; refine (hm.indicator {i:ι | (M i).lamp.lag=z}).congr ?_; intro i; simp [Set.indicator]
include hS
lemma seams (i:ℕ)(x:A) : Sleeve.currency t w M Kp T B i x= ∑ k∈S, treasury t M Kp i k x:= by
    let f(j:ℤ) w:= if ( M w ).lamp.lag=j then Sleeve.coin (M w) t Kp i x else 0; have hs: HasSum (fun i=>∑ j∈S,f j i) (∑ j∈S,q i j x):= by apply hasSum_sum; intro j _; exact funding t w M Kp ha T B j x i; -- signature uses `hasSum_sum`?
    apply (real_income t w M Kp ha T B i x).unique (hs.congr_fun _) ; intro i'; change _ = ∑ j∈S,f j i'; unfold f; simp [hS]
omit hS
lemma stretches (a':ℝ)(h0:a'≠0)(s:ℤ)(x:A)(k:ℕ): a'^k • (Sleeve.treasury t M Kp k s (a'⁻¹ • x))= a'^s • Sleeve.treasury t M Kp k s x:= by
    let h₀:=(funding t w M Kp ha T B s x k).const_smul (a'^s); apply ((funding t w M Kp ha T B s (a'⁻¹ • x) k).const_smul (a'^k)).unique; apply h₀.congr_fun; intro i
    split; next hi=> rw [heat _ _ _ a' h0, hi]
    next=> rw [smul_zero,smul_zero]
end Sleeve
end YM.QuadraticLocal.Rebirth
