import YM.QuadraticLocal.Fk.Broadcast
import YM.QuadraticLocal.Fk.WickLimit
/-!
# Analytic certificate of full fields for unmasked analytic packets

Power coupling factors BEFORE evaluating masks in the local
comparison. This ensures the chosen native Mark prescription is
not forgetting any physical factors of g. Use also on successor syntactic
model along all Fk paths for reparameterization of power grade. This
receipt in power-scaled coordinates requires an explicit phase effort
`Row.loan.toll` tied to the current μ-dimension.Owner.Step.Card.Data`. No
 discontinuous mask terms in the analytic prescription; the REAL call
compared using support estimates on all these *actual* U.Support choices.
 Doesn't assume predicted norms once dropping gauge predicate aliases.
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
variable (q:ι→ℂ)(w:V→ℕ)(U:Staff M q w a k)
variable (L:Layout G)(T:Finset Age)
set_option quotPrecheck false
open Comparison.RG02 Comparison.RG02.Bulk
local notation "Yₐ"=> Launch.index R w
local notation "Ptv" i:max=> ScatterR.actor M i
local notation "R₀"=> Air.craft M q w L T
local notation "μ" t:max=> (fun i:ι=> (ScatterR.actor M i).val=Subtype.val t)
variable (y:Multi.Hot R)
variable {c' : Side} {S:StepData c' n} {B₀:Clip} {D':PathData G}{O:ChartRatio G}
variable (K:Comparison.RG02.Bulk.Kernel S B₀ D' O)(X:Forest S.ratio)(t:S.Choices)(x:Exterior.fieldDir G c' 1)
local notation "W" i:max=> ScatterR.colors M i L T R (ScatterR.actor M) q w
local notation "Φ" p:max => Bulk.Fk K X t p x r
open Comparison.RG02 Order
variable [Fintype V]
include U
lemma stability : Tendsto (fun i:Finset ι=> (Φ (W i))) atTop (𝓝 (Φ (R₀))):= WickLimit.survey _ B₀ D' O K X (fun i:Finset ι=> W i) R₀ t x (fun _=>rfl) (fun _=>rfl) (fun y j x=>Air.convergence M q w U L T y X j x) -- parameter order
lemma panorama (j:ℕ): Tendsto (fun i:Finset ι=> Order.observe R r (Order.logMarked ( Bulk.Fk K X t (ScatterR.colors M i L T R (ScatterR.actor M) q w) x r)) j) atTop (𝓝 (Order.observe R r (Order.logMarked ( Bulk.Fk K X t ( R₀ ) x r)) j)) := ((Order.observeL (R:=R) (r:=r) j).continuous_of_finiteDimensional.tendsto _).comp ((WickLimit.always_marked.tendsto _).comp ( stability M q w U L T K X t x))
-- rank quantities for unmasked values. Need REAL α branch `g` not analytic extension if negative.L.Gauge Cur.Frame.S.Step.Wear.
variable (u:ℝ)(hu:u ≠ 0)(A:Config G n)
-- lit. `p.Phase. Persona q` possibly not Row.paint; record then specialize later when transmitting analytic extension

def grainR (i:ι)(g:ℝ)(A:Config G n) := q i*Complex.ofReal ((M i).grain g A)
include hu
lemma fresh (i:ι): Air.grainR M q i u A= (u^( R₀|>.power ( ScatterR.actor M i)))⁻¹ • ( ScatterR.familyAt M q i u A):= by
 let P:= M i; let t:ℕ:= ( R₀ ).power ( ScatterR.actor M i ); rw [show (R₀).power ( ScatterR.actor M i)= (M i).lamp.power from congr_arg (·+1) (U.written i|>.symm)]; unfold grainR Row.grain; rw [← Loan.emission (M i|>.lamp) (M i|>.atom) (M i|>.center) u hu A]; unfold ScatterR.familyAt; rw [Complex.real_smul]; push_cast; ring
-- owner.`character before Share.Parts.Scope`. Summable by querying each Mode.Λ_H.
open Multi
local notation "B" i:max=> (u ^((R₀).power i))⁻¹
local notation "P₁"=> ( Air.grainR M q )
local notation "Θ"=> (Comparison.RG02.Integral.markedLog u A (Air.craft M q w L T))
local notation "X₀" i:max=> Poly.send (M i).mode (Air.grainR M q i u A)
lemma liftPassport : HasSum (fun i:ι=> Poly.send (M i).mode (Air.grainR M q i u A)) (Comparison.RG02.Integral.markedLog u A (Air.craft M q w L T)):= by
 apply Pi.hasSum.mpr; intro i -- α beta swap?
 change HasSum (fun j=> (Poly.send (M j).mode _).part i) ((Θ).part i)
 by_cases h:i=R.quiet;
 · subst i; unfold Comparison.RG02.Integral.markedLog; rw [part_lit_quiet]; exact hasSum_zero.congr_fun (fun j=> part_quiet_hot (ScatterR.actor M j) _)
 let v : Multi.Hot R:= ⟨i,(Comparison.RG02.Cumulants.hot_iff_ne i).2 h⟩; let f j:= @ite ℂ ((μ v) j) (Classical.propDecidable _) (ScatterR.familyAt M q j u A) 0; have hf:(Θ).part i = ( B v ) • (∑' j,f j):= part_lit _ v;
 rw [hf]; have h1: Summable f:= Air.usable_all M q w U A u (μ v); apply (h1.hasSum.const_smul (B v)).congr_fun; intro j; unfold f; split; next he=> rw [Poly.part_send, if_pos (show i=(M j).mode from he.symm), fresh M q w U L T u hu A j, show ScatterR.actor M j = v from Subtype.ext he]
 next he=> rw [Poly.part_send,if_neg (fun h : i=(M j).mode=> he h.symm),smul_zero]
-- no Fintype? hasSum etc. wire polynomial parts coupling expansion published.Me.Frame.Axis.Visibility.Fit.Env. receipt in unmasked log. Row.Mark grief
end Air
end YM.QuadraticLocal.Earn
