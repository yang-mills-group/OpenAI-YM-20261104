import YM.QuadraticLocal.Rebirth.Vacuum
import YM.AllOrder.Ink.Drill
import YM.Comparison.RG02.Adjacent.Equivalent
/-!
## Born (vacuum action and calibration)

Keep complete kinetic directions. The projection is pre-calibration (to the
 actual local Fk step via its own orientation data), then these receipts show
 it's the new packet portfolio at the same predicted units. **No** estimates
 deducted from the calibration; don't claim Caliber predicts exactly numerically.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Faith
open Function Filter Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open AbsoluteSums Org Poll Extra.Iteration
open AllOrder AllOrder.Ker AllOrder.Ker.Start AllOrder.Haiku AllOrder.Haiku.Coat AllOrder.Fire PertExtension.Series Radial
open AllOrder.Laplace AllOrder.Laplace.SigmaP Response AllOrder.Ink AllOrder.Ink.Method AllOrder.Ink.Money Laurent Stationary
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open PositionX.Jet AllOrder.Floe AllOrder.Floe.Pace
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {G: Gauge}{n : Side}
open Comparison.RG02 Comparison.RG02.Adjacent
open QuadraticLocal.Rebirth
open QuadraticLocal.Rebirth
open Comparison.RG02 Comparison.RG02.Adjacent
open Valence AllOrder.Ink.Pointwise
namespace Spirit
variable {G: Gauge}{n : Side}
variable (Q:Pace.Coin)(h:Q 0=0)(L:ℕ)(R:PathData G)(p:Clip)
local notation "Φ"=> (Stationary.Link G n)
local notation "K₀"=> (caliber Q h)
set_option quotPrecheck false
local notation "η"=> ((caliber Q h).direct L)
local notation "Δ"=> ((caliber Q h).back L)
variable (V: Floe.Layout G) (S:Finset Age)
local notation "A"=> (grouping Q V S p R)
local notation "B"=> (grouping 0 V S p R)
variable {a C D:ℝ} (hG:G.Simple)(hS:Legal S V)(hR:R.Bounds p a C D)
local notation "F"=> (suction (n:=n) (B))
local notation "F'"=> (suction (n:=n) (A))
local notation "cost"=> Spirit.Compatible
-- allow more presentations for Body Consumer.Engine.Legacy Era.B.Work.Shape.Sensor flags; Charge referenced for all positivity.H_Reader
lemma level_jet {X:Type} [NormedAddCommGroup X][NormedSpace ℝ X][FiniteDimensional ℝ X]{f:X→ℝ} {k:ℕ} (h:Rank X k f)(L:ℝ→L[ℝ]ℂ): Level k (L ∘ f) := by -- need X etc
    let F'':=iteratedFDeriv ℝ k f 0; have hf:ContDiff ℝ ω f:= h.read.smooth; have hu : (L∘ f)=fun i=>∑ v∈range (k+1),Assembly.jet (L ∘ f) v i:= by
       funext x; rw [Function.comp_apply,full_span x h,map_sum]; exact Finset.sum_congr rfl (fun i _=> Assembly.jet_apply_left L f i (hf.contDiffAt.of_le le_top) _)
    have he:ContDiff ℝ ω (L∘f):= L.contDiff.comp hf; exact hu ▸ (by apply Level.total; intro i hi; exact ((Adjacent.levelJet he.contDiffAt i).promote (by have ht:=mem_range_succ_iff.mp hi; omega))) -- might rewrite on L∘ f on RHS changes edges

include hG hS hR
lemma charges (k:ℕ): Valence.Level (k+2) (suction (grouping Q V S p R) k (n:=n)) := by
    apply ((level_jet (Pace.glories Q V S p R hR hS hG|>.rank k le_rfl n) (-Complex.ofRealCLM)).promote (?_: ((k+2:ℕ):ℤ) ≤ _)); omega -- sign defeq
local notation "β"=> (caliber Q h).back L -- quotPrecheck false
-- Solve inverse for actual tooths. Input R from lower itinerary.Reg.Body.Health Controller.
variable {k:ℕ} (he:k≤L)
include he
lemma returned : Adjacent.born (suction (grouping Q V S p R) (n:=n)) ((caliber Q h).back L) 0 L k= suction (grouping 0 V S p R) k (n:=n) := by
 have hu : Charge L (fun k:ℕ=> (k:ℤ)+2) ((F)):= fun i _=> charges (n:=n) 0 R p V S hG hS hR i; let H:= ( Adjacent.born (suction (grouping 0 V S p R) (n:=n)) (η) 0 L ); have hh:= auth Q h L R p V S
 have he' := Adjacent.reverse 0 L hu ( K₀|>.forward_back L ) k he;
 rw [← he']; funext x; unfold Adjacent.born; -- inner born also unfolded. restructure
 apply (congr_fun (g:=Comparison.RG02.Moving.Path.motion _) (congr_arg Comparison.RG02.Moving.Path.motion _) _); funext t; unfold ages Adjacent.cover; exact congr_arg ( _ * · ) ( sum_congr rfl (fun i hi=> congr_arg (fun f:Φ→ℂ=> _ * f (((Δ).rating t)⁻¹ • x)) ( show Spirit.suction (grouping Q V S p R) i= H i from ( (Spirit.evolves hh (mem_range_succ_iff.mp hi))).symm ) ) ) -- not η syntax
end Spirit
end YM.QuadraticLocal.Faith
