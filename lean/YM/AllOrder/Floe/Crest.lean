import YM.AllOrder.Floe.Acre
import YM.Extra.WILSON_STARTUP.Match
import YM.AllOrder.Iron.Entries
import YM.Extra.ITERATION_NO_LOSS.Inherited
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Floe
open Function Filter Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open AbsoluteSums Org Poll
open Ker Ker.Start Haiku Haiku.Coat Fire PertExtension.Series Radial
open Laplace Laplace.SigmaP Response Ink Ink.Method Ink.Money Laurent Stationary
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open PositionX.Jet Extra.Iteration
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {G: Gauge} {c f n : Side} {k j w N : ℕ} {S:StepData c f}
variable {σ C Z D β Θ:ℝ}
namespace Crest
/-! Choose curvature book through all orders *before* L restriction. Takes peak.T.Purchase implied basis via canon. Keep regulator link unmasked & Symm actions. -/
open WilsonStartup WilsonStartup.Design WilsonStartup.Padded Work Tensor
variable (p:Clip)
abbrev headx (G: Gauge) (r:ℕ) := bulk p • Tensor.coeff (inK G) r 0
def place (G:Gauge)(r i:ℕ):Atom G r:= Design.extractAtom G (Padded.name PlaqAxes i) (if fixed PlaqAxes i then headx p G r else 0)
def allowance (G:Gauge)(r:ℕ)(σ:ℝ):ℝ:= ∑ i:PlaqAxes, (Design.extractAtom G i (headx p G r)).budget σ
lemma grant (G:Gauge)(k:ℕ)(σ:ℝ): Extra.Iteration.Charged (place p G k) σ (allowance p G k σ):= by refine Padded.budget (α:=PlaqAxes) ?_ (fun i=> ?_) le_rfl; intro i; unfold place; split; rfl; rw [Atom.budget,Design.extract_magnitude_zero,zero_mul]; unfold Atom.budget Atom.magnitude; positivity -- split proof sequence ambiguous
lemma moves (G:Gauge)(r:ℕ):Extra.Iteration.SymmetricAtoms (place p G r):= by
 intro i; apply extract_invariant; intros u v; split; simp only [headx, ContinuousMultilinearMap.smul_apply, coeff_adjoint]; simp
local notation "u"=> Atom G
variable (U:Config G n)
lemma read0 (r:ℕ): uncut (place p G r) U=∑ b:WilsonStartup.Cell n, bulk p * Tensor.diagonal (Tensor.coeff (inK G) r 0) (G.curvature (faceValue U b)):= by
 unfold uncut; rw [Fintype.sum_prod_type]; apply Finset.sum_congr rfl; intro t _; apply Padded.totals; intro i; unfold place; split <;> rw [Design.extract_unmasked] <;> simp only [headx,Tensor.diagonal, ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.zero_apply,smul_eq_mul]
abbrev channel (r:ℕ) (v:G.El):ℝ:= Tensor.diagonal (Tensor.coeff (inK G) r 0) (G.curvature v)
lemma channel_conj (r:ℕ)(v w:G.El):channel r (v*w*v⁻¹)=channel r w:= by unfold channel; rw [G.curvature_conjugate]; exact coeff_adjoint ..
lemma channel_neg (r:ℕ)(v:G.El):channel r v⁻¹=channel r v:= by
 unfold channel; rw [G.curvature_inv]; obtain he|ho:= Nat.even_or_odd r; · rw [← neg_one_smul ℝ _, Tensor.homogeneous,he.neg_one_pow,one_smul]
 rw [odd_diagonal _ r ho,odd_diagonal _ r ho]
lemma face_signed (s:Signed)(b:WilsonStartup.Cell n)(r:ℕ):channel r (faceValue (pull s 0 U) b) = channel r (faceValue U (Face.send s 0 b)):= Face.send_price U b s 0 (channel r) (fun _=>channel_neg r _) (fun v w => channel_conj r w v)
lemma read (r:ℕ): Extra.Iteration.action (place p G r) U =∑ b:WilsonStartup.Cell n, bulk p * channel r (faceValue U b) := by
 have he (s:Signed): uncut (place p G r) (pull s 0 U)=∑ b:WilsonStartup.Cell n, bulk p * channel r (faceValue U b):= by
    rw [read0]; change ∑ b: WilsonStartup.Cell n, _ * channel r (faceValue (pull s 0 U) b) = _; simp_rw [face_signed U s _ r]; exact Equiv.sum_comp (Equiv.ofBijective _ ⟨Face.injective_send s (0:Site n), Finite.injective_iff_surjective.mp (Face.injective_send ..)⟩) (fun b:WilsonStartup.Cell n=>bulk p*channel r (faceValue U b))
 unfold Extra.Iteration.action Patch.average; simp_rw [he]; simp
end Crest
end YM.AllOrder.Floe
