import YM.OPE.Compatible.Fiord.Kra
/-! # Cost transport into orthogonal cube. Projection preserves Hardy plateau. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Merchant
set_option maxHeartbeats 200000
open Function Filter MeasureTheory Lattice Laurent Wilson RG Precision Metric Matrix Cascade Finset Tensor
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}
attribute [local instance] Gauge.frobInner
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion Score
open Flock Libra.Shell Next.Foundations Weir Exterior Bloch Next.Free Frequency Streamer Votive Flume Flume.Script Glass Quit.PriceZ Quit Paver
open Drift Char Silt Silt.Float Module Variance StepsL Claw Prom Ibis Merchant.SiteL Flume.Page StepsL Wool
variable {i j d k m r l b:ℕ}{n:Side}
local notation "D!"=> Bid.Dir G n
open Aloof
namespace Sleeve
variable {I:Type}{A:I→ Side}{φ:Filter I}{Z:I→ℝ}{W:I→ℕ}{a c b':ℝ}(U:Scaffold φ Z A W r)
variable (q p: GlyphQ G A)
open Scaffold
variable (h:Shor U q p)(V:(i:I)→Board (A i) (r+1))
-- Application to arbitrary enactments. Costs independent of input size using Roster.G.
open Cinders
variable {D:I→ Type} [∀ i, MeasurableSpace (D i)] {μ:(i:I)→Measure (D i)}[∀ i,IsProbabilityMeasure (μ i)]
open Claw
section
variable (X:(i:I)→D i→ Bid.Dir G (A i))(hX:SkinQ A Z μ φ X)
private lemma Pcomp {E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F](g:F→ℝ)(L:E→L[ℝ] F)(h:Tall g k): Tall (g ∘ L) k:=by
       obtain ⟨P,h⟩:=h.stock; let Q(j:ℕ):= (P j).compContinuousLinearMap (fun _=>L); rw[h,show (∑ j∈range (k+1), Tensor.diagonal (P j)) ∘ L= ∑ j∈range (k+1), Tensor.diagonal (Q j) from funext fun i=>by rw[Function.comp_apply,Finset.sum_apply,Finset.sum_apply];rfl]; exact Tall.sums _ _ (fun i hi=>Tall.loan _ (by have h:=mem_range.mp hi;omega))
private lemma Pshape (k:ℕ):∃ c:ℝ,0≤c∧∀ (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E](f:E→ℝ)(_:Tall f k)(b:ℝ), LimitR b f→∀ x:E, ‖f x‖ ≤ c*b*(1+‖x‖)^k:=by
       let A:=range (k+1); choose! C hC H using fun j (hj:j∈A)=>Tall.notate j k (show j≤k from by have hx:=mem_range.mp hj;omega); refine ⟨∑ i∈A,C i,sum_nonneg hC,fun E _ _ f hv b hh x=>?_⟩
       nth_rw 1[hv.allot]; let v:=1+‖x‖; have ht:1 ≤v:= le_add_of_nonneg_right (norm_nonneg _); let y:=v⁻¹ • x; have hz:v • y=x:=smul_inv_smul₀ (zero_lt_one.trans_le ht).ne' _; have hy:‖y‖≤1:=by unfold y; rw[norm_smul, Real.norm_of_nonneg (by positivity), inv_mul_eq_div,div_le_one (zero_lt_one.trans_le ht)]; exact le_add_of_nonneg_left zero_le_one
       rw[Finset.sum_apply,sum_mul,sum_mul]; refine (norm_sum_le ..).trans (sum_le_sum fun i hi=>?_); change ‖rank f i x‖ ≤ _*v^k; nth_rw 1 [← hz]; rw [Claw.rank, Tensor.homogeneous,norm_smul,norm_pow,Real.norm_of_nonneg (by positivity),mul_comm]; refine mul_le_mul (show ‖rank f i y‖ ≤ _ from H i hi E ℝ _ hv _ hh y hy) (pow_le_pow_right₀ ht (by have h:=mem_range.mp hi;omega)) (pow_nonneg (by positivity) _) (mul_nonneg (hC i hi) ((norm_nonneg (f 0)).trans (hh _ (by simp))))
include hX
variable (ht:Tendsto Z φ atTop)
include ht
lemma dream (hp:Photos φ Z a p)(hf:∀ᶠ i in φ, Tall (p i) k) : Grain μ φ Z (fun i x=> p i (X i x)) a:=by
       obtain ⟨v,hv,hV⟩:= hp.cost; obtain ⟨s,hs,H⟩:= Pshape k; let t(i:I)(x:D i):=1+Roster (X i x); have hg:Grain μ φ Z t 0:= (Grain.const (RateLE.const 1 ht)).add hX.Φ ht; apply Grain.of_le (((Grain.const (μ:=μ) ((RateLE.const s ht).mul hv)).mul (hg.pow ht k)).mint (by simp)); · exact (hX.meat.and hf).mono fun i hi=> (hi.2.neat.continuous.measurable.comp hi.1).aestronglyMeasurable
       filter_upwards [hV,hf] with i he hp; filter_upwards with x; let z:= X i x; let B:= tellerT G (A i); let L:= B.toContinuousLinearMap; let y:= B.symm z; have hh: LimitR (v i) (p i ∘ L):=by intro a ha; refine he _ ?_; change ‖B.symm (B a)‖ ≤1;rw [B.symm_apply_apply]; exact ha
       have hL:= H _ (p i ∘ L) (Pcomp (p i) L hp) (v i) hh y; rw [Function.comp_apply, show L y=z from B.apply_symm_apply z] at hL; exact hL.trans (Real.le_norm_self _)
-- eventual all legs
lemma Flown (f:Forge G A)(hp:Silks φ Z a f)(hf:∀ p:Phase, ∀ᶠ i in φ,Tall (eyeR f p i) (d+p.val)) : Pine μ φ Z (fun i x=>f i (X i x)) a:= fun i=> dream _ X hX ht (hp.marks i) (hf i)
end
end Sleeve
end YM.OPE.Merchant
