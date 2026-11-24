import YM.OPE.Compatible.Hatch.Ray
/-! # Cost transport into orthogonal cube. Projection preserves Hardy plateau. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Merchant
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
noncomputable abbrev BudL (k:ℕ)(j:I)(x:Bid.Dir G (A j)):= (fderiv ℝ (jet (q j) (k+1)) x).comp (sailT G (V j))
private lemma image_π {J:Type}[Fintype J] (G:Gauge)(y:Libra.Keys G J)(P:Libra.Keys G J →L[ℝ]ℝ)(v:J × G.ColorIndex→ℝ)(h:∀ i,‖P (PickL G i)‖ ≤ v i): ‖P y‖ ≤ (∑ i,v i)*‖y‖:=by
        nth_rw 1[resident y]; rw[map_sum,Finset.sum_mul]; refine (norm_sum_le ..).trans (sum_le_sum fun i _=>?_); rw[map_smul,norm_smul,mul_comm]; apply mul_le_mul (h i) _ (norm_nonneg _) ((norm_nonneg _).trans (h i)); rw[phone_eq]; exact (PiLp.norm_apply_le ..).trans (norm_le_pi_norm ..)
private lemma image_power {J : Type} [Fintype J] (G : Gauge) (y : Libra.Keys G J)
    (P : Libra.Keys G J →L[ℝ] ℝ) (v : J × G.ColorIndex → ℝ) (u : ℝ)
    (bound : ∀ j, ‖P (PickL G j)‖ ≤ v j * u) : ‖P y‖ ≤ (∑ j, v j) * u * ‖y‖ := by
  simpa only [Finset.sum_mul] using image_π G y P (fun j => v j * u) bound

private lemma bud_read (k : ℕ) (j : I) (x : Bid.Dir G (A j)) (y : Chamber G r) :
    BudL q V k j x y = Budγ q V k j x y := rfl
include h
section
local notation "B!"=> Cpit G A W
set_option maxHeartbeats 200000
lemma PISeen (k:ℕ):∃ t:I→ℝ,RateLE φ Z t 0∧ ∀ᶠ i in φ,∀ x:Bid.Dir G (A i),∀ c:ℝ,0<c→ Roster x ≤ c→∀ y: Chamber G r, ‖BudL q V k i x y‖ ≤ t i*c^k *‖y‖:=by
  let P := ↥(fieldP r) × G.ColorIndex
  choose t v ht hv hC using fun u : P => ζPass U q p h V u.1 u.2 k 0
  refine ⟨fun i => ∑ j, t j i, RateLE.sum (S := univ) U.top.fair (fun j _ => ht j), ?_⟩
  filter_upwards [eventually_all.mpr hC] with i hi x c hc hx y
  apply image_power G y (BudL q V k i x) (fun j => t j i) (c^k)
  intro j
  rw [bud_read]
  exact (hi j x c hc hx).1
lemma VDeep (k:ℕ): ∃ t:I→ℝ,RateLE φ Z t a∧∀ᶠ i in φ,∀ x:Bid.Dir G (A i),∀ c:ℝ,0<c→ Roster x ≤ c→∀ y: Chamber G r, ‖BudL q V k i x y-BudL q V k i ((Cpit G A W i) x) y‖ ≤ t i*c^k *‖y‖:=by
  let P := ↥(fieldP r) × G.ColorIndex
  choose t v ht hv hC using fun u : P => ζPass U q p h V u.1 u.2 k a
  refine ⟨fun i => ∑ j, v j i, RateLE.sum (S := univ) U.top.fair (fun j _ => hv j), ?_⟩
  filter_upwards [eventually_all.mpr hC] with i hi x c hc hx y
  let signal := BudL q V k i x - BudL q V k i ((Cpit G A W i) x)
  apply image_power G y signal (fun j => v j i) (c^k)
  intro j
  simp only [signal, _root_.sub_apply, bud_read]
  exact (hi j x c hc hx).2
end
end Sleeve
end YM.OPE.Merchant
