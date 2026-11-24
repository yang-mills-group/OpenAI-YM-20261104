import YM.OPE.Compatible.Song.Heed
/-!
# Froben budget. Projection on first terms.Low layer
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Merchant
open Function Filter MeasureTheory Lattice Laurent Wilson RG Precision Metric Matrix Cascade Finset Tensor
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}
attribute [local instance] Gauge.frobInner
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion Score
open Flock Libra.Shell Next.Foundations Weir Exterior Bloch Next.Free Frequency Streamer Votive Flume Flume.Script Glass Quit.PriceZ Quit Paver
open Drift Char Silt Silt.Float Module Variance StepsL Claw Prom Ibis Merchant.SiteL
variable {i j d k m r l b:ℕ}{n:Side}
variable {I:Type} {B:I→ Finset (Edge Cover)}{N:I→ Side}{φ:Filter I}{Z:I→ℝ}
section
open OrientX
variable {D:I→Type}[∀ i,Fintype (D i)]{F:Type}[Fintype F]
local notation "F!"=> Keys G F
variable (Y:(i:I)→ Keys G F →L[ℝ] Keys G (D i))(K:(i:I)→Keys G (D i)→ₗ[ℝ] Dual' (Keys G (D i))) (T:I→Law (Keys G F))
-- avoid defer.O. hp explicit presence
lemma Marks (k:ℕ)(u:(i:I)→Keys G (D i)→ℝ)(ht:Tendsto Z φ atTop)(h:∃ c:ℝ,0 < c ∧∀ᶠ i in φ,∀ x, c*‖x‖^2≤ (T i).P x x)(hp:Bills φ Z (fun i x=> mate (Y i) (K i) (T i) x))(hY:∀ i x,‖Y i x‖ ≤ ‖x‖)(hu:Bills φ Z u)(hx:∀ᶠ i in φ,Tall (u i) d): Bills φ Z (fun i=>OrientX.νrt (K i) (Y i) (T i) (u i) k):=by
       obtain ⟨c,hc,H⟩:= h; obtain ⟨b,hb,V⟩:=hp; obtain ⟨f,hf,hK⟩:= blissP u ht (Breeze ht hu hx (k+1)) (hx.mono fun i hi=>hi.neat.contDiffAt); let U(i):=1+‖b i‖; have hU(i):1≤ U i:= le_add_of_nonneg_right (norm_nonneg _); let a(i):= (((k+1:ℕ):ℝ)*(U i^(k+1)*f i))/c
       refine ⟨a,?_ ,?_⟩; · unfold a; simp_rw [div_eq_mul_inv]; exact (((RateLE.const ((k+1:ℕ):ℝ) ht).mul ((((RateLE.const (1:ℝ) ht).add hb.norm ht).pow _ ht).mul hf)).mul (RateLE.const _ ht)).mono (by norm_num)
       filter_upwards [V,hK,H] with i hv hh hx; exact OrientX.boundω (K i) (Y i) (T i) hh ((norm_nonneg _).trans (hh 0 (fun _=>by simp))) (hU i) (fun x hz=> (hv x hz).trans ((Real.le_norm_self _).trans (le_add_of_nonneg_left zero_le_one))) (fun x h=> (hY _ _).trans (h.trans (hU i))) hc hx
end
end YM.OPE.Merchant
