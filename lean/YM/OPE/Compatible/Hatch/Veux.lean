import YM.OPE.Compatible.Hatch.Song
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
variable (L:I→ Law (Chamber G r))
open Merchant.SiteL
section
private lemma bet {E J:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E][NormedAddCommGroup J][NormedSpace ℝ J][FiniteDimensional ℝ J](V:J→L[ℝ] E)(H:E→ₗ[ℝ] Dual' E)(L:Law J)(x:E)(t c:ℝ)(ht:0<t)(he:∀ y:J,t*‖y‖^2 ≤L.P y y)(h:∀ y, H x (V y)≤ c*‖y‖): ‖pour V H L x‖ ≤ max c 0/t:=by
       let z:=pour V H L x; by_cases hs:z=0; · change ‖z‖≤_; rw[hs,norm_zero]; positivity
       specialize h z; rw[loan _ _ L x z] at h; let B:= max c 0; have hk : t*‖z‖^2 ≤ B*‖z‖ := (he z).trans (h.trans (mul_le_mul_of_nonneg_right (le_max_left ..) (norm_nonneg _))); have hp : t*‖z‖ ≤ B:= le_of_mul_le_mul_right (show t*‖z‖*‖z‖ ≤ B*‖z‖ from by nlinarith only[hk]) (norm_pos_iff.mpr hs); change ‖z‖ ≤B/t; rw [le_div_iff₀ ht]; exact (mul_comm ..).trans_le hp
include h
variable (hc:∀ i,SiteL (sailT G (V i)) (chrom (q i)) (L i))
lemma splayU (i:I)(x:Bid.Dir G (A i))(y: Chamber G r): chrom (q i) (sailT G (V i) y) x= BudL q V 1 i x y:=by
        have hv:=h.smooth_f i; let z:=sailT G (V i) y; let K:= q i; symm; change fderiv ℝ (jet K 2) x z= _; rw [Merchant.podium]; change fderiv ℝ (Tensor.diagonal (Tensor.coeff (q i) 2 0)) x z= _; rw[differential_diagonal _ (coeff_symm (hv.of_le le_top)), Tensor.coeff]; simp only[ContinuousMultilinearMap.curryLeft_apply,_root_.smul_apply]; rw[show Fin.cons z (fun _:Fin 1=>x)=![z,x] from funext fun i=>by fin_cases i <;> rfl,← Nat.cast_smul_eq_nsmul ℝ,smul_smul]; norm_num [Nat.factorial];ring -- `Merchant.podium` inspect
include hc
variable {δ:ℝ} (hv:0<δ)(hL:∀ i x,δ*‖x‖^2 ≤ (L i).P x x)
include hv hL
lemma pour_pay :∃ t:I→ℝ, RateLE φ Z t 0∧∀ᶠ i in φ,∀ (x:Bid.Dir G (A i)) (b:ℝ),0<b→ Roster x ≤ b→ ‖pour (sailT G (V i)) (chrom (q i)) (L i) x‖ ≤ t i*b:=by
        obtain ⟨M,hM,H⟩:=PISeen U q p h V 1; let f(i):= ‖M i‖*δ⁻¹; refine ⟨f,(hM.norm.mul (RateLE.const _ U.top.fair)).mono (by simp),?_⟩; filter_upwards [H] with i hi x b hb hX; let R:= sailT G (V i); let K:= chrom (q i); let c:= ‖M i‖*b; apply le_trans (bet R K (L i) x δ c hv (hL i) (fun y=>?_)); swap
        · rw[(hc i).hike x (R y)]; refine (Real.le_norm_self _).trans (?_ : ‖K (R y) x‖ ≤ _); unfold K R; rw [splayU U q p h V]; exact (hi x b hb hX y).trans (mul_le_mul_of_nonneg_right ((by rw[pow_one]: M i*b^1=M i*b).trans_le (mul_le_mul_of_nonneg_right (Real.le_norm_self _) hb.le)) (norm_nonneg _))
        rw [max_eq_left (show 0≤c by unfold c;positivity)]; unfold c f; exact le_of_eq (by ring)
lemma pour_drop :∃ v:I→ℝ,RateLE φ Z v a∧∀ᶠ i in φ,∀ (x:Bid.Dir G (A i)) (b:ℝ),0<b→ Roster x ≤ b→ let F:=pour (sailT G (V i)) (chrom (q i)) (L i); ‖F x - F (Cpit G A W i x)‖ ≤ v i*b:=by
        obtain ⟨M,hM,H⟩:=VDeep (a:=a) U q p h V 1; let f(i):= ‖M i‖*δ⁻¹; refine ⟨f,(hM.norm.mul (RateLE.const _ U.top.fair)).mono (by simp),?_⟩; filter_upwards[H] with i hi x b hb hX; let X:=Cpit G A W i x; let R:=sailT G (V i); let K:=chrom (q i); let c:=‖M i‖*b; intro F; rw[← map_sub]; apply le_trans (bet R K (L i) (x-X) δ c hv (hL i) (fun y=>?_)); swap
        · rw[(hc i).hike (x-X) (R y),map_sub]; refine (Real.le_norm_self _).trans (?_ : ‖K (R y) x-K (R y) X‖ ≤ _); unfold K R X; rw [splayU U q p h V,splayU U q p h V]; exact (hi x b hb hX y).trans (mul_le_mul_of_nonneg_right ((by rw[pow_one]: M i*b^1=M i*b).trans_le (mul_le_mul_of_nonneg_right (Real.le_norm_self _) hb.le)) (norm_nonneg _))
        rw[max_eq_left (by unfold c;positivity: 0 ≤ c)]; unfold c f; exact le_of_eq (by ring)
end
end Sleeve
end YM.OPE.Merchant
