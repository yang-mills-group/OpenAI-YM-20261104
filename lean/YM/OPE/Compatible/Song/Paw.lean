import YM.OPE.Compatible.Song.Foliage
import YM.OPE.Compatible.Parch.Mirror
/-!
# Native Taylor incomes; through cubic derivatives. Use frozen V only.
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
variable {I W:Type} {B:I→ Finset (Edge Cover)}{N:I→ Side}{φ:Filter I}{Z:I→ℝ}
section
variable {D:I→Type}[∀ i,Fintype (D i)]
open LinearMap
private lemma fuel (z:(i:I)→Keys G (D i)→ℝ)(g:(i:I)→Keys G (D i))(hx:RateLE φ Z (fun i=> ‖g i‖) 0)(hT:Tendsto Z φ atTop)(k:ℕ)(hp:Bills φ Z (fun i=>jet (z i) k))
         (hv:∀ᶠ i in φ,ContDiffAt ℝ ω (z i) 0): Bills φ Z (fun i=> bat (g i) (jet (z i) k)):=by
        cases k with
        | zero=> apply Bills.merge (Bills.zeroB hT); filter_upwards with i; funext v; unfold bat; rw[show jet (z i) 0=fun _=>z i 0 from funext fun j=> jet_zero .., fderiv_const_apply];rfl
        | succ k=>
          obtain ⟨c,hc,H⟩:=blissP z hT hp hv; let X(i):=Tensor.coeff (z i) (k+1) 0; refine ⟨fun i=> ((k:ℝ)+1)*c i*‖g i‖,(((RateLE.const ((k:ℝ)+1) hT).mul hc).mul hx).mono (by norm_num),?_⟩; filter_upwards [H,hv] with i hi hj x hx; unfold bat; change ‖fderiv ℝ (Tensor.diagonal (X i)) _ _‖≤ _; rw[differential_diagonal _ (coeff_symm (hj.of_le le_top)), ← Nat.cast_smul_eq_nsmul ℝ,norm_smul,Nat.cast_add_one,Real.norm_of_nonneg (by positivity)]; rw[ mul_assoc]; refine mul_le_mul_of_nonneg_left (((X i).le_opNorm (Fin.cons (g i) (fun _=>x))).trans ?_) (by positivity)
          simp only[Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ,prod_const,card_univ,Fintype.card_fin]; exact mul_le_mul (Dollar ((norm_nonneg _).trans (hi 0 (fun _=>by simp))) hi) (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hx)) (mul_nonneg (norm_nonneg _) (by positivity)) ((norm_nonneg (X i)).trans (Dollar ((norm_nonneg _).trans (hi 0 (fun _=>by simp))) hi))
end
-- ρ cost any salary. 
lemma Phil (Q:GlyphQ G N) (x:(i:I)→Bid.Dir G (N i))(hv:∀ᶠ i in φ, ContDiffAt ℝ ω (Q i) 0)(hz:RateLE φ Z (fun i=> ‖x i‖) 0)(ht:Tendsto Z φ atTop)
     (h0:Filμ B φ Z (fun i=>jet (Q i) k) k) : Filμ B φ Z (fun i=>bat (x i) (jet (Q i) k)) k:=by
       refine ⟨(h0.here.and hv).mono (fun i hi=>?_ ),hv.mono (fun i hi=>?_ ), fuel Q x hz ht k h0.loud hv⟩; swap
       · cases k with
         | zero=> rw[show jet (Q i) 0=fun _=>Q i 0 from funext fun j=>jet_zero ..,show bat (x i) _=(0:Bid.Dir G (N i)→ℝ) from funext fun j=>by unfold bat; rw [fderiv_const_apply];rfl]; exact Tall.bread0
         | succ k=> let z:= Tensor.coeff (bat (x i) (Q i)) k 0; change Tall _ (k+1); rw [show bat (x i) (jet (Q i) (k+1))= jet (bat (x i) (Q i)) k from funext fun j=>vast (Q i) k hi _ _]; exact Tall.loan z (Nat.le_succ _)
       let M:=BlurD G (B i) (N i); refine ⟨fun y z hz=>?_⟩; let f:=jet (Q i) k; let a:=x i; have hf:Differentiable ℝ f:= (Tall.loan (Tensor.coeff (Q i) k 0) le_rfl).neat.differentiable (by simp); have he:(fun t:ℝ=> f (y+t • a))=(fun t:ℝ=> f (z+t • a)):=funext fun t=> hi.1.jury _ _ (by rw [map_add,map_add,hz]); unfold bat; let A(y):HasDerivAt (fun t:ℝ=>f (y+t•a)) (fderiv ℝ f y a) 0:=(by simpa only[zero_smul,add_zero] using! (HasFDerivAt.comp_hasDerivAt (f:=fun t:ℝ=>y+t • a) 0 (hf _).hasFDerivAt ((YM.Stationary.ray_id a).const_add y))); exact (A y).unique (he.symm ▸ A z)
end YM.OPE.Merchant
