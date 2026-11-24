import YM.OPE.Compatible.Parch.Quit
import YM.OPE.Compatible.Grid.Lucre
/-!
# Material curvature earnings. Δν analytic direction
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Merchant
open Function Filter MeasureTheory Lattice Laurent Wilson RG Precision Metric Matrix Cascade Finset
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}
attribute [local instance] Gauge.frobInner
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion Score
open Flock Libra.Shell Next.Foundations Weir Exterior Bloch Next.Free Frequency Streamer Votive Flume Flume.Script Glass Quit.PriceZ Quit Paver
open Drift Char Silt Silt.Float Module Variance StepsL Claw Flume.Page
variable {i j d k m r l b:ℕ}{n:Side}{S:Finset Cover}{o:Cover}
namespace Prom
-- local support emission
noncomputable def Stretch (x:Tray G S)(e:Edge Cover):G.Color:= if h:e∈crossV S then x ⟨e,h⟩ else 0
noncomputable def Spear (x:Tray G S)(u: Cover×Shade G):ℝ:= Stretch x (u.1,u.2.1) u.2.2
lemma subL (x:Tray G S)(p:Edge Cover):indexS p (Spear x)= Stretch x p:=rfl
lemma norm_s_ (x:Tray G S)(p:Edge Cover): ‖indexS p (Spear x)‖ ≤ ‖x‖:=by rw [subL]; unfold Stretch; split; exact norm_le_pi_norm ..; rw[norm_zero]; positivity
lemma proc (x:Tray G S)(t:ℝ): lobK G S (t • x)=lotU (t • Spear x):=by
       funext i; unfold lobK TipP lotU; rw [map_smul,subL]; unfold Stretch; split; rfl; rw[smul_zero,G.mat_lieExp_zero]
lemma adv_root {E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F] (Q:E→L[ℝ] F){f:ℝ→ E}(h:ContDiff ℝ ω f)(n:ℕ):iteratedDeriv n (Q∘f) 0= Q (iteratedDeriv n f 0):=by unfold iteratedDeriv; erw [Q.iteratedFDeriv_comp_left h.contDiffAt le_top];rfl
lemma boom (G:Gauge)(d:ℕ): ∃ C:ℝ,0 ≤ C∧∀ (S:Finset Cover)(n:ℕ)(o:Cover)(P:Prom S o n)(x:Tray G S),‖x‖≤1→ ‖iteratedFDeriv ℝ d (fun t:ℝ=>P.brood (t • x)) 0‖≤ C*((n:ℝ)+1)^d:=by
       obtain ⟨A,h,H⟩:= pointBill G d 1 zero_le_one; obtain ⟨q,hq,hQ⟩:= (show ∃ K:ℝ,0<K∧∀ x:G.Mat, ‖milk G x‖≤K*‖x‖ from ContinuousLinearMap.bound _); let C:= q*A* 2^d; refine ⟨C,?_,fun S n o P x hx=>?_⟩; · unfold C; positivity
       rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]; let F(t:ℝ):=P.brood (t • x); let Q:=iteratedDeriv d F 0; have hT : ContDiff ℝ ω F:=(P.bliss G).comp (contDiff_id.smul contDiff_const); have he:0≤ C*((n:ℝ)+1)^d:=by unfold C; positivity
       refine (pi_norm_le_iff_of_nonneg he).2 (fun i=>?_); let f(t:ℝ):=G.mat (travel (lotU (t • Spear x)) o (P.ringL i)); let z:Tray G S→L[ℝ] G.Color:= ContinuousLinearMap.proj i; have hz: Q i= milk G (iteratedDeriv d f 0):=by
             rw [show Q i=iteratedDeriv d (z∘F) 0 from (adv_root z hT d).symm]; have ht(t:ℝ):(z ∘ F) t=(milk G ∘ f) t:=by change P.current _ i=_; rw [currentM, proc]; rfl
             rw [funext ht]; exact adv_root (milk G) (show ContDiff ℝ ω f from fluted (P.ringL i) _ (Spear x)) d
       change ‖Q i‖≤_; rw [hz]; let a:ℝ:=n; let u:ℝ:= (P.ringL i).length; calc
            _ ≤ q*‖iteratedDeriv d f 0‖:= hQ _
            _ ≤ q*(A*(u+1)^d):=mul_le_mul_of_nonneg_left (H _ _ _ (fun i _=> (norm_s_ x i).trans hx) 0) hq.le
            _ ≤ q*(A*((2*((n:ℝ)+1))^d)):=by gcongr; unfold u; have hv:=P.via i; linarith only[show ((P.ringL i).length:ℝ) ≤ 2*(n:ℝ)+1 from by exact_mod_cast hv]
            _ = _:=by unfold C; rw [mul_pow]; ring
end Prom
end YM.OPE.Merchant
