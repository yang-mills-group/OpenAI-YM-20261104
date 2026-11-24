import YM.OPE.Compatible.Tony.Ray
/-!
# Alt.Const for directional symbols
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
open Drift Char Silt Silt.Float Module Variance StepsL Claw Prom Ibis Merchant.SiteL Flume.Page Wool
variable {i j d k m r l b:ℕ}{n:Side}
local notation "D!"=> Bid.Dir G n
section
lemma leapB (G:Gauge)(a:Edge Cover)(s:ℝ)(k:ℕ)(h:0<s):∃ C:ℝ,0 ≤ C∧∀ q:G.ColorIndex,∀ (n: Side)(p:Script (Shade G) (k+1))(f:Bid.Dir G n→ℝ)(c:ℝ), ContDiffAt ℝ ω f 0→ Felt p s c→ Voice p (spool G n).toContinuousLinearMap f→∀ (r:ℕ)(b:ℝ),0 ≤ b→ ∀ v:Fin k→ Bid.Dir G n,(∀ i,Roster (v i) ≤ b)→ let M:= sillM G n (r+1); let z:=bat (functorE 0 a q) f; let T:=iteratedFDeriv ℝ k z 0; ‖T v‖≤ C*b^k*c ∧ ‖T v- T (M ∘ v)‖ ≤ C*b^k * c * Real.exp (-(s/4)*r):=by
        obtain ⟨C,hC,Z⟩:= Altitude (I:=Shade G) k (size a.1) s h; obtain ⟨Y,hY,hZ⟩:= Plenty (I:=Shade G) k (size a.1) s h; refine ⟨C+Y,add_nonneg hC hY,fun q n p f c hf hp ht r b hb v hv=>?_⟩; intro M z T
        let x:= (Moor a n).1; let V:=functorE (0:Site n) a q; have hx:pdist x ≤ size a.1:= Next.Free.within_size ..; have hT:= BudgetV (n:=n) a q; let L:=(spool G n).toContinuousLinearMap; let F(w:Fin k→Bid.Dir G n): Fin (k+1) → Flume.Script.deck (Shade G) n:= Fin.cons (L V) (L ∘ w); have hu:0 ≤ c:=Sack.coins hp; have hhS(w:Fin k→Bid.Dir G n): T w= library n p (F w):=by
             change iteratedFDeriv ℝ _ (Analysis.D V f) 0 w =_; rw [← Analysis.cons_inner (hf.of_le le_top),← ht]; apply congr_arg; funext i; refine Fin.cases ?_ (fun j=>?_) i; rfl; simp [F]; rfl
        rw [hhS, hhS]; have he(i): Revenue b (L (v i)):=spoolE _ (hv i); have hm(i): Revenue b (L (M (v i))):=spoolE _ ((shrink _ _).trans (hv i)); refine ⟨(hZ _ _ p c hp hx _ _ _ _ zero_le_one hb hT he).trans ?_,(Z _ _ p _ r hp hx (L ∘ v) (L ∘ M ∘ v) _ _ _ zero_le_one hb hT he hm (fun _=>shiftM ..)).trans ?_⟩
        · rw [mul_one]; gcongr; exact le_add_of_nonneg_left hC
        rw [mul_one,mul_right_comm _ (Real.exp _)]; gcongr; exact le_add_of_nonneg_right hY
-- tensor Budget.Orients, lower absolute around origin only, under Costume. 
noncomputable def tfan (p:Edge Cover)(u:G.ColorIndex)(n:Side)(f:Bid.Dir G n→ℝ):= bat (functorE 0 p u) f
lemma linearX {E F: Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F](D:E→L[ℝ] F)(k:ℕ)(g:F→ℝ)(h:ContDiffAt ℝ ω g 0)(v:Fin k→E) :iteratedFDeriv ℝ k (g∘D) 0 v=iteratedFDeriv ℝ k g 0 (D ∘ v):=by rw[jets_linear D (h.of_le le_top)];rfl
lemma Tenter (G:Gauge)(s:ℝ)(h:0<s)(a:Edge Cover)(k:ℕ):∃ C:ℝ,0 ≤ C∧∀ (n:Side)(u:G.ColorIndex)(f: Bid.Dir G n→ℝ) (p:Script (Shade G) (k+1))(c:ℝ), ContDiffAt ℝ ω f 0→ Felt p s c→ Voice p (spool G n).toContinuousLinearMap f →∀ r:ℕ, let V:= (tellerT G n).toContinuousLinearMap; let w:=tfan a u n f; ‖iteratedFDeriv ℝ k (w ∘ V) 0‖ ≤ C*c∧ ‖iteratedFDeriv ℝ k ((w- (w ∘ sillM G n (r+1))) ∘ V) 0‖ ≤ C*c*Real.exp (-(s/4)*r):=by
       obtain ⟨C,hC,H⟩:= leapB G a s k h; refine ⟨C,hC,fun n u f p c hx hP hQ r=>?_⟩; intro V w; have hv: ContDiffAt ℝ ω w 0:= picked f hx (functorE 0 a u); have hc:= Sack.coins hP; let t:= C*c; have ht:0 ≤ t:=mul_nonneg hC hc; let M:=sillM G n (r+1); have hz:ContDiffAt ℝ ω (w∘M) 0:= (M.map_zero.symm ▸ hv:ContDiffAt ℝ ω w (M 0)).comp _ M.contDiff.contDiffAt
       let D:=w-(w ∘ M); have hd:ContDiffAt ℝ ω D 0:= hv.sub hz; let b:=Real.exp (-(s/4)*r); let F:= iteratedFDeriv ℝ k (w ∘ V) 0; let W:= iteratedFDeriv ℝ k (D∘V) 0
       have he(x): Roster (V x) = ‖x‖:=congr_arg norm ((tellerT ..).symm_apply_apply x)
       have hh(x:Fin k → Bid.Dir G n)(h:∀ i,‖x i‖ ≤1): ‖F x‖ ≤ C*c∧ ‖W x‖≤t*b:=by
            let L:=iteratedFDeriv ℝ k w 0; let g:=V∘x; have h (v:Fin k):Roster (V (x v))≤1:= (he (x v)).trans_le (h v); have h1:=H u n p f c hx hP hQ r 1 zero_le_one g h; norm_num only [one_pow,mul_one] at h1; unfold F W; rw[linearX _ _ _ hv,linearX _ _ _ hd, show iteratedFDeriv ℝ k D 0= _ from iteratedFDeriv_sub_apply (hv.of_le le_top) (hz.of_le le_top),_root_.sub_apply,linearX _ _ _ hv]; exact h1
       exact ⟨Dollar ht (fun x hx=>(hh x hx).1),Dollar (mul_nonneg ht (Real.exp_nonneg _)) (fun x hx=>(hh x hx).2)⟩
end
end YM.OPE.Merchant
