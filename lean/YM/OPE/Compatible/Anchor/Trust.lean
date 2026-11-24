import YM.OPE.Compatible.Anchor.Lead
import YM.OPE.Compatible.Rhus.Scar
/-! # Boose moment criterion -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Variance
open Function Filter Set MeasureTheory Lattice Laurent Wilson RG Precision Metric Matrix Cascade Finset Labels
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{P:ChartRatio G}
attribute [local instance] Gauge.frobInner
open Next.SectorChange Stationary
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion Work.F08
open Flock Libra.Shell Next.Foundations Weir Score Exterior Bloch Next.Free Frequency Streamer AnalyticNext.QuarticMatch.Joint Votive Flume Flume.Script Glass Quit.PriceZ Quit Paver FreeResolvent WithLp
open Drift Char Silt Silt.Float Module Page Planned.PrimaryIntegral295.Carrier
variable {i j d k m r n l:ℕ}{Z I J M E F:Type}
-- ↑indexIt. identify by charge-limit using ψ.Sensors.
variable (p:cope G r m)
local notation "θ"=> 𝓝[>] (0:ℝ)
noncomputable abbrev Lug(p:Script (Shade G) r) (x:Alphabet G d) (v:ℝ):= wholeX p (fun _=>showerW d v x)
lemma lune (x:Alphabet G d)(h:r*d ≤ m): ContDiff ℝ ω (Lug p.val x):=by
     rw [show Lug p.val x=fun t:ℝ=>∑ k:Fin r→Fin d, t^rankX k • solidX p.val k (fun _=>x) from funext fun i=> showerView p h i _]; exact ContDiff.sum (fun s _ => contDiff_id.pow _|>.smul contDiff_const)
lemma strainT (x:Alphabet G d)(h:r*d≤m)(hv:n≤ m):
   WardBin.leading n (Lug p.val x) = (Flume.Script.tiller G r m n hv d p).val (fun _=>x):=by
      rw [show Lug p.val x=fun t:ℝ=>∑ k:Fin r→Fin d, t^rankX k • solidX p.val k (fun _=>x) from funext fun i=> showerView p h i _]; let F(i:Fin r→Fin d)(v:ℝ):= v^rankX i • solidX p.val i (fun _=>x); rw[show WardBin.leading n (fun t=>_) = ∑ i,WardBin.leading n (F i) from WardBin.lead_sum (f:=F) _ (fun i _=> (contDiffAt_id.pow _|>.smul contDiffAt_const))]; change _= (honeyX p.val _ _ d) _; unfold honeyX;rw [_root_.sum_apply]; refine sum_congr rfl (fun i _=>?_); unfold F; rw[WardBin.lead_monomial]; unfold actX; split; next h=> rw[dif_pos h.symm];rfl
      next h=>rw [dif_neg (Ne.symm h)]; rfl
lemma prismInject (x y:partX G r k d)(h:∀ v:Alphabet G d,x.val (fun _=>v) = y.val (fun _=>v)): x=y:=by
     let A:MixX G r k (d+1):=(x,0); let B: MixX G r k (d+1):=(y,0); exact congr_arg Prod.fst (show A=B from mixUni A B fun v=>congr_arg (fun x:ℝ=>(x:ℂ)+Complex.I*((0:partX G r k d).val (fun _=>v):ℝ)) (h v))
lemma Bells_crit (h:r*d≤ m) (hz:n<m) (hv:n≤d) (f: Alphabet G d→ℝ)(ht:∀ x:Alphabet G d,Tendsto (fun i:ℝ=> (i^n)⁻¹ * Lug p.val x i) θ (𝓝 (f x))):
     Bells p.val n∧∀ x:Alphabet G d,(Flume.Script.tiller G r m n hz.le d p).val (fun _=>x)= f x :=by
          have hh(x:Alphabet G d)(k:ℕ)(hk:k≤m)(s:ℝ)(hp:Tendsto (fun i:ℝ=>(i^k)⁻¹ * Lug p.val x i) θ (𝓝 s)):(Flume.Script.tiller G r m k hk d p).val (fun _=>x)=s:=(strainT p x h hk).symm.trans (WardBin.leading_of_lim ((lune p x h).of_le le_top|>.contDiffAt) _ hp)
          constructor; swap; · exact fun x=> hh x n hz.le _ (ht x)
          have hp0(v:ℕ)(hp:v≤n): Bells p.val v:=by
               induction v with | zero=> exact fun _ _ he=>by simp at he| succ v ih=>
                 apply (roll_inject p.val (patent_till p) (show v < m from by omega) (d:=d) (by omega) (patent p).2.1 (ih (by omega))).mp; let Z:=Flume.Script.tiller G r m v (by omega) d p; have he: Z=0:=prismInject Z 0 fun x=>hh x v _ 0 (WardBin.falls (Nat.lt_of_succ_le hp) (ht x)); exact congr_arg Subtype.val he
          exact hp0 n le_rfl
end YM.OPE.Variance
