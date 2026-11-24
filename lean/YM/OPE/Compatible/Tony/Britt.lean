import YM.OPE.Compatible.Tony.Noro
/-!
# Relative chart-inflation estimates. Path without budget.Reference exterior law.
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
open Drift Char Silt Silt.Float Module Variance StepsL Claw Prom Ibis Merchant.SiteL Flume.Page StepsL Wool
variable {i j d k m r l b:ℕ}{n:Side}
local notation "D!"=> Bid.Dir G n
section
-- Numeric chart derivative lease ν
lemma snaps {B E:Type}[NormedAddCommGroup B][NormedSpace ℝ B][NormedAddCommGroup E][NormedSpace ℝ E](f:B→E)(h:ContDiffAt ℝ ω f 0)(x:B)(j:ℕ)(w:ℝ): iteratedDeriv j (fun t:ℝ=> f (t • w • x)) 0 = (w^j) • (iteratedDeriv j (fun t:ℝ=> f (t • x)) 0):=by
        have he(x): WardBin.leading j (fun t:ℝ=>f (t • x))=Tensor.diagonal (Tensor.coeff f j 0) x:= WardBin.leading_tensor _ _ (h.of_le le_top)
        let v:= ((j.factorial:ℝ)⁻¹); have hv: v ≠ 0:=by unfold v; positivity
        have hh:Function.Injective (fun x:E=> v • x):=smul_right_injective E hv; apply hh; dsimp only; rw [smul_comm v (w^j),show v • _=_ from he (w • x),show v • _=_ from he x];apply Tensor.homogeneous
lemma tether (_h:Board n b)(x:D!)(u:↥(RingP b)): let Q:=quay b; let v:=BlurD G (crossV (RingP b)) n x; travel (lobK G (RingP b) v) (anchorX b) (Q.voyage u)=travel (expandAt 0 (represent x)) (anchorX b) (Q.voyage u):=by intro Q v; exact ((quay b).trough u _ _ (glowQ x 0)).symm
lemma latchP (h:Board n b)(x:D!)(hx:Roster x ≤1): ‖BlurD G (crossV (RingP b)) n x‖ ≤ 1+(b:ℝ):=by
        refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i=>?_ ; rw [echoP]; apply (rentE x _).trans; convert! le_trans (mul_le_of_le_one_right (tensile ((Moor i.val n).1)).le hx) (show costume (Moor i.val n).1≤ _ from ?_) using 1
        change (1:ℝ)+↑(pdist (Moor i.val n).1) ≤ _; rw [show pdist (Moor i.val n).1=b from StepsL.rise _ ((cross_def _).1 i.property).1 h]
variable (G)
lemma tipHeight (d:ℕ) :∃ C:ℝ,0 ≤ C∧∀ b:ℕ,∀ (n:Side)(_:Board n b)(x:Bid.Dir G n),Roster x ≤1→∀ u:↥(RingP b), let f(t:ℝ):= travel (expandAt 0 (represent (t • x))) (anchorX b) ((quay b).voyage u); ‖iteratedDeriv d (fun t:ℝ=>G.mat (f t)) 0‖ ≤ C * ((b:ℝ)+1)^(2*d):=by
        obtain ⟨C,hC,H⟩:=pointBill G d 1 zero_le_one; refine ⟨C*32^d,mul_nonneg hC (by positivity),fun b n h x hx u=>?_⟩; intro f; let p:= (quay b).voyage u; let V(y):= G.mat (travel (lobK G (RingP b) y) (anchorX b) p); let L:=BlurD G (crossV (RingP b)) n x; let s:ℝ:=1+b; have hs:0<s:=by unfold s; positivity
        let z:= s⁻¹ • L; have he: s • z=L:= smul_inv_smul₀ hs.ne' _; have hz: ‖z‖ ≤1:=by unfold z; rw [norm_smul,norm_inv,Real.norm_of_nonneg hs.le]; exact (mul_le_mul_of_nonneg_left (latchP h x hx) (inv_nonneg.mpr hs.le)).trans_eq (inv_mul_cancel₀ hs.ne')
        have hp : (fun t:ℝ=>G.mat (f t))=(fun t:ℝ=> V (t • s • z)):=by funext i; unfold V; rw [he,← show BlurD G _ n (i • x) = _ from map_smul ..|>.trans rfl,tether h]
        have hh:(fun t:ℝ=> V (t • z))=(fun t=>G.mat (travel (lotU (t • Spear z)) (anchorX b) p)):= funext fun i=>by unfold V; rw[proc]
        rw [hp,snaps V (travelsB G (anchorX b) p).contDiffAt z,hh,norm_smul, norm_pow,Real.norm_of_nonneg hs.le]; calc
               _ ≤ s^d*(C*(p.length+1:ℝ)^d):=mul_le_mul_of_nonneg_left (H p _ _ (fun i _=>(norm_s_ z i).trans hz) _) (pow_nonneg hs.le _)
               _ ≤ s^d*(C*(32*((b:ℝ)+1))^d):=by gcongr; linarith only [show (p.length:ℝ) ≤ 32*b from by exact_mod_cast ((quay b).miles u)]
               _ = _:=by unfold s; rw [mul_pow]; ring
end
end YM.OPE.Merchant
