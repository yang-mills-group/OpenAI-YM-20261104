import YM.OPE.Compatible.Anchor.Rook
/-! # Motor generators. Join as currents. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Variance
open Function Filter Set MeasureTheory Lattice Laurent Wilson RG Precision Metric Matrix Cascade Finset Labels
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius RealInnerProductSpace
variable {G:Gauge}{P:ChartRatio G}
attribute [local instance] Gauge.frobInner
open Next.SectorChange Stationary
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion Work.F08 Maxwell
open Flock Libra.Shell Next.Foundations Weir Score Exterior Bloch Next.Free Frequency Streamer AnalyticNext.QuarticMatch.Joint Votive Flume Flume.Script Glass Quit.PriceZ Quit Paver FreeResolvent WithLp
open Drift Char Silt Silt.Float Module Page Planned.PrimaryIntegral295.Carrier
variable {i j d k m r n l:ℕ}{Z I J M E F:Type}
local notation "θ"=> 𝓝[>] (0:ℝ)
variable {K:Sponsor G}{S:Seasons K}{u:M→ℝ}{τ:Phase→ℕ}
variable (L:M→Submodule ℝ (solar G d τ))(A:(j:M)→Alps K S i (u j)) {α:Fin r→Fin k} (X:partX G (r+1) n k)
variable (T: (i:Fin r)→ Taylor G (α i).val→ₗ[ℝ] Alphabet G k)
noncomputable def Teas : Alphabet G k→ₗ[ℝ] (MultilinearMap ℝ (fun i=> Taylor G (α i).val) ℝ):={
     toFun p:= MultilinearMap.compLinearMap (MultilinearMap.curryLeft X.val p) T
     map_add' x y:=by ext1 v; rw [map_add];rfl
     map_smul' a x:=by ext1 v; rw [map_smul];rfl }
abbrev taxCoord (v:Alphabet G k):∀ i:Fin r, Taylor G (α i).val:= fun i=>v (α i)
lemma arrayR (m v) : Teas X T m v=X.val (Fin.cons m fun i=> T i (v i)):=rfl
lemma turf {k:ℕ} (s:G.El)(p:HornIdx k)(v:G.Color): Pi.single (M:=fun _:HornIdx k=> G.Color) p (G.adjoint s v)=Ahorn s (Pi.single p v):=by funext i; change _=G.adjoint s (Pi.single (M:=fun _:HornIdx k=>G.Color) p v i); by_cases h:i=p; subst i; simp; simp[h]
lemma initial_u (g:Fin k)(hg:g.val=j+1)(hp:(r+1)*k ≤ τ 0)(he:r+1≤d)(hG:G.Simple)(h:Forum A L)(ht:∀ (i:Fin r)(s:G.El)(x:Taylor G (α i).val),T i (Taylor.paint s x)= spray s (T i x))(hx:n=j+2+rankX α):
    Obtains (ZTheta u) L (r+1) n (fun x: Alphabet G k=> (Teas X T) (monoX g (armK G g.val (x g))) (fun i=>x (α i))):=by
       let P:(HornIdx j)→ (G.Color→ₗ[ℝ] (MultilinearMap ℝ (fun i=> Taylor G (α i).val) ℝ)):=fun i=> Teas X T ∘ₗ Rosary g hg ∘ₗ (LinearMap.single ℝ (fun _:HornIdx j=>G.Color) i)
       have hv(i:HornIdx j)(v:G.Color)(x) : P i v x= Teas X T (Rosary g hg (Pi.single i v)) x:=rfl
       have hV(i:HornIdx j)(s:G.El)(v x): P i (G.adjoint s v) (fun i=> Taylor.paint s (x i))= P i v x:=by
            rw [hv,hv,turf, RosaryTurn,arrayR,arrayR]; apply Eq.trans _ ((show Off G (r+1) n k X.val from X.property).Colors s _); apply congr_arg X.val; funext j; refine Fin.cases ?_ (fun i=>?_) j; rfl; exact ht i s _ -- term x cast
       choose F hF hQ using fun i=> polyVe (P i) (hV i)
       let Q(i:HornIdx j):Alphabet G k→ℝ:= χFlat (F i) i.1 i.2 g hg; rw [show (fun x: Alphabet G k=> _)=(∑ i:HornIdx j,Q i) from ?_]; swap
       · funext x; rw [Finset.sum_apply]; let u:= x g; let w:= twist hg u; let v:= bets G j w; rw [show monoX g (armK G g.val (x g))= Rosary g hg v from ?_]; swap; · exact congr_arg (fun z:Taylor G g.val=>monoX g z) (Raylet hg (x g)).symm
         have he:v=∑ i:HornIdx j,Pi.single (M:=fun _:HornIdx j=>G.Color) i (v i):=by funext i; rw[Finset.sum_apply,sum_eq_single i]; simp;intro j _ hj; exact Pi.single_eq_of_ne hj.symm _;simp
         rw [he,map_sum,map_sum,_root_.sum_apply]; apply sum_congr rfl;intro i _; let t:= fun i=>x (α i); rw [show v i= _ from (show v i=flame (hg ▸ u) i.1 (basis ∘ i.2) from (by unfold v w; rw [twistSal];rfl))]; exact hQ i t _
       apply Obtains.sum L _ _ _ hp; intro i _; unfold Q; have hv:= renewZ L A (F i) i.1 i.2 g hg hp he hG (hF i) h; rwa [← hx] at hv
end YM.OPE.Variance
