import YM.OPE.Compatible.Anchor.Motions
import YM.OPE.Compatible.Tips.Thel
import YM.OPE.Compatible.Glim.Rib
/-! # optical force readings. index slots structural -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Variance
open Function Filter Set MeasureTheory Lattice Laurent Wilson RG Precision Metric Matrix Cascade Finset
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{P:ChartRatio G}
attribute [local instance] Gauge.frobInner
open Next.SectorChange Stationary
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion
open Flock Libra.Shell Next.Foundations Weir Score Exterior Bloch Next.Free Frequency Streamer AnalyticNext.QuarticMatch.Joint Votive Flume Flume.Script Glass Quit.PriceZ Quit Paver
open Drift Char Silt Silt.Float Alps Roles Planned.PrimaryIntegral295.Carrier
variable {u d s r l k m:ℕ}{W I:Type}{τ:Phase→ℕ}
variable {n c:Side} (a: Axis)
noncomputable abbrev angleZ (z:RootEdge):RootEdge:= ((Wm a).act z.1+ dust a z.2,z.2)
lemma vert (x:Site n)(z:RootEdge): Quit.spur a (placed n (dart a x) z)=placed n x (angleZ a z):=by
      unfold angleZ placed Quit.spur; rw [errand]; dsimp; rw [(Wm a).act_add, dart, wrap_signed,← Signed.act_mul,ζFlags,Signed.act_one]; simp only [map_add]; unfold dust; split <;> simp [add_assoc]
variable [Fintype I]
noncomputable abbrev Turned (U:I→RootEdge): Libra.Keys G I →L[ℝ] Libra.Keys G I:= Flick (Equiv.refl I) (fun i=> (Wm a).flip (U i).2)
omit [Fintype I] in
lemma lensC (U:I→RootEdge)(x:Site n): dip U n (dart a x) (G:=G)∘L (Quit.streak a G n)= (Turned a U)∘L dip (angleZ a ∘ U) n x :=by
      ext1 y; funext i; change ((Quit.streak a G n y) (sett n (dart a x) (U i)))=_; unfold sett Quit.streak; rw [tread G _ _,FlickP,Yew,Yea]; rw [show sendEdge (Wm a) _ _=_ from vert a x (U i)]; change (if (Wm a).flip _ then _ else _)= Turned a U (dip (angleZ a ∘ U) n x y) i; rw [Turned,FlickP]; rfl -- split
variable {K:Sponsor G}{S:Seasons K}{w:ℝ}(A: Alps K S k w)
omit [Fintype I] in
lemma Saction (Y:I→RootEdge)(p: Libra.Keys G I→G.Color)(e:RootEdge)(b:Bool)(x:Site n)(h:Variance.Cand d (p∘ dip Y n (dart a x)))(hp:G.Simple) :
    let Y':=angleZ a ∘ Y; let u:= dart a x; (Cake (sett n u e) b (Dune A) (Rh A) (p∘ dip Y n u) d ∘ Quit.streak a G n)= Cake (sett n x (angleZ a e)) (b.xor ((Wm a).flip e.2)) (Dune A) (Rh A) ((p∘Turned a Y)∘ dip Y' n x) d:=by
       intro Y' u; symm; rw [show (p∘Turned a Y)∘ dip Y' n x= (p∘ dip Y n u) ∘ Quit.streak a G n from funext fun i=>congr_arg p (DFunLike.congr_fun (lensC a Y x (G:=G)) i).symm]; have h:= LeafEq (p:= sett n u e) (b:=b) (δH (Wm a)) (tourH (Wm a) (0:Site n)) (DuneAt A hp) h; dsimp only at h; rw [← tread, Dunear _ _ _, Rhythm _ _ _,sett,Yew,Yea, show sendEdge (Wm a) _ _=_ from vert a x e] at h; exact h
omit [Fintype I] in
lemma Candturned (Y:I→RootEdge)(p:Libra.Keys G I→G.Color)(x:Site n)(h:Variance.Cand d (p∘ dip Y n (dart a x))): Variance.Cand d ((p∘Turned a Y)∘ dip (angleZ a∘ Y) n x):=by
       rw [show (p∘Turned a Y)∘ dip (angleZ a ∘ Y) n x= (p∘ dip Y n _)∘ Quit.streak a G n from funext fun i=>congr_arg p (DFunLike.congr_fun (lensC a Y x (G:=G)) i).symm]; exact CandL h _
lemma RotHeld (Y:I→RootEdge)(p:Libra.Keys G I→G.Color)(e:RootEdge)(F:solar G s τ)(h:G.Simple)(hv:BudY e false d Y p)(hp:Holds F (SongY A e d Y p)): Holds (spose a G s τ F) (fun n u=>Cake (sett n u (angleZ a e)) (false.xor ((Wm a).flip e.2)) (Dune A) (Rh A) ((p∘ Turned a Y)∘ dip (angleZ a ∘ Y) n u) d):=by
       filter_upwards [hp] with n hn; funext i v; exact (toner a F.val i v).trans ((congr_fun (congr_fun hn _) (Quit.streak a G n v)).trans (congr_fun (Saction a A Y p e false i (hv.tilt_i n _) h) v))
end YM.OPE.Variance
