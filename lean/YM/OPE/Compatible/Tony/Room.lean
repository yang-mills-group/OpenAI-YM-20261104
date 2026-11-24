import YM.OPE.Compatible.Tony.Rot
/-!
# Shadow terms.Quilt. Expose Loyalty ∀Z. observer.
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
namespace Sleeve
variable {I:Type}{A:I→ Side}{a c:ℝ}{φ:Filter I}{Z:I→ℝ}{W:I→ℕ}
variable {K:Sponsor G}{T:Seasons K}{v:I→ℝ}
variable (V:(j:I)→ Alps K T i (v j))(B:Scaffold φ Z A W r)
namespace Scaffold
variable {p p' q q':GlyphQ G A}
variable (H:Shor B p p') (H':Shor B q q')
variable (e:↥(fieldP r))(u:G.ColorIndex)
local notation "Pi!"=> fun i:I=>bark (W i+1)
open Quit.Jac
lemma tissue {f f': Forge G A} (h:PlaneQ (Pi!) φ Z f (k+1))(hv:∀ᶠ i in φ,f i=f' i): PlaneQ (Pi!) φ Z f' (k+1):=by constructor; intro p; refine (h.roll p).congress (hv.mono fun i hi=>?_); unfold eyeR;rw[hi]
include H in lemma lineP: PlaneQ (Pi!) φ Z (loft A e.val u (ofCourse p' 2)) 1:=by
       let z:= rerun e.val u p'; let X:=ofCourse z 1; rw [show loft _ _ _ _= X from funext fun i=> pry_mold (p' i) 1 (H.smooth_s i) _]; constructor; intro i; fin_cases i<;>first|exact (H.rim e u 1 0).2|exact (H.rim e u 2 0).2|exact (H.rim e u 3 0).2 -- 2 rank?
include H in lemma lineT: PlaneQ (Pi!) φ Z (loft A e.val u (ofCourse p' 0)) 1:=by
       let z:= rerun e.val u p'; let X:= LiftA 1 (ofCourse z 0); rw [show loft _ _ _ _= X from funext fun i=>?_]; rotate_left; · rw[show loft _ _ _ _ i= _ from (show loft A e.val u (ofCourse p' 0) i=_ from pry_m0 (p' i) (H.smooth_s i) _)]; funext j; change Ū*_=Ū^1*_; rw [pow_one];rfl
       refine PlaneQ.zoomP B.top.fair 1 ?_ (k:=0) (by omega)
       constructor; intro i; fin_cases i<;> first|exact (H.rim e u 0 0).2|exact (H.rim e u 1 0).2|exact (H.rim e u 2 0).2
include H H' in lemma Feather: PlaneQ (Pi!) φ Z (loft A e.val u (billcoat p' q')) 1:=by
       rw [show loft A e.val u (billcoat p' q')=loft A e.val u (ofCourse p' 2)+loft A e.val u (ofCourse q' 0) from funext fun i=> Variance.pryAdd _ _ _ (tallJ _ _) (tallJ _ _)]; exact PlaneQ.Shade B.top.fair (lineP B H e u) (lineT B H' e u)
variable (h:∀ i,Board (A i) (W i+1)) {R:Clip}
variable (hp:forall i,(V i).clip=R)(ht:RateLE φ Z v 0)(he:4 ≤ i)(hs:G.Simple)
include hp ht he hs
local notation "q₀"=> fun i:I=>W i+1
lemma harvest_ice:∃ (L:I→Law (Chamber G r)), (∀ i, SiteL (sailT G (B.top.room i).money) (chrom (HabitK A V i)) (L i) ∧∀ x: Chamber G r,2*damp r R*‖x‖^2≤ (L i).P x x) ∧ Shroud B.top (rawP V (q₀) h) (rawL V (q₀) h) L :=by
       have hv(i:I):∃ L:Law (Chamber G r), SiteL (sailT G (B.top.room i).money) (chrom (HabitK A V i)) L ∧∀ x,2*damp r R*‖x‖^2≤ L.P x x:=by
            let H:= (Merchant.station (B.top.room i).money (V i) he hs (tip (B.bone i) (show r+2 ≤ W i+2 from by have hx: r<W i+1:= (B.top.room i).wide; omega))) -- namespace collisions
            rw [hp i] at H; exact H
       choose L hL using hv; refine ⟨L,hL,⟨?_ ,?_ ,?_ ,fun i u=>?_⟩⟩
       · exact Eventually.of_forall fun j=> ⟨easy hs _ _,Consider (V j) (h j)⟩
       · exact Eventually.of_forall fun i=>Eraρ hs (V i) (h i) _ (B.top.room i).wide _ (hL i).1
       · exact ⟨_,mul_pos (by norm_num: 0 < (2:ℝ)) (dampK R r), Eventually.of_forall fun i=>(hL i).2⟩
       exact Feather B (hEra V hs B hp h) (lEra V hs B ht h) i u
end Scaffold
end Sleeve
end YM.OPE.Merchant
