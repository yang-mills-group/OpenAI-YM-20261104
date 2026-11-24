import YM.OPE.Compatible.Sward.Vanish
import YM.OPE.Compatible.Frog.Eye
/-!
# Wick drag on infinite support gauge frames, fixed period as chosen.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Silt.Phere
open Next.Free Bloch MeasureTheory Function Filter Finset Lattice Laurent Flume Flume.Script Flume.Page Precision Module Libra Shell Char RG Work.F08 Float
open scoped Topology BigOperators Classical
variable {I G K E F X:Type}{m r i j n k:ℕ}{C D:ℝ} {H:Gauge}
open Cloud JetS
open scoped ContDiff
variable {v y:fieldX (Shade H)}
open Tensor WardBin
-- budget C estimate.O. Use masks of bad axes
open Cascade Terp Paver Rill Shell FreeResolvent Exterior MSbar.Tree MSbar.Tree.Resolvent Frequency Streamer
open Votive
variable {N:Side}{L:KernelChoices} (x:Site N)
open Drift Shell Char
variable {τ :Char.Phase→ℕ}{d:ℕ}
open PertExtension Series GaussianScore
open Matrix
section
lemma kuff (p:Seat k m (Shade H))(hp:settled (m:=m) p) {b: Side→ℕ}(hc:∀ c:Side,LightP (0:Site c) (m:=m) p∈ Breeze (Bid.Dir H c) j (b c)): Deep (m:=m) p j:=by
       intro i hi; let f:= lilies m k (Shade H) p i; have ht:= (sproutV _ _ p).2 i; have he(c:Side):formSong m k H (0:Site c) p i=0:=by
            let T:= LightP (0:Site c) (m:=m) p; let Y:= (flats H c).symm.toContinuousLinearMap; let S:= formSong m k H (0:Site c) p; have ht:Tensor.coeff T i 0=0:= (hc c).2 i hi; have hz:T∘ Y=Strike k S:= by ext1 v; unfold Function.comp T LightP; rw [← strikesT, show flats H c (Y v)= v from (flats H c).apply_symm_apply v]
            rw [← gradeC (chic (0:Site c) p hp) i, show Strike k _= _ from hz.symm]; ext1 v; rw [onceD _ T (polW (m:=m) _ p|>.cost) i,ht];rfl
       apply Flume.Script.home (T:=Shade H) (φ:=atTop) (sootS ht) summable_zero (hp i) (fun _=>rfl) epochX (tendsto_add_atTop_nat 1) (Eventually.of_forall _); -- home expect
       intro n w; change scribe 0 f (fun _=> w) = scribe 0 0 (fun _ :(Fin i)=> w); rw [show scribe _ f _=_ from (coupled i (m:=m) p (0:Site (epochX n)) (fun _=>w)).symm,he]; simp [scribe]
end
end YM.OPE.Silt.Phere
