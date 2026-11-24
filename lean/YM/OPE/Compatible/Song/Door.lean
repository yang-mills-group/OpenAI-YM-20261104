import YM.OPE.Compatible.Song.Lion
import YM.OPE.Compatible.Song.Story
/-!
# Field Arrow.Dynamic Loom remuneration
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
variable {i j d k m r l b:ℕ}{n:Side} {w:ℝ}
variable {I W:Type} {B M:I→ℕ} {p:I→ Finset Cover} {N:I→ Side}{φ:Filter I}{Z:I→ℝ}{o:I→ Cover}
section
variable (b:ℕ)
abbrev FirmR (B:Finset (Edge Cover))(u:Bid.Dir G n→ G.Color)(r:ℕ):Prop:= u=Claw.rank u r ∧Crisp B u ∧(∀ x y,u (x+gillS (tor n) y)=u x)∧∀ g:G.El,∀ x,u (glint _ g x)=G.adjoint g (u x)
variable (A:Audience φ Z N M r) (u:CrysP N G) (h:∀ᶠ i in φ,FirmR (bark (M i)) (u i) d) (hp:Bills φ Z u) (e:↥(fieldP r))
lemma colorPrice {E:I→Type}[∀ i,NormedAddCommGroup (E i)] (f:(i:I)→ E i→G.Color)(d:G.ColorIndex)(ht:Tendsto Z φ atTop)(hz:Bills φ Z f): Bills φ Z (fun i=> (Phone G).coord d∘ f i):=by
        obtain ⟨b,hb,h⟩:=hz; let C:= ((Phone G).coord d).toContinuousLinearMap; refine ⟨_,((RateLE.const ‖C‖ ht).mul hb).mono (by norm_num),h.mono fun i hi x hp=>?_⟩; exact (C.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hi x hp) (norm_nonneg _))
lemma blank (G:Gauge)(n:Side)(e:Finset (Edge Cover)): FirmR e (0:Bid.Dir G n→ G.Color) k:=by
       refine ⟨?_ ,⟨fun _ _ _=>rfl⟩,(fun _ _=>rfl),fun _ _=>(map_zero _).symm⟩; funext i; unfold Claw.rank; rw [show Tensor.coeff (0:Bid.Dir G n→G.Color) k 0=0 from Tensor.coeff_zero k 0]; rfl
include h hp A e
lemma launch :∃ W:(i:I)→ Tray G (Lattice.box (M i)) → G.Color, (∀ j:G.ColorIndex,∀ s:Phase, Tonic (I:=fun i=>↥(bark (M i))) Z φ (fun i=>(Phone G).coord j ∘ W i) (d+s.val)) ∧(∀ i, BudY e.val false d (fun j:↥(bark (M i))=>j.val) (W i))∧∀ᶠ i in φ,∀ j:G.ColorIndex, jet ((Phone G).coord j ∘ (W i ∘ BlurD G (bark (M i)) (N i))) d=(Phone G).coord j ∘ u i:=by
       let f(i):= if FirmR (bark (M i)) (u i) d then u i else (0:Bid.Dir G (N i)→ G.Color); have ht(i): FirmR (bark (M i)) (f i) d:=by unfold f; split; assumption; exact blank ..
       let P(i:I):= Classical.choice (stadium (M i) e.val.1 (show _∈ _ from (cross_def _|>.1 (surf (A.room i).wide (mem_sdiff.mp e.property).1)).1))
       let T (i:I):Lattice.box (M i)⊆Lattice.box (M i):= fun _ h=>h; let H i:Board (N i) (M i):=(A.room i).board
       let W(i):= Oasis (P i) (M i) (T i) (H i) (f i); refine ⟨W,fun j s=>?_ ,fun i=> Prom.variant (P i) _ _ _ (f i) _ rfl (ht i).1 (ht i).2.2.1 (ht i).2.1 (ht i).2.2.2,h.mono (fun i hi j=> ?_)⟩
       · let q(j:G.ColorIndex)(i:I):=(Phone G).coord j∘ f i; have hf:Bills φ Z f:= hp.merge (h.mono fun i hi=>(if_pos hi).symm)
         have hT:∀ i, Tall (q j i) d:=fun i=>Tall.tag le_rfl (marks_j (f i) (ht i).1 (ht i).2.2.1 (ht i).2.1 j).1; refine Basin P (q j) T H A.fair ?_ (colorPrice f j A.fair hf) (Eventually.of_forall hT) (d+s.val); push_cast; exact ((RateLE.const (10:ℝ) A.fair).mul A.cash).mono (by norm_num)
       · exact (Prom.mapQ (P i) _ _ _ (f i) (ht i).1 (ht i).2.2.1 (ht i).2.1 j).trans (congr_arg _ (show f i=u i from if_pos hi)) -- refine may need disambig
end
end YM.OPE.Merchant
