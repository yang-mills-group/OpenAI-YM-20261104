import YM.OPE.Compatible.Song.Paw
import YM.OPE.Compatible.Song.Veil
/-!
# Habitat receipts for regional Tate assembler. Through Lens τ
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
variable {M:I→ℕ}
abbrev CrysP (N:I→ Side)(G:Gauge):= (i:I)→Bid.Dir G (N i)→G.Color
set_option quotPrecheck false
structure ShineX (_A:Audience φ Z N M r)(V:CrysP N G)(p:ℕ)(e:↥(fieldP r)) :Prop where
       march : ∀ᶠ i in φ, Variance.Cand p (V i)∧ rooted (sett (N i) 0 e.val) false (tor (N i)) (V i)
       cost :∀ u:G.ColorIndex, PlaneQ (fun i=>bark (M i)) φ Z (N:=N) (G:=G) (fun i=>Pawn.mold ((Phone G).coord u ∘ V i) p) p
-- `A` unused precise FQS need keep as argument? linter.Warn.
section
variable {f:GlyphQ G N}(ht:Tendsto Z φ atTop) (V:(i:I)→ Libra.Keys G (B i)→ ℝ)
noncomputable abbrev pensH (p:ℕ):Forge G N:=fun i=>Pawn.mold (V i ∘ BlurD G (B i) (N i)) p
private lemma legalT {p:ℕ}(h:Tonic (I:=fun i=>↥(B i)) Z φ V p)(hx:∀ᶠ i in φ,ContDiffAt ℝ ω (V i) 0): Filμ B φ Z (N:=N) (G:=G) (fun i=> jet (V i ∘ BlurD G (B i) (N i)) p) p:=by
        let C (i:I) := BlurD G (B i) (N i); let f(i:I):= V i; have he:∀ᶠ i in φ,∀ x,jet (V i ∘ C i) p x=jet (V i) p (C i x):=hx.mono fun i hi x=> congr_arg JetS.s (congr_fun (moldC (C i) _ hi p) x)
        obtain ⟨w,h,H⟩:= h; refine ⟨he.mono (fun i hi=> ⟨fun x y hy=> (hi x).trans ((congr_arg _ hy).trans (hi y).symm)⟩),Eventually.of_forall fun i=>Tall.loan (Tensor.coeff (f i ∘ C i) p 0) le_rfl,w,h,(he.and H).mono (fun i hi x hp=>?_)⟩; change ‖jet (V i∘ C i) _ x‖ ≤_; rw [hi.1 x]; exact hi.2 _ (fun _=>(buf G _ x).trans hp)
lemma pool_h (p:ℕ)(hv:∀ i:Phase,Tonic Z φ V (p+i.val))(hx:∀ᶠ i in φ,ContDiffAt ℝ ω (V i) 0):PlaneQ B φ Z (pensH V (N:=N) p) p:=by
       constructor; intro s; fin_cases s <;> first|exact legalT V (hv 0) hx|exact legalT V (hv 1) hx|exact legalT V (hv 2) hx
end
section
variable (A:Audience φ Z N M r) (e:↥(fieldP r))
local notation "B!"=>fun i:I=>bark (M i)
local notation "N!"=>fun i:I=> N i
include A
lemma sweat (u:G.ColorIndex): RateLE φ Z (fun i=> ‖functorE (0: Site (N i)) e.val u‖) 0:=by
       let J:= (e,u); let C:= ‖PickL G J‖; refine RateLE.absBound C A.fair ?_; filter_upwards with i; rw [Real.norm_of_nonneg (norm_nonneg _)]; exact (show _= _ from (congr_arg norm (ferryT G (A.room i).money e u).symm)).trans_le (sailX _ _ _)
lemma roof (p:GlyphQ G N)(u:G.ColorIndex)(d:ℕ)(hv: PlaneQ (B!) φ Z (N:=N) (G:=G) (fun i=> Pawn.mold (p i) d) d)(h:∀ᶠ i in φ, ContDiffAt ℝ ω (p i) 0): PlaneQ (B!) φ Z (loft N e.val u (fun i=>Pawn.mold (p i) d)) d:=by
       let x(i:I):= functorE (0: Site (N i)) e.val u; have hx:= sweat A e u; constructor; intro s; fin_cases s <;> first|exact Phil p x h hx A.fair (hv.roll 0) | exact Phil p x h hx A.fair (hv.roll 1) | exact Phil p x h hx A.fair (hv.roll 2)
lemma hold_stamp (a j:G.ColorIndex): PlaneQ (B!) φ Z (N:=N) (G:=G) (fun i=>Mount (sett (N i) 0 e.val) ((Phone G) a) false j) 0:=by
       let D:=(Phone G).coord j; let f:G.Color→ℝ:=D ∘ Cast false ((Phone G) a); have hf:ContDiffAt ℝ ω f 0:= D.toContinuousLinearMap.contDiff.contDiffAt.comp _ (cast_sm ..)
       let L(i:I):=ContinuousLinearMap.proj (φ:=fun _: Body 1 (N i)=>G.Color) (R:=ℝ) (sett (N i) 0 e.val); let Q(i:I)(s:Phase):= jet (f ∘ L i) s.val; have h(i)(x:Bid.Dir G (N i))(s:Phase): Q i s x=jet f s.val (L i x):=congr_arg JetS.s (congr_fun (moldC _ _ hf _) x)
       have hv(s:Phase) :Filμ (B!) φ Z (N:=N) (G:=G) (fun i=>Q i s) s.val:=by
            refine ⟨Eventually.of_forall (fun i=> ⟨fun x y hE=>?_⟩),Eventually.of_forall (fun i=> Tall.loan (Tensor.coeff (f ∘ L i) s.val 0) le_rfl),?_ ⟩
            · rw [h,h]; apply congr_arg; have ht:= (surf (A.room i).wide) (mem_sdiff.mp e.property).1; let y':↥(bark (M i)):=⟨e.val,ht⟩; exact congr_fun hE y'
            let C:=Tensor.coeff f s.val 0; refine ⟨fun _=>‖C‖,RateLE.const _ A.fair,Eventually.of_forall fun i x he=>?_ ⟩; change ‖Q i s x‖ ≤ ‖C‖;rw[h]; refine (C.le_opNorm _).trans (mul_le_of_le_one_right (norm_nonneg _) (Finset.prod_le_one (fun _ _=>norm_nonneg _) (fun j _=>?_))); exact (norm_le_pi_norm x _).trans he
       constructor; intro i; rw[Nat.zero_add]; fin_cases i<;> first|exact hv 0|exact hv 1|exact hv 2
end
end YM.OPE.Merchant
