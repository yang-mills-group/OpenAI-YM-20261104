import YM.OPE.Compatible.Song.Amt
import YM.OPE.Compatible.Song.Door
/-!
# Actual chamber field. Birth Lease
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
variable {M:I→ℕ}(A:Audience φ Z N M r)(f g:GlyphQ G N)(T:I→ Law (Chamber G r))
namespace Shroud
variable (u:GlyphQ G N)(k:ℕ)(i:I)
open OrientX
variable (V: ∀ i,Board (N i) (r+1))
noncomputable abbrev scion:=νrt (chrom (f i)) (sailT G (V i)) (T i) (u i) k
noncomputable abbrev exP:=ρX (chrom (f i)) (sailT G (V i)) (T i) (u i) k
variable (S: Shroud A f g T)
variable (h: Filμ (fun i=>bark (M i)) φ Z u d) (he:∀ᶠ i in φ, LevelA (tor (N i)) (u i))
local notation "p!"=> scion f T u k
section
-- store all material.Scale outside applications
set_option maxHeartbeats 200000
abbrev Fort {F:Type}[Fintype F](X:Bid.Dir G n→ Keys G F)(d:ℕ)(w:ℕ):Prop:= Crisp (bark w) X∧ X=Claw.rank X d ∧ContDiff ℝ ω X ∧(∀ i v,X (i+gillS (tor n) v)= X i) ∧∀ x g,X (glint _ g x)=glint _ g (X x)
variable {E:Type}[Fintype E](F:(i:I)→ Keys G E→L[ℝ] Bid.Dir G (N i))(K:(i:I)→ Bid.Dir G (N i)→ₗ[ℝ] Dual' (Bid.Dir G (N i))) (N':I→Law (Keys G E))
include h he
lemma GroupV (hp:∀ᶠ i in φ, OrientX (tor (N i)) (K i) (F i) (N' i))(hx:∀ᶠ i in φ, Crisp (bark (M i)) (fun x=> pour (F i) (K i) (N' i) x)):∀ᶠ i in φ, Fort (νrt (K i) (F i) (N' i) (u i) k) k (M i):=by
       filter_upwards [hp,hx,h.here,h.tariff,he] with i hi hE hx ht hg; refine ⟨⟨fun x y hh=>?_⟩,fuelω (K i) (F i) (N' i) _ k,dutyω (K i) (F i) (N' i) _ k,fun x y=>hi.frameS _ hg ht.neat.contDiffAt y x, fun x g=>hi.FrameAd _ hg ht.neat.contDiffAt x g⟩; exact remN (K i) (F i) (N' i) _ (u i) hx.jury hE.jury ht.neat.contDiffAt x y hh
lemma Exo (hp:∀ᶠ i in φ, OrientX (tor (N i)) (K i) (F i) (N' i))(hx:∀ᶠ i in φ, Crisp (bark (M i)) (fun x=> pour (F i) (K i) (N' i) x)):∀ᶠ i in φ,let p:=ρX (K i) (F i) (N' i) (u i) k; Crisp (bark (M i)) p ∧ p=Claw.rank p (k+1)∧ LevelA (tor (N i)) p∧∀ x y,p (x+F i y)=p x:=by
       filter_upwards [hp,hx,h.here,h.tariff,he] with i hi hE hx ht hg; intro p; let H := sun₀ _ (K i) (F i) (N' i) (u i) hi k hg ht.neat.contDiffAt; exact ⟨⟨fun x y hv=> rimE (K i) (F i) (N' i) (BlurD G _ _) _ hx.jury hE.jury ht.neat.contDiffAt x y hv k⟩,(diana (K i) (F i) (N' i) _ _).symm,H⟩
omit he
lemma Poseρ (ht:Tendsto Z φ atTop)(hv:Bills φ Z (fun i x=> mate (F i) (K i) (N' i) x)): Bills φ Z (fun i=> ρX (K i) (F i) (N' i) (u i) k):=by
       obtain ⟨b,hb,H⟩:=hv; have hx:=Breeze ht h.loud h.tariff (k+1); have he: ∀ᶠ i in φ,Tall (Claw.rank (u i) (k+1)) (k+1):=Eventually.of_forall fun i=>Tall.loan _ le_rfl
       obtain ⟨a,ha,h'⟩:= hx.radiusH ht hb he; exact ⟨a,ha,(h'.and H).mono fun i hi x hx=> hi.1 (mate _ _ _ x) (hi.2 x hx)⟩
end
set_option maxHeartbeats 200000
include S
lemma boonJ :∀ᶠ i in φ, OrientX (tor (N i)) (chrom (f i)) (sailT G (V i)) (T i):= birth A f g T S
set_option maxHeartbeats 200000 in lemma loam :∀ᶠ i in φ, Crisp (bark (M i)) (fun x=> pour (sailT G (V i)) (chrom (f i)) (T i) x):=by
  filter_upwards [leap A f g T S] with i hi
  have field : (fun x:Bid.Dir G (N i) => ΘT A f T i x)=
      (fun x:Bid.Dir G (N i) => pour (sailT G (V i)) (chrom (f i)) (T i) x) :=
    congrArg (fun W:Board (N i) (r+1) => fun x:Bid.Dir G (N i) =>
      pour (sailT G W) (chrom (f i)) (T i) x)
      (Subsingleton.elim (A.room i).money (V i))
  rw [←field]
  exact hi
include h he
lemma eman :∀ᶠ i in φ, Fort (scion f T u k i V) k (M i):=by
       unfold scion; exact GroupV u k h he (fun i:I=>sailT G (V i)) (fun i:I=>chrom (f i)) T (boonJ A f g T V S) (loam A f g T V S)
elab "originalOutputType% " t:term : term => do
  let v ← Lean.Elab.Term.elabTerm t none
  Lean.Meta.inferType v
lemma ηspout : originalOutputType% (Exo u k h he (fun i:I=>sailT G (V i)) (fun i:I=> chrom (f i)) T (boonJ A f g T V S) (loam A f g T V S)) :=
  Exo u k h he (fun i:I=>sailT G (V i)) (fun i:I=> chrom (f i)) T (boonJ A f g T V S) (loam A f g T V S)
lemma rump :∀ᶠ i in φ,Crisp (leash r (M i)) (exP f T u k i V) ∧ exP f T u k i V=Claw.rank (exP f T u k i V) (k+1)∧ LevelA (tor (N i)) (exP f T u k i V):=by
       filter_upwards [ηspout A f g T u k V S h he] with i hi; exact ⟨Crisp.cull (M i) (A.room i).board (A.room i).wide hi.1 (V i) hi.2.2.2 hi.2.2.1,hi.2.1,hi.2.2.1⟩
omit he
omit S h in
private lemma exP_apply (i:I) (x:Bid.Dir G (N i)) :
    exP f T u k i V x=Claw.rank (u i) (k+1) (mate (sailT G (V i)) (chrom (f i)) (T i) x) :=by
  simp only [exP,ρX,Function.comp_apply]
lemma extRate : Bills φ Z (fun i=>exP f T u k i V) :=by
  obtain ⟨w,hw,H⟩:=S.polesξ A f g T V
  have core:=Breeze A.fair h.loud h.tariff (k+1)
  have retained : ∀ᶠ i in φ,Tall (Claw.rank (u i) (k+1)) (k+1) :=
    Eventually.of_forall (fun i=>Tall.loan _ le_rfl)
  obtain ⟨c,hc,priced⟩:=core.radiusH A.fair hw retained
  refine ⟨c,hc,(priced.and H).mono ?_⟩
  intro i bill x small
  change ‖exP f T u k i V x‖ ≤ c i
  rw [exP_apply]
  let z : Bid.Dir G (N i) := mate (sailT G (V i)) (chrom (f i)) (T i) x
  have inside : ‖z‖≤w i := bill.2 x small
  exact bill.1 z inside
end Shroud
end YM.OPE.Merchant
