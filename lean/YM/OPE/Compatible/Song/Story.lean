import YM.OPE.Compatible.Song.Lion
import YM.OPE.Compatible.Song.Focus
/-!
# Lifting any demanding leading row λ through 2-order posture. Keep same chamber.
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
variable {f: GlyphQ G N}
variable (A:∀ i,p i⊆Lattice.box (B i)) (Y:∀ i,Board (N i) (B i)) (P:(i:I)→Prom (p i) (o i) (M i))
variable (he:Tendsto Z φ atTop) (hp:RateLE φ Z (fun i=>(M i:ℝ)) 0) (ht:Filμ (fun i=>crossV (p i)) φ Z f k) (hs:∀ᶠ i in φ, f i=Claw.rank (f i) k ∧ LevelA (tor (N i)) (f i))
include he hp ht hs P Y A
lemma porch :∃ U:Forge G N, PlaneQ (fun i=>crossV (p i)) φ Z U k∧ Divining φ U∧∀ᶠ i in φ,eyeR U 0 i=f i:=by
        let T:(i:I)→ Tray G (p i)→ℝ:=fun i=> Oasis (P i) (B i) (A i) (Y i) (f i); let U:= pensH T (N:=N) k
        have hm(j:Phase):Tonic Z φ T (k+j.val):= Basin P f A Y he hp ht.loud ht.tariff _; have hx:∀ᶠ i in φ,ContDiffAt ℝ ω (T i) 0:=ht.tariff.mono fun i hi=>((P i).schoolC (B i) (A i) (Y i) _ hi.neat).contDiffAt
        have hV:∀ᶠ i in φ,(tor (N i)).Marbles (U i) ∧ eyeR U 0 i=f i:=by
             filter_upwards [ht.here,hs] with i hi ⟨hh,hj⟩; let hT:=Φ_read (P i) (B i) (A i) (Y i) _ hh hi hj.tilts (fun a y=>hj.inherits y a); exact ⟨hT.1,hT.2.1⟩
        refine ⟨U,?_,⟨hV.mono (fun _ ht=>ht.1)⟩,hV.mono (fun _ ht=>ht.2)⟩; exact pool_h T k hm hx
end
-- external specialization
section
variable (A:Audience φ Z N M r)(p: GlyphQ G N)
variable (ht:Filμ (fun i=>leash r (M i)) φ Z p k)(hs:∀ᶠ i in φ, p i=Claw.rank (p i) k ∧ LevelA (tor (N i)) (p i))
include A ht hs
lemma PorchE :∃ U:Forge G N, PlaneQ (fun i=>leash r (M i)) φ Z U k∧ Divining φ U∧∀ᶠ i in φ,eyeR U 0 i=p i:=by
        let P(i:I):= Classical.choice (Aurora (A.room i).wide); apply porch (p:=fun i:I=>galaxy r (M i)) (B:=M) (fun _=>sdiff_subset) (fun i=>(A.room i).board) P A.fair ?_ ht hs
        push_cast; exact ((RateLE.const _ A.fair).mul A.cash).mono (by norm_num)
end
end YM.OPE.Merchant
