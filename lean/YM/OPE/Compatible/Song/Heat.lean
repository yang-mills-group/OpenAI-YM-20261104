import YM.OPE.Compatible.Song.Dollar
import YM.OPE.Compatible.Song.Get
import YM.OPE.Compatible.Song.Dart
/-!
# Compile a layer. Every sector-lift under budget.
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
variable {I W:Type} {N:I→ Side}{φ:Filter I}{Z:I→ℝ}{p q z:Forge G N}
variable {M:I→ℕ}(A:Audience φ Z N M r) (s:Phase)
variable {K:Sponsor G}{T:Seasons K}{τ:Phase→ℕ}
variable {v:I→ℝ}(V:(j:I)→ Alps K T i (v j)) (P T₀: GlyphQ G N) {P₁: ChartRatio G}
variable (hp:4 ≤ i)(hr:LocalRatio P₁)(hs:G.Simple)(hV:0 ≤ v)(R:Patch)(a:Axis)
variable (h: Hand V φ Z τ d l)
variable (Z₁:∀ i,Board (N i) (r+1))
set_option quotPrecheck false
local notation "B'"=>fun i:I=>bark (M i)
local notation "E'"=> fun i:I=>leash r (M i)
local notation "I!"=>↥(fieldP r)
open Shroud
section
variable (T':I→Law (Chamber G r))(S:Shroud A P T₀ T') (u:GlyphQ G N)(hd: Filμ (fun i=>bark (M i)) φ Z u (k+1))(hz:∀ᶠ i in φ,LevelA (tor (N i)) (u i))
include A S h hd hz
lemma appoint (q:↥(fieldP r))(hv:k+1≤d+s.val):∃ (f:I→solar G d τ)(Y:CrysP N G), let e:= Flan q.val P T₀ Y k; ShineX A Y k q ∧ Crier A V P T₀ hp hr hs hV R a l f (LiftA s e) ∧ ∀ᶠ i in φ,∀ j:G.ColorIndex, jet ((Phone G).coord j ∘ Y i) k=(fun x=> (Phone G).coord j (scion P T' u k i Z₁ x q)):=by
       have he:=shard A P T₀ T' u k Z₁ S hd hz q; exact legion A V P T₀ hp hr hs hV R a h (fun i x=>scion P T' u k i Z₁ x q) q he.2 he.1 _ hv
omit h
lemma promise :∃ E:Forge G N,EarthX (fun i=>leash r (M i)) φ Z E (k+1)∧∀ᶠ i in φ, eyeR E 0 i=exP P T' u k i Z₁ ∧ eyeR E 0 i=Claw.rank (eyeR E 0 i) (k+1):=by
       let U(i):=exP P T' u k i Z₁; have hx:=Shroud.rump A P T₀ T' u k Z₁ S hd hz; have hp:Filμ (fun i=>leash r (M i)) φ Z U (k+1):= ⟨hx.mono fun i hi=>hi.1,hx.mono fun i hi=> Tall.tag le_rfl hi.2.1,Shroud.extRate A P T₀ T' u k Z₁ S hd⟩; obtain ⟨z,hz,he,h⟩:= PorchE A U hp (hx.mono fun i hi=>hi.2)
       exact ⟨z,⟨hz,he⟩,(hx.and h).mono fun i hi=> ⟨hi.2,(hi.2.trans hi.1.2.1).trans (congr_arg (fun x=> Claw.rank x _) hi.2.symm)⟩⟩
omit hd hz
lemma hollow (Y:↥(fieldP r)→ CrysP N G) (hv:∀ q:↥(fieldP r), ShineX A (Y q) k q)
       (ht:∀ q:↥(fieldP r), ∀ᶠ i in φ,∀ j:G.ColorIndex, jet ((Phone G).coord j ∘ Y q i) k=(fun x=> (Phone G).coord j (scion P T' u k i Z₁ x q))):
       let Q:=∑ i:↥(fieldP r), LiftA s (Flan i.val P T₀ (Y i) k); ∀ᶠ i in φ, Claw.rank (eyeR Q s i) (k+1)=Claw.rank (u i) (k+1)-exP P T' u k i Z₁:=by
       intro Q; let F(i:↥(fieldP r)):= Flan i.val P T₀ (Y i) k; have he(S:Finset (↥(fieldP r))): eyeR (∑ i∈S, LiftA s (F i)) s=∑ i∈S,eyeR (F i) 0:=by rw[eye_sum]; exact sum_congr rfl (fun i _=>fling ..)
       filter_upwards [S.calm, eventually_all.mpr (fun i=>(hv i).march), eventually_all.mpr ht] with i hp hj h; rw [show eyeR Q s=_ from he univ]; funext x; rw [Finset.sum_apply]; apply Eq.trans ?_ (corona (Z₁ i) (P i) (T₀ i) (T' i) (u i) hp.1.sm (fun j=>Y j i) (fun i=> (hj i).1.smooth) h x); congr 1; funext j; rw [Finset.sum_apply]; exact (seqSum (univ:Finset (↥(fieldP r))) (fun q=>F q i j) 0).symm -- motive
end
end YM.OPE.Merchant
