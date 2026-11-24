import YM.OPE.Compatible.Song.Door
/-!
# Customer exercise. WageK
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
variable {K:Sponsor G}{T:Seasons K}{τ:Phase→ℕ}
variable {M:I→ℕ}(A:Audience φ Z N M r)
variable {v:I→ℝ}(V:(j:I)→ Alps K T i (v j)) (P T₀: GlyphQ G N) {P₁: ChartRatio G}
set_option quotPrecheck false
-- raw wages blueprint
variable (hp:4 ≤ i)(hr:LocalRatio P₁)(hs:G.Simple)(hV:0 ≤ v)(R:Patch)(a:Axis)
structure Hand (V:(j:I)→ Alps K T i (v j)) (φ:Filter I)(Z:I→ℝ)(τ:Phase→ℕ) (d l:ℕ) :Prop where
       treasury : ∃ q:Clip,∀ i,(V i).clip=q
       score : RateLE φ Z v 0
       toll : Antitone τ
       beam (s b:Phase): StencilTax (d+s.val) (l+l+1) ≤ τ b
variable (h: Hand V φ Z τ d l)
local notation "B'"=>fun i:I=>bark (M i)
variable (Y:CrysP N G) (e:↥(fieldP r))(hy: ∀ᶠ i in φ, FirmR (bark (M i)) (Y i) k)(ht:Bills φ Z Y) (s:Phase)(hA:k+1≤d+s.val)
include hy ht h hA
open Quit.Jac
lemma legion :∃ (f:I→solar G d τ) (Vh:CrysP N G), let y:= Flan e.val P T₀ Vh k; ShineX A Vh k e∧ Crier A V P T₀ hp hr hs hV R a l f (LiftA s y) ∧∀ᶠ i in φ,∀ u:G.ColorIndex, jet ((Phone G).coord u ∘ Vh i) k=(Phone G).coord u∘ Y i :=by
       obtain ⟨W,H,hpW,hR⟩:= launch A Y hy ht e
       let B (i:I):=bark (M i); let p(i:I): ↥(B i)→RootEdge:=fun j=>j.val; let T (i:I):= BlurD G (B i) (N i); let Vh(i:I):= W i ∘ T i; obtain ⟨q,hq⟩:=h.treasury; have hθ:∀ j,StencilTax (d+s.val) (l+l+1) ≤ τ j:= h.beam s
       let hD:Arid Z φ p:= aridK (p:=fun i:I=>Lattice.box (M i)) (fun i↦ Finset.Subset.refl _) A.fair A.cash -- fix args
       obtain ⟨P',hH,hT⟩:= issuer hr hp hs R V p W e hpW A.fair h.score hD H hq hV s a hA hθ (Nat.lt_succ_self (l+l)) h.toll
       have hp:∀ i, Anti (N i) e (p i):=fun i=>AntiB (fun _ h=>h) (A.room i).board e.val (surf (A.room i).wide (mem_sdiff.mp e.property).1)
       have he:ShineX A Vh k e:= by
           refine ⟨Eventually.of_forall fun j=> ⟨(hpW j).tilt_i _ _,(hpW j).clock _ _⟩,fun u=>pool_h (fun i=>(Phone G).coord u ∘ W i) k (H u) ?_⟩; exact Eventually.of_forall fun i=> ((Phone G).coord u).toContinuousLinearMap.contDiff.contDiffAt.comp _ (hpW i).sm
       refine ⟨P',Vh, he, ⟨?_,hH⟩,hR⟩; let f:=LiftA s (Flan e.val P T₀ Vh k); apply (WageK.piece Vh k e s he|>.cong (y:=f)); refine Eventually.of_forall fun i=>⟨funext fun j=>(hT i (N i) (hp i) 0 j).symm,rfl⟩
end YM.OPE.Merchant
