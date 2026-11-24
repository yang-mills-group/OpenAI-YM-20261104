import YM.OPE.Compatible.Song.Heat
/-!
# Compile a layer. Ascending/
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
variable (h: Hand V φ Z τ d l) {T':I→Law (Chamber G r)}(S:Shroud A P T₀ T')
set_option quotPrecheck false
local notation "B'"=>fun i:I=>bark (M i)
local notation "Egn"=> fun i:I=>leash r (M i)
local notation "I!"=>↥(fieldP r)
open Shroud
structure SeedB (T:I→solar G d τ)(U E:Forge G N):Prop where
       manned : Crier A V P T₀ hp hr hs hV R a l T U
       planet : EarthX (fun i=>bark (M i)) φ Z U d
       fieldC : EarthX (fun i=>leash r (M i)) φ Z E d
include S h
section
lemma rebate (hp':FixP (B') φ Z p d s (k+1))(hv:k+1 ≤ d+s.val):∃ (T:I→solar G d τ) (F G':Forge G N), SeedB A V P T₀ hp hr hs hV R a (l:=l) T F G'∧ FixP (B') φ Z (p-F-G') d s k:=by
       let o(i:I):=(A.room i).money; let u:= eyeR p s; obtain ⟨hx,ht,hU⟩:=hp'; let hQ:= hushed _ ht hx.mass
       choose f F he hC he' using fun q:I!=>appoint A s V P T₀ hp hr hs hV R a h o T' S u hU hQ q hv -- arg l?
       let z(j:I!):=Flan j.val P T₀ (F j) k; let Y:=∑ i:I!, LiftA s (z i); let Q:= hollow A s P T₀ o T' S u F he he'; obtain ⟨E,hE,hE'⟩:= promise A P T₀ o T' S u hU hQ; let E₁:=LiftA s E; let Hp:=PeakR (k:=k) A s univ z (fun i hi=> let hY:= PlaneQ.quasar A _ _ _ S _ _ i (he i); EarthX.mk hY.1 hY.2) hv
       let hc:= Crier.totals (A:=A) univ f (fun i=>LiftA s (z i)) (fun i hi=> hC i); have H:EarthX (fun i=>leash r (M i)) φ Z E₁ d:=hE.below A.fair s hv -- notation E₁ conflict
       refine ⟨∑ i,f i,Y,E₁,⟨hc,Hp.1,H⟩, ⟨ ?_ ,(ht.sub Hp.2.1).sub (Pulse E _),?_⟩⟩
       · refine (hx.shift A.fair Hp.1).shift A.fair (H.further fun _=> cure ..)
       apply whirl A.fair hU Hp.2.2; swap; · refine (Q.and hE').mono (fun i hi=>?_ ) ; have hx':Claw.rank (eyeR Y s i) (k+1)=_:=hi.1; rw [hx']; have he: eyeR E₁ s=eyeR E 0:= fling ..; rw[he,← hi.2.2, hi.2.1]; change Claw.rank (u i) _- (Claw.rank (u i) _- _)= _; abel
       rw[show eyeR E₁ s=eyeR E 0 from fling ..]; exact ((hE.further (fun i=> cure r (M i))).pay.roll 0) -- he proof
end
end YM.OPE.Merchant
