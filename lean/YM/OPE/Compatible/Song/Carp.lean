import YM.OPE.Compatible.Song.Plate
/-!
# Exact PT Orientation shadow algorithm. Reassemble true winding materials.
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
namespace SeedB
variable {A V P T₀ hp hr hs hV R a}
lemma Advent {f g:I→solar G d τ}{v w x y:Forge G N}(h:SeedB A V P T₀ hp hr hs hV R a (l:=l) f v x)(hB:SeedB A V P T₀ hp hr hs hV R a (l:=l) g w y): SeedB A V P T₀ hp hr hs hV R a (l:=l) (f+g) (v+w) (x+y):= ⟨Crier.leanB h.manned hB.manned,h.planet.height A.fair hB.planet, h.fieldC.height A.fair hB.fieldC⟩
lemma remain {f:I→solar G d τ}{v w: Forge G N}(h:SeedB A V P T₀ hp hr hs hV R a (l:=l) f v w)(he: EarthX (B') φ Z p d): EarthX (B') φ Z (p-v-w) d:= (he.shift A.fair h.planet).shift A.fair (h.fieldC.further fun _=>cure ..)
end SeedB
include S h
section
local notation "ΔX"=> SeedB A V P T₀ hp hr hs hV R a (l:=l)
lemma deeper (ht:FixP (B') φ Z p d s k)(hk:k ≤ d+s.val):∃ (T:I→solar G d τ) (F G':Forge G N), SeedB A V P T₀ hp hr hs hV R a (l:=l) T F G'∧ gapV (p-F-G') (s.val+1) φ:=by
       induction k generalizing p with
       | zero=> obtain ⟨z,hz,-,hv⟩:= levelH A s ht.1 ht.2.1 ht.2.2; exact ⟨0,0,z,⟨Crier.zeroP,EarthX.birth0 A.fair, hz⟩,by rw [sub_zero]; exact hv⟩
       | succ k ih=>
             obtain ⟨q,y,w,hX,ht⟩:= rebate A s V P T₀ hp hr hs hV R a h S ht hk; obtain ⟨g,F,Gn,H,Y⟩:= ih ht (by omega); exact ⟨q+g,y+F,w+Gn,hX.Advent H,by rw [show p-(y+F)-(w+Gn)=p-y-w-F-Gn by abel]; exact Y⟩
lemma riseMore (hx:EarthX (B') φ Z p d)(hK:gapV p s.val φ): ∃ (T:I→solar G d τ) (F G':Forge G N), SeedB A V P T₀ hp hr hs hV R a (l:=l) T F G'∧ gapV (p-F-G') (s.val+1) φ:=
        deeper A s V P T₀ hp hr hs hV R a h S ⟨hx,hK,hx.pay.roll _⟩ le_rfl
-- complete body Η retinal transaction. h generators Κτ independent
lemma transfixed (hx:EarthX (B') φ Z p d):∃ (T:I→solar G d τ) (F G':Forge G N), SeedB A V P T₀ hp hr hs hV R a (l:=l) T F G'∧∀ᶠ i in φ,p i-F i=G' i:=by
        obtain ⟨p0,f0,g0,H0,h0⟩:= riseMore A 0 V P T₀ hp hr hs hV R a h S hx (fun j hj=>False.elim (Nat.not_lt_zero _ hj)); obtain ⟨p1,f1,g1,H1,h1⟩:= riseMore A 1 V P T₀ hp hr hs hV R a h S (H0.remain hx) h0; obtain ⟨p2,f2,g2,H2,h2⟩:= riseMore A 2 V P T₀ hp hr hs hV R a h S (H1.remain (H0.remain hx)) h1
        refine ⟨p0+p1+p2,f0+f1+f2,g0+g1+g2,(H0.Advent H1).Advent H2,(gapV.null h2).mono fun i hi=>?_⟩; apply sub_eq_zero.mp; change p i-f0 i-g0 i-f1 i-g1 i-f2 i-g2 i=0 at hi; simp only[Pi.add_apply] at *; exact (show _= _ by abel).trans hi
end
end YM.OPE.Merchant
