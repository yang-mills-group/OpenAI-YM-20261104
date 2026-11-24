import YM.MS.Vista.Terrain
/-!
# Difference identities static. telescope. use convergence at compact full w.H fill optics.Flint
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Vista
open Set Filter Function Finset Metric MeasureTheory Real High
open Koszul Plane Landau Detect Tone Momentum Heat Osc Fiddle Osc.Snap Native Lattice City Latch Job Belt Rake Flux Wire Book Convolve Orbit
open Rake.Geo
open scoped Topology ContDiff Interval
variable {I E:Type}{G:Gauge}{P:Scale I}{K:I→ Latch.Edge G}{X Y F H:I→ Law G}{x:I→ℝ}{v:I→Cover}{μ ν:I→Measure QP}
variable (p:Bool)(b A:I→Cover) {q:I}
-- actual ∫ subtraction on compact rather than unfolded.Integrability explicit.
variable [∀ i, IsFiniteMeasure (μ i)](h:∀ i,Cour (μ i)) (hp:Fund P K x)(hF:Visible X)(he: Visible Y)
include h hp he hF
lemma part_cut (p:Bool) : pClock μ p b K ( X-Y )= pClock μ p b K X-pClock μ p b K Y := by
    funext i w; unfold pClock Θ_pc; simp only [Pi.sub_apply]; simp_rw [mul_sub, Finset.sum_sub_distrib, mul_sub ]; exact integral_sub ( cafe (μ i) (h i) ( (mint_pc (A:=b) hp hF p i w).2.continuous ) ) ( cafe (μ i) (h i) ((mint_pc (A:=b) hp he p i w).2.continuous))
lemma wind_qu (hK:Visible H) : Window p b A μ K (X-Y) H=Window p b A μ K X H-Window p b A μ K Y H:= by
    funext i t; unfold Window PairV; let T:= allocate ( field parity ) t (R:=ℂ); change T _= T _-T _; rw [ ← map_sub ]; apply congr_arg T; funext x y; have hx (j k:BH G)(F:I→Law G)(hf: Visible F):= cafe (μ i) ( h i ) ( ( h_toned hp hf hK p i j k x y ( A i ) ).continuous ); simp only [ Pi.sub_apply,← mul_sub, ← Finset.sum_sub_distrib ]; refine congr_arg ( ( be ( b i ) (net x ))* · ) ( Finset.sum_congr rfl fun j _=> Finset.sum_congr rfl fun k _=> ?_ ); unfold viν; simp_rw [Pi.sub_apply,mul_sub,sub_mul,mul_sub]; exact integral_sub (hx j k X hF) (hx j k Y he)
lemma wind_r (hK:Visible H) : Window p b A μ K H ( X-Y )=Window p b A μ K H X- Window p b A μ K H Y:= by funext i t; unfold Window PairV; let T:= allocate (field parity) t ( R:=ℂ ); change T _= T _-T _; rw [ ← map_sub ]; apply congr_arg T; funext x y; have hx (j k:BH G)(F:I→Law G)(hf: Visible F):= cafe (μ i) (h i) ( (h_toned hp hK hf p i j k x y (A i)).continuous ); simp only [Pi.sub_apply, ← mul_sub,← Finset.sum_sub_distrib]; refine congr_arg (( be (b i) (net x))* · ) ( Finset.sum_congr rfl fun j _=> Finset.sum_congr rfl fun k _=> ?_ ); unfold viν; simp_rw [Pi.sub_apply,mul_sub]; exact integral_sub (hx j k X hF) ( hx j k Y he ) -- types
-- warm difference
omit h hp [∀ i,IsFiniteMeasure (μ i)] in
lemma visible_sub : Visible ( X-Y ) := by
   refine ⟨ fun i x y H=> ?_, fun i E _ _ f v hx ht=>(hF.2 i E f v hx ht).sub ( he.2 i E f v hx ht ) ⟩; simp_rw [ Pi.sub_apply,hF.1 i x y H, he.1 i x y H ]
lemma carry₂ (hc:Visible F)(hJ: Visible H): Window p b A μ K X F- Window p b A ν K Y H= Window p b A μ K (X-Y) F+ Window p b A μ K Y ( F-H )+( Window p b A μ K Y H-Window p b A ν K Y H ):= by rw [ wind_qu p _ _ h hp hF he hc, wind_r p _ _ h hp hc hJ he ]; abel
omit hp h hF he [∀ i,IsFiniteMeasure (μ i)]
-- B/H tree identities. no measure.S
abbrev Motor (K:I→ Latch.Edge G) (F H:I→Law G)(i:I):=tree parity ( K i ) (F i) (H i)
lemma stepwise : Motor K X Y- Motor K F H= Motor K ( X-F ) H+ Motor K X ( Y-H ):= by
    funext i; let U:= boulevard parity ( K i ); change U (X i) (Y i)-U ( F i ) ( H i )= U ( X i- F i ) ( H i ) + U ( X i ) ( Y i-H i ); rw [map_sub U,LinearMap.sub_apply,map_sub ]; abel
end YM.MS.Vista
