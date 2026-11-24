import YM.MS.SpaceOut.High
/-!
# Elongation estimate. A line downclocked while momenta outside central shrink. νpower exponents here nonnegative.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.SpaceOut
open Set Function Filter Finset Metric MeasureTheory Real High
open Koszul Plane Landau Detect Tone Momentum Heat Osc Fiddle Osc.Snap Native Lattice City Latch Job Belt Rake Flux Wire Book Convolve Orbit
open Vista
open scoped Topology ContDiff Interval
variable {I E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][ NormedSpace ℝ F] {S T:Scale I}
 {f:I→ E→ F}{D Z:I→Set E}{n: ℤ}{s t:I→ℝ}
variable (h:∀ i, S.length i ≤ T.length i)
include h
omit [ NormedSpace ℝ E] in
lemma κSize (i:I)(x:E) : S.weight i x ≤ T.weight i x:=by unfold Scale.weight; gcongr; exact h i
omit [NormedSpace ℝ E] in
lemma fare (v b:ℕ)(x:E)(i:I)(hp:T.length i ≤ 2*T.weight i x*S.length i): T.length i^v / T.weight i x^( b+(v+1)) ≤ (2:ℝ)^(v+1)*( S.length i^v/S.weight i x^b*(S.length i/T.length i)) := by
    let X:= T.length i; let V:=S.length i; let Z:= T.weight i x; let B:= S.weight i x; have he: X>0:=T.pos i; have hX:V>0:=S.pos i; have hV:Z>0:= T.weight_pos i x; have hm:B>0:= S.weight_pos i x; obtain hh := pow_le_pow_left₀ he.le hp (v+1); have hB: B≤Z:=κSize h i x; have hG: X^(v+1)*B^b≤ (2:ℝ)^(v+1)*Z^(b+(v+1))* V^(v+1):= by apply le_trans (b:=(2*T.weight i x * S.length i)^(v+1)* Z^b) ( mul_le_mul hh (pow_le_pow_left₀ hm.le hB b) (by positivity) ( show 0≤( 2*Z*V ) ^(v+1) from by positivity) ); unfold V Z; rw [pow_add]; ring_nf; rfl
    change _≤ (2:ℝ)^(v+1) * ( V ^ v / B ^ b * (V / X) ); change X ^ v / Z ^ ( b+(v+1) ) ≤ _; rw [ div_mul_div_comm, ← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity) ]; calc
       _ = X^(v+1)*B^b:= by ring
       _ ≤ _:= hG
       _ = _:= by ring
lemma clock_mesh (n:ℕ)(hx:∀ i x,x∈D i→ T.length i ≤ 2*T.weight i x*S.length i)(hf:Line T Z f (fun i=> T.length i^n))(hp:∀ i,D i ⊆ Z i)(hv:∀ i,T.basic i=S.basic i) : Line S D f ( fun i=> S.length i^n * ( S.length i/T.length i ) ):= by
    intro b; refine ⟨ (hf b).smooth,fun j=>?_⟩; let y:= n+j+1; obtain ⟨C,hC,w,hW⟩:= (hf (b+y)).quoted j; refine ⟨ C*(2^y),by positivity,w,fun i x hP=>(hW i x ((hp i) hP)).trans ?_⟩; simp only [ Scale.strict,hv ]; obtain hh:= fare h (n+j) b x i ( hx i x hP ); rw [ mul_right_comm C (2^y:ℝ),mul_assoc ( C*_ ) ]; apply mul_le_mul_of_nonneg_left _ (by have ht:=S.basic_pos i; positivity ); calc
       _ = _:= ?e
       _ ≤ _:=hh
       _ = _:= ?y
    all_goals unfold y; rw [pow_add _ n j]; ring
-- t-bit.G.Basis.ΣBeam.
end YM.MS.SpaceOut
