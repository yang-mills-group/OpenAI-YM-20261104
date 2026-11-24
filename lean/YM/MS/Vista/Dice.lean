import YM.MS.Vista.Rough
/-!
# λ-weight transfers when a nonzero corner is bounded away from low-
 legs. Strict extension uses another lift to reach exact bulk conservation. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Vista
open Set Function Filter Finset Metric MeasureTheory Real High
open Koszul Plane Landau Detect Tone Momentum Heat Osc Fiddle Osc.Snap Native Lattice City Latch Job Belt Rake Flux Wire Book Convolve Orbit
open scoped Topology ContDiff Interval
variable {I E F G:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
 [NormedAddCommGroup G][NormedSpace ℝ G]{D:I→Set E}{L:E→L[ℝ] F}{p:F}{S:Scale I}{U:I→Scale I}
 {u:I→F→G}{t:I→ℝ}{q:Orbit.Half}
-- translations.On Full.Cases.Any.
lemma S_late (P:E→L[ℝ] F)(x:F) (h:∀ i,1≤ S.length i)(hf:Bound S u t): Costs (wideCost S D S.length h) S (fun i p=>u i (P p+x)) (fun i _=> t i):= by
    apply tilted _ _ (P:=S.full) hf (fun i x h=>trivial); refine ⟨1+‖P‖+‖x‖,by positivity,1,fun i v hx=>?_⟩; let K:= 1+‖P‖; obtain ht:= S.basic_pos i; obtain hL:= h i; obtain he:= S.pos i; have hz:1 ≤ S.weight i v:= S.one_le_weight ..; simp only [pow_one,mul_one,Scale.full]; apply le_of_sub_nonneg; let A:= S.basic i; let X:= S.length i; let W:= S.weight i v; have hp : S.weight i (P v+x) ≤ K*W+ X*‖x‖:= by
        refine le_trans ?_ ( add_le_add_left ( S.weight_L P i v ) _); unfold Scale.weight X; apply le_trans ( add_le_add_right (mul_le_mul_of_nonneg_left (norm_add_le (P v) x) he.le) _ ); rw [mul_add,add_assoc] -- add_le uses arg positions
    have HH : S.weight i (P v+x) ≤ X * ((K+‖x‖)*W):= le_trans hp (by
        have hh : 1 ≤ W:= hz; have hu:0≤ X * ‖x‖:=mul_nonneg he.le (norm_nonneg _); have hm:0≤K*W:=(by unfold K; positivity); rw [add_mul K ‖x‖, mul_add X]; apply add_le_add (le_mul_of_one_le_left hm hL); rw [ ← mul_assoc ]; exact le_mul_of_one_le_right hu hh)
    exact sub_nonneg.mpr ( ( mul_le_mul_of_nonneg_left HH ht.le ).trans_eq (by unfold K X W; ring)) -- syntax
lemma S_front (P:E→L[ℝ] F)(x:F)(r:ℝ)(hr: 0<r)(hm:∀ i p,p∈D i→ r≤‖p‖)(hf:Bound S u t): Costs ( Slice S D ) S (fun i p=>u i (P p+x)) (fun i _=> t i):= by
    apply tilted _ _ (P:=S.full) hf (fun i x h=> trivial); let M:= ‖P‖ + ‖x‖ / r; have hM:0≤M:=add_nonneg (norm_nonneg _) (by positivity); refine ⟨1+M,by linarith,1, fun i v ht=>?_⟩; obtain hs:= hm i v ht; obtain hB:= S.basic_pos i; obtain hL:= S.pos i; simp only [pow_one,mul_one,Slice,Scale.full]; rw [mul_left_comm (1+M)]; gcongr; unfold Scale.weight;
    have hc : ‖P v +x‖ ≤ M * ‖v‖:= by
       unfold M; rw [add_mul]; apply le_trans (norm_add_le ..); apply add_le_add ( P.le_opNorm _ ); apply le_trans _ (mul_le_mul_of_nonneg_left hs (div_nonneg (norm_nonneg _) hr.le)); rw [ div_mul_cancel₀ _ hr.ne' ]
    nlinarith [ norm_nonneg v ]
-- near-corner.At root shift forced lift.
lemma corner_act (p:Orbit.Half)(i:Axis): Lattice.lift p i=0 ∨ Lattice.lift p i=1:= by obtain ⟨h,hh⟩:= lift_centers p i; rw [ k_val ] at *; omega
lemma corner_norm (hp:q≠0): ‖Coord q‖=π:= by
    have hv (i:Axis): Coord q i=π*(Lattice.lift q i:ℝ):= by rw [Coord,wrapZ,η_walk,at_whole,ψstep,k_val,tier]; push_cast; ring
    apply le_antisymm
    · refine (pi_norm_le_iff_of_nonneg Real.pi_pos.le).mpr fun i=>?_ ; rcases corner_act q i with h|h <;> simp [hv,h,abs_of_nonneg Real.pi_pos.le]; linarith [Real.pi_pos]
    have hh : ∃ i:Axis,Lattice.lift q i≠0:= by contrapose! hp; rw [← wrap_lift q, (show Lattice.lift q=0 from funext hp ),map_zero]
    obtain ⟨i,h⟩:= hh; obtain ht:= norm_le_pi_norm ( Coord q ) i; rw [hv,show Lattice.lift q i=1 from (corner_act q i).resolve_left h] at ht; simpa [abs_of_nonneg Real.pi_pos.le] using ht -- norm_of
abbrev cave (r:ℝ) (_:I): Set E:= Metric.closedBall 0 r
abbrev ahead (r:ℝ)(_:I): Set E:= ( Metric.closedBall 0 r )ᶜ
lemma pin_cave (Q:E→L[ℝ] QP)(hp:q≠0): ∃ r:ℝ,0<r ∧ ∀ x:E,x∈Metric.closedBall 0 r → 1≤ ‖Q x+Coord q‖ ∧ ‖Q x+Coord q‖≤ wide := by
    obtain hv:= corner_norm hp; let r:=1/(1+‖Q‖); refine ⟨r,by unfold r; positivity,fun x hx=>?_⟩; have ht : ‖Q x‖≤1:= by refine ( Q.le_opNorm x ).trans ?_; obtain he:= (show ‖x‖≤ r from by simpa using hx); unfold r at he; obtain hz:0 < 1+‖Q‖:=(by positivity); nlinarith [ ( le_div_iff₀ hz ).mp he,norm_nonneg x ]
    obtain hc:= norm_add_le (Q x) (Coord q); have he:= norm_sub_norm_le (Coord q) (Q x+Coord q); rw [ show Coord q - (Q x + Coord q)= -(Q x) from (by abel), norm_neg ] at he; unfold wide; constructor <;> nlinarith [Real.pi_gt_three]
end YM.MS.Vista
