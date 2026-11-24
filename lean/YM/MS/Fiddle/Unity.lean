import YM.MS.Fiddle.Pump
/-!
# Global line comparison on smooth folded supports. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Fiddle
open Function Set Filter Finset Metric Real MeasureTheory Momentum Tone Landau Osc Osc.Snap Lattice
open scoped Topology ContDiff
variable {I E:Type}[ NormedAddCommGroup E][NormedSpace ℝ E] {S:Scale I}{F G:I→QP→ℂ}{g a:I→ℝ}
lemma mergeLine (P Q:I→ Set QP) (h:∀ i p,p∈ P i ∨ p∈ Q i)(hx:Line S P F g)(hp: Line S Q F g)(hh:∀ i,0≤ g i) : Line S (fun _=> Set.univ) F g:= by
   intro b; refine ⟨(hx b).smooth,fun j=>?_⟩; obtain ⟨C,hC,k,hk⟩:= (hx b).quoted j; obtain ⟨M,hM,w,hW⟩:=( hp b).quoted j; refine ⟨ C+M,add_pos hC hM,k+w,fun i p ht=>?_⟩; have hK:= S.one_le i; have hS:= S.pos i; have hr:= S.weight_pos i p; specialize hh i; rcases h i p with h1|h1 <;> first|(apply le_trans (hk i p h1)) |apply le_trans (hW i p h1)
   all_goals simp only [Scale.strict]; gcongr; linarith; omega
abbrev Inland (_:I): Set QP:= Metric.ball 0 inner
lemma Hydro (hx: Sharp S a located F G g)(h:∀ i, Veiled ( F i ))(hp:∀ i,1≤ S.length i){k:ℕ}(hk:∀ i,( S.length i^k)⁻¹ ≤ a i): Line S (fun _=> Set.univ) (fun i p=> (aisle p:ℂ)*F i p-G i p ) (fun i=> g i*a i):= by
   let f i p:=(aisle p:ℂ)*F i p; have he := folding hx.lattice h hp; let D (i:I):= (Inland i)ᶜ;
   have hD (i:I)(p:QP)(ht:p∉ Inland i): 1≤‖p‖:= by simp only [Inland, inner, Metric.mem_ball,dist_zero_right, not_lt] at ht; linarith [Real.pi_gt_three]
   have hg:= noPole hx.lattice; have hf := Line.tail he hg hD k; have ht:= Line.tail hx.std hg hD k; refine mergeLine Inland D (fun i p=> em _) ?_ ?_ (fun i=> mul_nonneg (hg i) (( inv_nonneg.mpr ( pow_nonneg (S.pos i|>.le) k) ).trans (hk i))) -- hp
   · intro b; refine ⟨ fun i=>(hf b|>.smooth i).sub (ht b|>.smooth i),fun j=>?_ ⟩; obtain ⟨C,hC,v,hv⟩:= (hx.close b).quoted j; refine ⟨C,hC,v,fun i p hp=>?_⟩; dsimp only;
     have hh : p∈located i:= Metric.mem_closedBall.mpr (by have hu:= Metric.mem_ball.mp (show p∈ Inland i from hp); unfold inner at hu; linarith [Real.pi_pos]); rw [ (Filter.EventuallyEq.iteratedFDeriv ℝ (f₂:=(fun p:QP=> F i p-G i p)) ?_ j).eq_of_nhds ]; exact hv i p hh
     filter_upwards [Metric.isOpen_ball.mem_nhds (show p∈Inland i from hp)] with p hx; rw [door_c (by simpa only [dist_zero_right] using (Metric.mem_ball.mp hx).le)]; simp
   have hle i:g i*(S.length i^k)⁻¹ ≤ g i*a i:= mul_le_mul_of_nonneg_left (hk i) (hg i);
   intro b; exact Costs.sub (hf.monotone hle b) (ht.monotone hle b)
end YM.MS.Fiddle
