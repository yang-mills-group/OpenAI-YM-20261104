import YM.MS.Vista.Meets
/-!
# Localize to fundamental frequency sector through congrQ.Bolt.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.SpaceOut
open Set Function Filter Finset Metric MeasureTheory Real High
open Koszul Plane Landau Detect Tone Momentum Heat Osc Fiddle Osc.Snap Native Lattice City Latch Job Belt Rake Flux Wire Book Convolve Orbit
open Vista
open scoped Topology ContDiff Interval
variable {G:Gauge}{I E:Type} {V:Visa I}{L:I→Side}{K:Planet G I}{p q:QP}{b:Bool}{r:ℝ}
lemma norm_zone (p:QP): p∈firstZone Axis↔‖p‖≤π:= Metric.mem_closedBall.trans (by simp) -- Iff?
lemma live (p:QP): ∃ x:QP, x∈ firstZone Axis∧ congrQ p x:= by
   obtain ⟨k,hk⟩:= allT (p+north); let P:=p+ Tone.rep k; refine ⟨ P,(inside_i _).mpr ?_, congrQ.sym ⟨ k,rfl ⟩⟩; intro i; obtain ⟨h1,h2⟩:= realm hk i; change 0 ≤ p i+π+rep k i at h1; change p i+π+rep k i < 2*π at h2; apply abs_le.mpr; change -π≤ p i+rep k i∧ p i+rep k i ≤ π; constructor <;> linarith
abbrev least (p:QP):= Classical.choose (live p)
lemma handle (p:QP): least p ∈firstZone Axis:= (Classical.choose_spec (live p)).1
lemma use (p:QP): congrQ p (least p) := (Classical.choose_spec (live p)).2
-- include actual lifts
lemma walkSpec (n:Side)(x:Cover): walk n x= ψstep n • embed x:=η_walk n x -- rfl
lemma absstep {n:Side} (x:Lattice.Site n): ‖Coord x‖= ψstep n * pdist x:= by unfold Coord wrapZ; rw [walkSpec,norm_smul_of_nonneg (ψpp ..|>.le), show ‖embed _‖=_ from budget_geom x]
lemma s_size (n:Side): 0 < (n.val:ℝ):= Bloch.side_pos n
lemma entered {n:Side}(x:Lattice.Site n): Coord x ∈ firstZone Axis:= by
    apply ( norm_zone _ ).mpr; rw [absstep]; unfold ψstep; rw [mul_comm,← mul_div_assoc,div_le_iff₀ ( s_size n ) ]; unfold tier; obtain h : 2*(pdist x :ℝ) ≤ n.val:=(by exact_mod_cast sizeX x); nlinarith [Real.pi_pos]
lemma discr {n:Side}(x:Lattice.Site n)(hv:x≠0): 0<pdist x := by contrapose! hv; rw [← wrap_lift x, show Lattice.lift x=0 from ?_,map_zero ]; funext i; obtain h:= component_le x i; change Lattice.lift x i=0; omega
-- sector minimum distance.Structive
lemma loopwalk (h: p≠q)(hx:congrQ p q): tier≤‖p-q‖:= by
    obtain ⟨x,rfl⟩:=hx; rw [add_sub_cancel_left]; obtain hh:x≠0:= by intro e; subst x; simp at h
    obtain ⟨i,hi⟩:= Function.ne_iff.mp hh; apply le_trans _ ( norm_le_pi_norm ( rep x ) i ); change tier≤ ‖tier*(x i:ℝ)‖; rw [norm_mul, norm_of_nonneg rising.le]; apply le_mul_of_one_le_right rising.le; suffices hx: (1:ℝ)≤((x i).natAbs:ℝ) by simpa only [ Nat.cast_natAbs, Int.cast_abs,norm_eq_abs ] using hx
    exact_mod_cast Int.natAbs_pos.mpr hi
-- cut.Support local lift.Guard.
def west (r:ℝ)(x:QP): ℝ:= aisle ( r • x )
def rim (r:ℝ)(x:QP): ℝ:= west r (least x)
lemma west_off (h:0≤r)(hx:wide<r*‖p‖): west r p=0:= by contrapose! hx; simpa [norm_of_nonneg h, norm_smul] using door_n hx
abbrev keyV : ℝ:= 9*π/8
lemma stretchP (hp: p∈firstZone Axis): ‖p‖<keyV:= by apply lt_of_le_of_lt ((norm_zone _).mp hp); unfold keyV; linarith [Real.pi_pos]
lemma far0 (h:2≤r)(hp:‖p‖<keyV)(hQ: p≠q)(hq: congrQ q p) : west r q=0:= by apply west_off (by linarith); obtain hm:= le_trans (loopwalk (Ne.symm hQ) hq) (norm_sub_le q p); unfold keyV at hp; unfold tier at hm; unfold wide; nlinarith [Real.pi_pos]
lemma glue (h:2≤r)(hp:‖p‖<keyV)(hq:‖q‖<keyV)(hV:congrQ p q): west r p=west r q:= by by_cases hv:p=q; exact hv ▸ rfl; rw [ far0 h hq (Ne.symm hv) hV, far0 h hp hv hV.sym ]
lemma rim_Q (h:2≤ r)(hp:‖p‖<keyV): rim r p=west r p:= glue h ( stretchP (handle p)) hp ( ( use p ).sym ) -- parse `use`
lemma rim_per (h:2≤r): pinQ (rim r):= fun {x y} hh=> glue h (stretchP ( handle x )) (stretchP (handle y)) (( (use x ).sym ).trans (hh.trans (use y)))
lemma rim_at (h:2≤r)(hp:p∈firstZone Axis): rim r=ᶠ[𝓝 p] west r:= by filter_upwards [ Metric.isOpen_ball.mem_nhds (show p∈Metric.ball 0 keyV from Metric.mem_ball.mpr (by simpa using stretchP hp)) ] with x hx; exact rim_Q h ( by simpa using hx )
lemma rim_s (h:2≤r): ContDiff ℝ ∞ (rim r):= by
    apply contDiff_iff_contDiffAt.mpr; intro i; obtain ⟨p,v,hv⟩:= live i; obtain ⟨k,hk⟩:=hv; let u (x:QP):=x+rep (-k); have he: u i=p:= by unfold u; rw [hk,map_neg]; abel
    have hm: rim r=(rim r) ∘ u:= funext fun x=> Eq.symm (rim_per h ( p:=u x ) ( q:=x ) ⟨ -k,rfl ⟩ ); rw (occs:=.pos [1]) [hm]; have hx: ContDiffAt ℝ ∞ (rim r) p:= ( door_sm.comp (show ContDiff ℝ ∞ (fun p:QP=> r • p) by fun_prop)|>.contDiffAt.congr_of_eventuallyEq ( rim_at h v )); exact ContDiffAt.comp i (show ContDiffAt ℝ ∞ (rim r) (u i) from he.symm ▸ hx) ( by unfold u; fun_prop ) -- ordering
lemma even_Q (h:2≤r): rim r (-p) = rim r p:= by obtain ⟨x,hx,hV⟩:= live p; rw [ rim_per h hV, rim_per h hV.opp,rim_Q h ( stretchP hx ),rim_Q h (p:=-x) (by rw [norm_neg]; exact stretchP hx) ]; rw [west,smul_neg,aisle_S]; rfl
end YM.MS.SpaceOut
