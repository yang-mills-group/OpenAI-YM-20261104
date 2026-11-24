import YM.MS.ScaleForest.Tally
/-!
# Common germ transfers, IR limit and its uniform remainder

Keep a shared z-aperture over all times. So can transfer integral
identities using data only on such an eventual aperture/disk.
`Frontier`: uniform (m test arbitrarily fixed) analytic control through
the ultimate IR cutoff removal. We compute Laurent and finite coefficients
at retained cutoff and in the stated order of limits, but also account for
this analytic region and convergence off contact, which can be used e.g. to
establish log-coefficient tests. `Frontier` applies also to weighted pieces
(compensated for their poles), or unweighted forest sums after subtraction.
We
use this on the analytic programs of the germ. We won't infer estimates
on raw reps with junk at the origin from these theorems.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.ScaleForest
open Set Filter MeasureTheory Real Function
open Plane Koszul Heat Flux Landau Arts Arc Spin Pilot Wire Rock Path Oceans Plum Alps Garment Color Book Convolve Signal Shine Hem Mell Pearl Train Dock Garment.Wick Garment.Wave GraphSum
open Detect Tone Momentum Osc Fiddle Metric
open scoped Topology ContDiff
variable {G : Gauge} {I J : Type} [TopologicalSpace I] {X Y : Curtain G I} {R T a b : ℝ} {p : ℤ}

abbrev AtIris (F Y : Curtain G I) := F=ᶠ[𝓝 0] Y
omit [TopologicalSpace I] in
theorem Birth (hR:Enough R) (ht:AtIris X Y) : ∃ r:ℝ, r≤R ∧ Enough r ∧ EqOn X Y (disc r) := by
   obtain ⟨T,hT,hV⟩:= Metric.mem_nhds_iff.mp ht; exact ⟨ min R T, min_le_left .., enough_le hR (lt_min hR.1 hT) (min_le_left ..), fun i hi=> hV (Metric.ball_subset_ball (min_le_right ..) hi)⟩
omit [TopologicalSpace I] in
theorem sway_at_full (he : EqOn X Y (disc R))(hv:Envelope R a b X) : Envelope R a b Y := by
   intro J q s v; unfold OnTest; simp_rw [fun i=> (he (q i).property).symm]; exact hv J q s v

theorem fullWaves (he : EqOn X Y (disc R))(hv: Waves R p X): Waves R p Y := by
   constructor; · unfold probe; simp_rw [show ∀ i : Atlas I R, Y i.1.val=X i.1.val from fun i=> (he i.1.property).symm]; exact hv.sway
   · intro t i; exact (hv.hol t i).con isOpen_ball (fun z hz=> congr_fun (congr_fun (he hz) t) i)
   all_goals intro z hz; rw [← he hz]; first|exact hv.funds z hz|exact hv.token z hz

theorem Paces.congr (h : Paces X p)(ht:AtIris X Y): Paces Y p := by
   intro b hb hp; obtain ⟨R,hR,hT,a,hX⟩:= h b hb hp; obtain ⟨u,hu,hU,he⟩:= Birth hR ht; exact ⟨ u,hU,fullWaves he (hT.shrink hu), a,sway_at_full he (hX.shrink hu)⟩
theorem Crossing.congr (h:Crossing X p)(ht:AtIris X Y): Crossing Y p:= by
   intro b hb hp; obtain ⟨R,hR,hT,hX⟩:= h b hb hp; obtain ⟨u,hu,hU,he⟩:= Birth hR ht; exact ⟨ u,hU,fullWaves he (hT.shrink hu),fun i=> sway_at_full he ((hX i).shrink hu)⟩
theorem MultiFuel.congr (h:MultiFuel X p)(ht:AtIris X Y): MultiFuel Y p:= by
   intro b hb hp; obtain ⟨R,hR,hT,hX⟩:= h b hb hp; obtain ⟨u,hu,hU,he⟩:= Birth hR ht; exact ⟨ u,hU,fullWaves he (hT.shrink hu),fun i=> sway_at_full he ((hX i).shrink hu)⟩

omit [TopologicalSpace I] in
theorem decider (he : Iris X Y) (hp : X 0=Y 0): AtIris X Y:= by
   obtain ⟨R,hR,hV⟩:= dotty_mem.mp he; refine ( Metric.mem_nhds_iff.mpr ⟨ R,hR,?_⟩ ); intro i hi; rcases eq_or_ne i 0 with hi'|hi'; subst i; exact hp; exact hV _ hi hi'

theorem colonize (hv : Waves R p X) (hR : Enough R) (he : Iris X Y) : AtIris X (populated Y) := by
   refine decider (EventuallyEq.trans he (EventuallyEq.symm (popTie Y))) ?_; funext s x; rw [popAt]; exact chosen (n:=0) (Lift.congr (Lift.trim (hv.hol s x) hR.1) (Eventually.mono he (fun i hi=> congr_fun (congr_fun hi _) _)))

structure Fringe (F:Curtain G I) (R a:ℝ) : Prop where
   story m : ∃ H:ℂ→I→ℂ, (∀ i,Forest (disc R) (fun z=>H z i))∧ Continuous (fun p:↥(disc R) × I=> H p.1 p.2)∧
      ∃ C:ℝ,0<C∧∀ (z:ℂ),z∈disc R→∀ (i:I) (s:ℝ),0≤s→ ‖F z s i m []-H z i‖ ≤ C*exp (-a*s)

def Frontier (F:Curtain G I) : Prop:= ∀ b:ℝ,0<b→ b<1→∃R:ℝ,Enough R∧ Fringe F R b
lemma Fringe.shrink (h : Fringe X R b)(ht:T≤R) : Fringe X T b where
   story m:= by
      obtain ⟨H,hH,hP,C,hC,hL⟩:=h.story m; let S:=Metric.ball_subset_ball (x:=(0:ℂ)) ht; exact ⟨ H,fun i z hz=>hH i z (S hz),hP.comp (f:=fun p:disc T×I=> ( (⟨ p.1.val,S p.1.property⟩:disc R), p.2 )) (by fun_prop), C,hC, fun z hz=> hL z (S hz)⟩
theorem Fringe.congr (h : Fringe X R b) (he : EqOn X Y (disc R)): Fringe Y R b where
   story m:= by obtain ⟨H,hH,hP,C,hC,hL⟩:= h.story m; exact ⟨ H,hH,hP,C,hC,fun i hi s t hh=>by rw [← he hi]; exact hL i hi s t hh⟩

theorem Frontier.congr (h: Frontier X) (he:AtIris X Y) : Frontier Y := by
   intro b hb hp; obtain ⟨R,hR,hT⟩:= h b hb hp; obtain ⟨u,hu,hU,hv⟩:= Birth hR he; exact ⟨ u,hU,(hT.shrink hu).congr hv⟩

theorem Frontier.drivePast [FirstCountableTopology I](hx: Crossing X p) : Frontier (vertical X) := by
   intro b hb hp; obtain ⟨R,hR,hX,hP⟩:= hx b hb hp; refine ⟨ R,hR,⟨fun m=>?_⟩⟩; obtain ht:= hP 1; obtain ⟨C,hC,hV⟩:= breath m hX ht zero_lt_one hb; exact ⟨ bottomLine X m, breathes m hX ht zero_lt_one hb,line_cont m hX ht zero_lt_one hb,C,hC,fun z hz i s he=>by rw [norm_sub_rev]; exact hV i (⟨ z,hz⟩:disc R) s he⟩

/-- its limUnder vs eventual equality at z, proof via uniform estimate -/
def WindowIR (F:Curtain G I) (m:ℕ) (z:ℂ) (i:I):= limUnder atTop fun s:ℝ=> F z s i m []
lemma Frontier.enter {X:Curtain G I} (h: Fringe X R b) (hp:0<b) (m:ℕ) :
    (∀ i, Forest (disc R) (fun z=> WindowIR X m z i))∧ Continuous (fun z:disc R × I=> WindowIR X m z.1 z.2) ∧
    (∃ C:ℝ,0<C∧∀ z∈disc R,∀ i s, 0≤s→ ‖X z s i m []-WindowIR X m z i‖≤C*exp (-b*s)) ∧
    (∀ z∈disc R,∀ i, Tendsto (fun t:ℝ=> X z t i m []) atTop (𝓝 (WindowIR X m z i))) := by
   obtain ⟨H,hH,hP,C,hC,hQ⟩:= h.story m; have hu (z:ℂ)(hz:z∈disc R)(i:I): Tendsto (fun t:ℝ=> X z t i m []) atTop (𝓝 (H z i)):= by
      have hx : Tendsto (fun t:ℝ=> C*exp (-b*t)) atTop (𝓝 0):= by simpa only [id,mul_zero, Function.comp_apply] using (tendsto_exp_atBot.comp (Tendsto.const_mul_atTop_of_neg (neg_lt_zero.mpr hp) tendsto_id)).const_mul C
      exact tendsto_iff_dist_tendsto_zero.mpr (squeeze_zero' (Eventually.of_forall fun t=> dist_nonneg) (by filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht; rw [dist_eq_norm]; exact hQ _ hz _ t ht) hx)
   have hM z (hz:z∈disc R)(i:I) : WindowIR X m z i= H z i:= (hu z hz i).limUnder_eq; refine ⟨fun i z hz=>?_,by simp_rw [hM _ (Subtype.property ..)]; exact hP, ⟨ C,hC,fun z hz i s he=>by rw [hM z hz]; exact hQ z hz i s he⟩, fun z hz i=> by rw [hM z hz]; exact hu z hz i⟩
   refine DifferentiableAt.congr_of_eventuallyEq (hH i z hz) ?_; filter_upwards [isOpen_ball.mem_nhds hz] with q hq; exact hM q hq i
end YM.MS.ScaleForest
