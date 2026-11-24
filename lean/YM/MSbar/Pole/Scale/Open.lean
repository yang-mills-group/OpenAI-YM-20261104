import YM.MSbar.Pole.Scale.Lucid

/-!
# Meromorphic primitive in a scaling dimension

Interpret dimensionally regulated integration in the scale variable by meromorphic power
integration around the endpoint `0`. Each Taylor term integrates with exact scaling, denominators
are poles BEFORE any projection. Separate proof supplies the differential identity and the rule
when `l=0`, which requires proper endpoint behavior.
-/
noncomputable section
set_option autoImplicit false
namespace YM.MSbar.Pole
open Function Filter Set MeasureTheory Ambient Momentum
open scoped Topology ContDiff BigOperators Classical Interval

-- Explicit degrees include marks and antifields. l free hard momentum integrations;
-- count actual integrations, not the perturbative loop order of meromorphic CT vertices.
structure Age where
  a : ℤ
  l : ℕ
namespace Age
variable (d : Age)
def linear : ℂ := 2*d.l
def alpha (z:ℂ):= (d.a:ℂ)+d.linear*z
/-- fixed Taylor order. -/
def safety:= d.a.natAbs +4
lemma safely : ∀ᶠ z in nhds (0:ℂ), 2≤(d.alpha z).re + d.safety:= by
  have he:= ((Complex.continuous_re.comp (show Continuous d.alpha from by unfold alpha; fun_prop)).add_const (d.safety:ℝ)).tendsto 0
  apply he.eventually (p:=fun x : ℝ=> 2≤x)
  apply le_mem_nhds
  simp only [alpha,mul_zero,add_zero,Complex.intCast_re,comp_apply]
  unfold safety
  have he : (2:ℤ)<d.a+(d.a.natAbs+4:ℕ):= by omega
  have hh := (Int.cast_lt.mpr he : ((2:ℤ):ℝ) < _)
  simpa only [Int.cast_add,Int.cast_ofNat,Int.cast_natCast] using hh

def increment (i:ℕ)(z:ℂ):=d.alpha z+i

/-- The constant zero denominator will be allowed (tree wave only),
with the independent requirement that term vanishes; carry zero in that case. -/
def resonates (i:ℕ) := d.l=0 ∧ d.a+i=0

lemma guards (i:ℕ) :
    ∀ᶠ z in nhdsWithin (0:ℂ) {(0:ℂ)}ᶜ, d.increment i z ≠ 0 ∨ d.resonates i:= by
  by_cases hx : d.a + (i:ℤ)=0
  · by_cases he:d.l=0
    · filter_upwards with z using Or.inr ⟨he,hx⟩
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hp:z≠0:=hz
    left; unfold increment alpha; push_cast at *
    rw [add_right_comm,← show (↑(d.a+(i:ℤ)):ℂ)= d.a+(i:ℂ) by push_cast; rfl,hx]; simp [linear,he,hp]
  have h : Continuous (d.increment i):=by unfold increment alpha; fun_prop
  have hh : (d.increment i) 0 ≠ 0:=by simp only [increment,alpha,mul_zero,add_zero]; exact_mod_cast hx
  apply Filter.Eventually.mono (p:=fun z=>d.increment i z ≠ 0) (mem_nhdsWithin_of_mem_nhds (h.continuousAt.eventually_ne hh)) fun i hi=>Or.inl hi
end Age
namespace Mellin
variable {E A : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]

-- scalar kernel operators don't mix points on different angular slices
lemma spill_chain {F : ℂ→ ℝ × A→ℂ} {G : ℂ→ℝ × E→ℂ} (z:ℂ) (x:A) (y:E) (h : ∀ t,F z (t,x)=G z (t,y)) (k:ℕ) :
    ∀ t,(Ray.spill^[k] F) z (t,x)=(Ray.spill^[k] G) z (t,y):=by
  induction k with
  | zero=> exact h
  | succ k ih=>
      intro t; simp only [iterate_succ_apply']
      change (∫ u:ℝ in Ioc 0 1, deriv (fun s:ℝ=>(Ray.spill^[k] F) z (s,x)) (u*t))=(∫ u:ℝ in Ioc 0 1, deriv (fun s:ℝ=>(Ray.spill^[k] G) z (s,y)) (u*t)); simp_rw [ih]

open Age Ray
variable {I : Type} [Fintype I] (U : Finset I) (d : Age)
def pbody (A : Finset I) (F : ℂ→ Cloud I) (i : ℕ) (z : ℂ) : Cloud I := fun n x => spill^[i] (augments A n F) z (0,x)

def eta (F : ℂ → Cloud I) (i : ℕ) (z : ℂ) : Cloud I:= fun n x=> (d.increment i z)⁻¹ * (pbody U F i z n x)

-- polynomial q^N remainder integration. Choose the exponent region separately.
def room (F : ℂ→ Cloud I) (z : ℂ): Cloud I:=fun n x=>later (spill^[d.safety] (augments U n F)) d.linear ((d.a:ℂ)-1+d.safety) z x

def step (F : ℂ→ Cloud I) : ℂ→ Cloud I := (room U d F)+(∑ i∈Finset.range d.safety, eta U d F i)

variable {F : ℂ→Cloud I} {R:ℝ}
lemma spillSym (z : ℂ) (h : Tensor (F z)) (t : ℝ) (i : ℕ) : Tensor (fun n x => spill^[i] (augments U n F) z (t,x)):=by
  constructor
  · intro n J x
    exact spill_chain z (J ∘ x) x (F:=augments U n F) (G:=augments U n F) (fun b=>by unfold augments; rw [move_turn,h.moves]) i t
  intro n x
  exact spill_chain z (place.pad n ∘ x) x (F:=augments U (n+1) F) (G:=augments U n F) (fun b=>by unfold augments; rw [move_pad,h.agrees]) i t
lemma space (H : Meridian (zone R) F) (hr : ∀ z∈ zone R, 2≤(d.alpha z).re + d.safety): Meridian (zone R) (room U d F):=by
  constructor
  · intro n; refine (carrying Metric.isOpen_ball (terms Metric.isOpen_ball (Momentum.puts H (B:=U) n) d.safety) d.linear ((d.a:ℂ)-1+d.safety) ?_).1
    intro z hz; have hh:=hr z hz; simp only [alpha,Complex.add_re,Complex.sub_re,Complex.intCast_re,Complex.one_re,Complex.natCast_re] at *; linarith
  intro z hz
  constructor
  · intro n J x; unfold room later; refine integral_congr_ae (Eventually.of_forall fun i=>?_); exact congr_arg (· * _) ((spillSym U _ (H.tensor z hz) i d.safety).moves n J x)
  intro n x; unfold room later; exact integral_congr_ae (Eventually.of_forall fun i=>congr_arg (· * _) ((spillSym U _ (H.tensor z hz) i d.safety).agrees n x))
lemma pbody_meridian (i : ℕ)(h : Meridian (zone R) F): Meridian (zone R) (pbody U F i):=by
  refine ⟨fun n => once_at_zero Metric.isOpen_ball (terms Metric.isOpen_ball (Momentum.puts h (B:=U) n) i),fun z hz=>spillSym U z (h.tensor z hz) 0 i⟩ --

private lemma singlePole (i:ℕ) : Vortex 1 (fun z=>fun (n:ℕ) (_:External I n)=> (d.increment i z)⁻¹) := by
  by_cases h:d.a+(i:ℤ)=0
  · have hp (z) : d.increment i z=d.linear*z:=by
      unfold increment alpha; rw [add_right_comm,← show ((d.a+(i:ℤ):ℤ):ℂ) = d.a+(i:ℂ) by push_cast; rfl,h]; simp
    refine ⟨1,(fun (_:ℂ) (n:ℕ) (_:External I n)=>d.linear⁻¹),zero_lt_one,⟨fun n=> ⟨Packet.const _,fun _ _ _=> differentiableAt_const _⟩,fun _ _=>⟨fun _ _ _=>rfl,fun _ _=>rfl⟩⟩,fun z hz _ _=>?_⟩
    have hh:z≠0:=hz.2; change z^1*(d.increment i z)⁻¹ = _; rw [hp,pow_one,mul_inv_rev,mul_inv_cancel_left₀ hh]
  have hc (z : ℂ) : DifferentiableAt ℂ (d.increment i) z:= by unfold increment alpha; fun_prop
  have h₀ : d.increment i 0≠0:=by simp only [increment,alpha,mul_zero,add_zero]; exact_mod_cast h
  let V := {z | d.increment i z≠0}; have ho:IsOpen V:=(isOpen_ne.preimage (show Differentiable ℂ (d.increment i) from hc).continuous)
  obtain ⟨R,hr,hh⟩:=Metric.mem_nhds_iff.mp (ho.mem_nhds (show (0:ℂ)∈V from h₀))
  let f(z:ℂ):= (d.increment i z)⁻¹
  have hA (z:ℂ) (hz:z∈ V) : DifferentiableAt ℂ f z:=(hc z).inv hz
  let r:=R/2; have he : Metric.closedBall (0:ℂ) r ⊆ V:= (Metric.closedBall_subset_ball (by dsimp [r]; linarith)).trans hh
  have ht : Meridian (zone r) (fun z=>fun (n:ℕ) (_:External I n)=> f z):= by
    refine ⟨fun n=> (Wall.formula (k:=f) (Metric.closedBall 0 r) (isCompact_closedBall ..) (fun z hz=>hA z (he hz)) (fun z hz=> ?_) Metric.ball_subset_closedBall),fun z hz=>⟨fun _ _ _=>rfl,fun _ _=>rfl⟩⟩
    have hl : DifferentiableOn ℂ f V:=fun w hw=>(hA w hw).differentiableWithinAt
    exact ((hl.analyticAt (ho.mem_nhds (he hz))).restrictScalars (𝕜:=ℝ)).contDiffAt
  exact Vortex.mono (k:=0) (regular_swirl ht (half_pos hr)) (Nat.zero_le _)

lemma regular_open (h : Meridian (zone R) F) (hr:0<R): Vortex 1 (step U d F):=by
  refine Vortex.add ?_ (Vortex.sum _ _ (fun i _=> ?_))
  · obtain ⟨S,hS,H⟩:= Metric.mem_nhds_iff.mp d.safely
    exact (regular_swirl (space U d (h.mono (zone_le (min_le_left R S))) (fun z hz=> H (zone_le (min_le_right R S) hz))) (lt_min hr hS)).mono (Nat.zero_le 1)
  have hp := Vortex.mul (I:=I) (singlePole d i) (regular_swirl (pbody_meridian U i h) hr)
  exact hp
end Mellin
end YM.MSbar.Pole
