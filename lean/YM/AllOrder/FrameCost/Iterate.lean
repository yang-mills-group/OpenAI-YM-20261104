import YM.AllOrder.FrameCost.Row

/-!
# Subpower frame estimate without needing an all-order or log estimate

This drives compatibility past investor (unselected/character) choice.
Leading pair comparison & engineering laws were enough because we can
iterate fixed but sufficiently long log-ratio steps. This doesn't give a
polylog estimate -- need sharper local inputs for that.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.FrameCost
open Function Filter Set Real OPE Spec Table Ward Leading Trace Trace.Pilot Climb
open scoped BigOperators Topology Classical ContDiff

lemma reaches_span (f : ℝ → ℝ) (hf : ∀ x,0≤ f x) {a b : ℝ}
    (hstep : ∃ z : ℝ, 0<z ∧ ∀ᶠ t in (atTop : Filter ℝ), f (t+z) ≤ f t * Real.exp (a*z))
    (hc : ∀ z> (0:ℝ), ∃ A : ℝ,0≤A ∧ ∀ᶠ t in (atTop : Filter ℝ), ∀ s∈ Icc 0 z, f (t+s) ≤ f t*A)
    (hb : a<b) : ∀ᶠ t : ℝ in atTop, f t ≤ exp (b*t) := by
    obtain ⟨z,hz,hS⟩ := hstep
    obtain ⟨A,hA,hC⟩:= hc z hz
    obtain ⟨R,hR⟩:= eventually_atTop.1 (hS.and hC)
    let g (i:ℕ) := R+i*z
    let K:= f R * exp (-a*R)
    have hk : 0 ≤ K:= mul_nonneg (hf R) (exp_pos _).le
    have hrs(i:ℕ): R ≤ g i:= le_add_of_nonneg_right (by positivity)
    have hG(i:ℕ): f (g i) ≤ K * exp (a*g i) := by
       induction i with
       | zero=> rw [show g 0=R by simp [g]]; unfold K; rw [mul_assoc,← exp_add]; simp
       | succ i ih=>
         have he : g (i+1)=g i+z:=by unfold g; push_cast; ring
         rw [he]; refine ((hR _ (hrs i)).1.trans ((mul_le_mul_of_nonneg_right ih (exp_pos _).le).trans_eq ?_))
         rw [mul_assoc,← exp_add, mul_add a (g i) z]
    let D:=exp (|a| *z)
    have hp:Tendsto (fun x:ℝ=> Real.exp ((b-a)*x)) atTop atTop :=
       Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (sub_pos.mpr hb))
    filter_upwards [eventually_ge_atTop R,hp.eventually_ge_atTop (K*D*A)] with t ht he
    let n : ℕ:= ⌊(t-R)/z⌋₊
    have hs : g n ≤ t:= by
       have hv := (le_div_iff₀ hz).1 (Nat.floor_le (div_nonneg (sub_nonneg.mpr ht) hz.le) : (n:ℝ)≤ _)
       dsimp only [g]; linarith
    let s := t-g n
    have hT:s∈Icc 0 z:= by
       refine ⟨sub_nonneg.mpr hs,?_⟩
       have h' := lt_of_lt_of_le (Nat.lt_floor_add_one ((t-R)/z)) le_rfl
       have hx := (div_lt_iff₀ hz).1 h'; change t-R < ((n:ℝ)+1) * z at hx
       unfold s g; linarith
    have hz': t=g n+s:= by unfold s; ring
    have hx : exp (a*g n) ≤ D*exp (a*t):= by
       unfold D; rw [← exp_add]; apply exp_monotone
       have hu : a*g n-a*t=(-a)*s:= by nth_rw 1 [hz']; ring -- t in g ? local defs
       linarith only [hu, mul_le_mul (b:=|a|) (neg_le_abs a) hT.2 hT.1 (abs_nonneg a)]
    calc f t ≤ f (g n)*A :=  (congr_arg f hz').trans_le ((hR (g n) (hrs n)).2 s hT)
         _ ≤ K*exp (a*g n)*A:= mul_le_mul_of_nonneg_right (hG n) hA
         _ ≤ K*D*A*exp (a*t):= le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hx hk) hA) (le_of_eq (by ring))
         _ ≤ exp ((b-a)*t)*exp (a*t):= mul_le_mul_of_nonneg_right he (exp_pos _).le
         _ = _:= by rw [← exp_add]; congr 1; ring

variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
variable {F : Spec.Final C f S} {U : ℝ → FamilyFrame S} {g : ℝ → ℝ}
variable {d e : ℕ}
local notation "free" => Bel C.book
local notation "ℓ" => FrameCost.length

theorem upper (φ : S.Field d→ₗ[ℂ] ℂ) (he : e ≤ d) (hφ : ∀ p ∈ Levy.planeAt (U:=F.sector.derivatives) e he, φ p = 0) (h : Aligned F g U) :
    RateLE atTop id (scale_row U φ) (-(e:ℝ)) := by
    intro a ha; obtain ⟨b,hb,h'⟩ := exists_between ha
    refine reaches_span (fun t=> ‖scale_row U φ t‖) (fun t=> norm_nonneg (scale_row U φ t)) ?_
        (fun z _=>row_continue φ h z) h'
    obtain ⟨A,hA,hC⟩:= row_start φ he hφ h
    have hx:Tendsto (fun z:ℝ=> Real.exp ((b+e)*z)) atTop atTop:= Real.tendsto_exp_atTop.comp
      (tendsto_id.const_mul_atTop (by linarith only [hb]))
    obtain ⟨z,hz,hS⟩:= ((hx.eventually_ge_atTop A).and (eventually_gt_atTop (0:ℝ))).exists
    refine ⟨z,hS, (hC z hS.le).mono (fun t ht=> ht.trans
       (mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_right (show A≤ Real.exp ((b+e)*z) from hz) (exp_pos _).le).trans_eq ?_) (norm_nonneg (scale_row U φ t))))⟩
    rw [←exp_add]; congr 1; ring

/-- Physical inverse-log clock -/
def clock (r : ℝ) := -Real.log r
lemma clock_time : Tendsto FrameCost.clock trail atTop :=
    tendsto_neg_atTop_iff.mpr Real.tendsto_log_nhdsGT_zero
lemma clock_inverse {x : ℝ} (hx : 0<x) : ℓ (FrameCost.clock x) = x := by rw [FrameCost.length, FrameCost.clock,neg_neg, Real.exp_log hx]

/-- Anchored price for all length frames, any further sequence or filter.
 Upper payments with exponent e apply to coordinates of U(r,d) killed on
 the actual e-1 plane. In particular every viewer with OPE Services will
 receive `Anchored`. -/
theorem anchored (h : Aligned F g U) (φ : S.Field d→ₗ[ℂ] ℂ) (he : e ≤ d)
    (hφ : ∀ p ∈ Levy.planeAt (U:=F.sector.derivatives) e he, φ p = 0)
    (x : (free).Field d) : RateLE trail FrameCost.clock (fun r => φ (U r d x)) (-(e:ℝ)) := by
    have hh:RateLE trail FrameCost.clock (scale_row U φ ∘ FrameCost.clock) (- (e:ℝ)) := (upper φ he hφ h).comp FrameCost.clock_time
    have hz:= RateLE.bil (F:=scale_row U φ ∘ FrameCost.clock) hh (RateLE.const x clock_time) (u:=fun r => φ (U r d x)) ?_
    · rwa [add_zero] at hz
    filter_upwards [show ∀ᶠ r in trail, 0<r from self_mem_nhdsWithin] with r hr
    let V:=scale_row U φ (FrameCost.clock r)
    apply le_trans _ (V.le_opNorm x)
    change ‖_‖≤ ‖φ (U (ℓ (FrameCost.clock r)) d x)‖
    rw [clock_inverse hr]
end YM.AllOrder.FrameCost
