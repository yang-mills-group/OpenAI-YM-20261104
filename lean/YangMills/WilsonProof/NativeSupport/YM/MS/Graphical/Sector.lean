import YM.MS.Graphical.Sector
import YM.MS.Hem.Foundation

/-!
# UV in the Schwinger length of the largest line

In these modules we specify graph integrals in *scale sectors*. Use logarithmic
length (UV is minus infinity). This file defines an integration prescription:
cut off the log length, add the analytic endpoint contribution of the
indicated (potentially divergent) Taylor orders, then remove the cutoff. Everything is at
**fixed** infrared length. This analytic continuation of endpoint integrals is
not the MS counterterm operation. In particular, for the relevant graph
inputs, it gives a *meromorphic*, not necessarily holomorphic, germ. Poles
aren't being subtracted from the coupling or operator here.

An important feature of this definition is the choice of regulator and order
of integrations. It's an iterated analytic regulator: at a sector node (line)
the already integrated child sector(s) are used in the integrand. One need not
look, e.g., for complex dimensions with four open axes and all the scale and
momentum integrals at all depths absolutely converging simultaneously.
In fact we give *another realization* later by simultaneous UV cutoff on all
the lines of a graph at fixed infrared length, limit and continuation; see
`Sprout.at_absolute_cut` (`SectorsAtCut`).

Use the momentum/colour/sector and Taylor test conventions of `YM.MS`.
`s` and `cut` below are upper and lower **log** lengths. `x` is the exponent
parameter, which also lets us specify analytic integration of the endpoint
terms separately. For dimension `4+2z` and `loops` actual dimensional loop
integrations (a contracted loop doesn't count), at engineering height `h`, we
use `x=-h-2*z*loops`, `h=4` for bulk, `h=operator dimension` for a single
physical mark. In particular the convention here for the power of length uses
`sources external`. On external word `w` the actual exponent is `x+mass w`.
`mass w` counts field dimensions (`Landau.dim`: 1 for `gauge`, `ghost`,
2 for `anti`, `gaugeC`). Use `h+1` Taylor projections: degrees 0 through h *including* the
field dimensions. Endpoints with no dimensional loop can use the simple integral
(no added term): we will verify convergence there too.

Evaluation here on dimensionally regulated graph objects is a **germ**
calculation; definitions on total functions like `Mob`, `Coat` can give junk
when used outside that domain. Integrals below on `[cut,s]` are oriented (only
the germ of cut near minus infinity matters).
-/

set_option autoImplicit false
noncomputable section

namespace YM.MS.Graphical

open Set (Iic)
open Filter Function Finset MeasureTheory
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps
open Garment Color Shine Hem Mell
open scoped Topology ContDiff Interval

variable {G : Gauge} {m k h ℓ : ℕ} {F : Mob G} {z x : ℂ}


lemma scalingShell_eq (x : ℂ) (F : Mob G) (t : ℝ) :
    scalingShell x F t = plow x t F := rfl




lemma tail_primitive_eq (k : ℕ) (x : ℂ) (hp : kPrice F) (t : ℝ) :
    analyticTail k x t F = plow x t (cPos k x F) := by
  rw [← cert]
  unfold cPos analyticTail
  rw [map_sum]
  apply Finset.sum_congr rfl; intro i hi
  rw [map_smul, cert, move_tad hp, smul_smul, div_eq_mul_inv, mul_comm]

lemma scalingShell_continuous (hp : kPrice F) (w : Legs (Shore G m)) :
    Continuous fun t => scalingShell x F t m w := by
  -- simpler use Taylor remainder k=0
  simpa only [scalingShell_eq, wood, Hem.clear, haze_zero, sub_zero] using
    sturdy_wood (x := x) (k := 0) hp w

/-- Formula at the log cutoff. `mend … cut` is the integrated Taylor remainder
below the cutoff, which we will show tends to zero. -/
lemma analytic_endpoint_identity (hp : kPrice F) (hx : 0 < x.re + k)
    (notpole : ∀ i : ℕ, i < k → x + i ≠ 0) (cut s : ℝ) (w : Legs (Shore G m)) :
    (∫ t in cut..s, scalingShell x F t m w) + analyticTail k x cut F m w =
      plow x s (progress k x F + cPos k x F) m w -
        mend (fun t => wood k x t F) cut m w := by
  -- FTC before taking anything to the limit. The upper primitive includes the analytic
  -- endpoint. `progress` is only on the Taylor remainder, integrable over Iic.
  let A (t : ℝ) := plow x t (progress k x F + cPos k x F) m w
  have ht : Trail (progress k x F + cPos k x F) F x := by
    have h := Trail.plus (Trail.prog_p hp hx) (modular hp notpole)
    rwa [Hem.clear, sub_add_cancel] at h
  have eq t : A t = mend (fun t => wood k x t F) t m w + analyticTail k x t F m w := by
    unfold A
    rw [tail_primitive_eq k x hp, ← cert x t, map_add, cert, cert, frame_time]
    rfl
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := A) (f' := fun t => scalingShell x F t m w) (fun t _ => ht.derive t m w)
      ((scalingShell_continuous hp w).intervalIntegrable ..)]
  change A s - A cut + _ = A s - _
  rw [eq cut]
  abel

lemma analytic_endpoint_limit (hp : kPrice F) (hx : 0 < x.re + k)
    (notpole : ∀ i : ℕ, i < k → x + i ≠ 0) (s : ℝ) (w : Legs (Shore G m)) :
    Tendsto (fun cut => (∫ t in cut..s, scalingShell x F t m w) + analyticTail k x cut F m w)
      atBot (𝓝 (plow x s (progress k x F + cPos k x F) m w)) := by
  simp_rw [analytic_endpoint_identity hp hx notpole]
  have tail : Tendsto (fun cut : ℝ => mend (fun t => wood k x t F) cut m w) atBot (𝓝 0) :=
    tendsto_integral_Iic_zero tendsto_id
  simpa only [sub_zero] using tail.const_sub (plow x s (progress k x F + cPos k x F) m w)

/-! The compensation really evaluates an analytic continuation. Freeze all momenta,
including the source momentum, the dimension parameter, and the child kernels. Vary an
auxiliary length exponent. The cost hypotheses give the holomorphic integral of the
remainder on the stated (larger) half-plane; the other terms are the displayed fractions.
Where convergence holds by positive real exponent, nothing has been subtracted. -/

lemma integrate_convergent_halfplane (hp : kPrice F) (hx : 0 < x.re) (k : ℕ) (s : ℝ)
    (w : Legs (Shore G m)) :
    IntegrableOn (fun t => scalingShell x F t m w) (Iic s) ∧
    (∫ t in Iic s, scalingShell x F t m w) =
      plow x s (progress k x F + cPos k x F) m w := by
  have hg : IntegrableOn (fun t => scalingShell x F t m w) (Iic s) := by
    simpa only [wood, Hem.clear, haze_zero, sub_zero, scalingShell_eq] using
      frame hp (k := 0) (x := x) (by simpa only [Nat.cast_zero, add_zero] using hx) s m w
  have he (j : ℕ) : 0 < (x+j).re := by simp only [Complex.add_re, Complex.natCast_re]; positivity
  have ht : Tendsto (fun t : ℝ => analyticTail k x t F m w) atBot (𝓝 0) := by
    unfold analyticTail; simp only [Finset.sum_apply, Pi.smul_apply]
    convert tendsto_finsetSum (f := fun (j : ℕ) (t : ℝ) =>
       (Alps.amount (x+j) t / (x+j)) • Tad F j m w)
       (a := fun _ => 0) (range k) (fun i hi => ?_) using 1
    · simp
    simpa only [zero_div, zero_smul] using
      (((x_scale0 (he i)).div_const (x+i)).smul_const (Tad F i m w))
  have hxk : 0 < x.re + k := by positivity
  have non (i : ℕ) (_ : i < k) : x + i ≠ 0 := fun hz =>
    (show 0 < (0:ℝ) from (show 0 < (0:ℂ).re from hz ▸ he i)).false
  refine ⟨hg, tendsto_nhds_unique ?_ (analytic_endpoint_limit hp hxk non s w)⟩
  simpa only [add_zero, id_eq] using
    (intervalIntegral_tendsto_integral_Iic s hg tendsto_id).add ht

lemma remainder_continues (hp : kPrice F) (hx : 0 < x.re + k) (w : Legs (Shore G m)) :
    DifferentiableAt ℂ (fun z => progress k z F m w) x := by
  let ε : ℝ := (x.re + k)/2
  have hε : 0 < ε := by unfold ε; positivity
  have ht : DifferentiableAt ℂ (fun z => progress k (z+x) F m w) 0 := by
    apply Hol.top (f := fun z => progress k (z+x) F) (D := disc ε) _ _ _
    · exact Metric.mem_ball_self hε
    refine prog_hol hε ?_ (fun z _ => differentiableAt_fun_id.add_const x) (Hol.stays hp)
    intro i hi
    have hn : ‖i‖ < ε := by simpa only [disc, Metric.mem_ball, dist_zero_right] using hi
    have hl := (abs_le.mp (Complex.abs_re_le_norm i)).1
    simp only [Complex.add_re]; unfold ε at *; linarith
  let v (z : ℂ) := z - x
  have he : v x = 0 := sub_self x
  have hy : DifferentiableAt ℂ (fun z => progress k (z+x) F m w) (v x) := he.symm ▸ ht
  have hz : (fun z => progress k (z+x) F m w) ∘ v = (fun z => progress k z F m w) :=
    funext fun _ => by simp [v]
  rw [← hz]
  exact hy.comp x (by unfold v; fun_prop)

lemma integrate_continues (hp : kPrice F) (hx : 0 < x.re + k) (s : ℝ)
    (notpole : ∀ i : ℕ, i < k → x + i ≠ 0) (w : Legs (Shore G m)) :
    DifferentiableAt ℂ (fun z => plow z s (progress k z F + cPos k z F) m w) x := by
  have ht : DifferentiableAt ℂ (fun z => cPos k z F m (sr s w)) x := by
    unfold cPos; simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply DifferentiableAt.fun_sum
    intro i hi
    have hz : DifferentiableAt ℂ (fun z : ℂ => z + i) x := differentiableAt_fun_id.add_const _
    exact (hz.inv (notpole i (mem_range.mp hi))).mul_const _
  simp only [plow, Pi.add_apply, Alps.amount]
  exact DifferentiableAt.mul (by fun_prop) ((remainder_continues hp hx (sr s w)).add ht)

lemma cutIntegral_limit_cycles (hℓ : ℓ ≠ 0) (hp : kPrice F)
    (hx : 0 < (vamp z h ℓ).re + ↑(h+1))
    (notpole : ∀ i : ℕ, i < h+1 → vamp z h ℓ + i ≠ 0) (s : ℝ) (w : Legs (Shore G m)) :
    Tendsto (fun cut : ℝ => cutIntegral ℓ h s cut z F m w)
      atBot (𝓝 (plow (vamp z h ℓ) s (Bless h ℓ z F) m w)) := by
  simpa only [cutIntegral, if_neg hℓ, Bless] using analytic_endpoint_limit hp hx notpole s w

lemma tree_shell_integrable (hp : kPrice F)
    (hv : Wind (fun t => plow (-(h:ℂ)) t F) atBot 0) (s : ℝ) :
    Gather (scalingShell (-(h:ℂ)) F) s := by
  simpa only [Gather, scalingShell_eq, wood, peer hp hv] using
    frame hp (x := -(h:ℂ)) (k := h+1) (by simp) s

lemma cutIntegral_limit_tree (hp : kPrice F)
    (hv : Wind (fun t => plow (-(h:ℂ)) t F) atBot 0) (s : ℝ) (w : Legs (Shore G m)) :
    Tendsto (fun cut : ℝ => cutIntegral 0 h s cut z F m w)
      atBot (𝓝 (plow (vamp z h 0) s (Bless h 0 z F) m w)) := by
  simpa only [cutIntegral, scalingShell_eq, vampV, Bless, frame_time, mend, wood, peer hp hv,
    if_true, add_zero, id_eq] using
      intervalIntegral_tendsto_integral_Iic s (tree_shell_integrable hp hv s m w) tendsto_id

/-- On a sufficiently small punctured neighborhood (`dotty`), the result of the UV
integration prescription, with `s` fixed. For loop-zero inputs we check convergence
directly (`tree_shell_integrable`, `cutIntegral_limit_tree`); for loop inputs with the
analytic compensation see also `analytic_endpoint_identity`. -/
theorem removal (f : ℂ → Mob G) (hm : ∀ᶠ z in dotty, kPrice (f z))
    (h ℓ : ℕ) (hp : ℓ = 0 → ∀ᶠ z in dotty, Wind (fun s => plow (-(h:ℂ)) s (f z)) atBot 0) :
    ∀ᶠ z in dotty, ∀ s, (∀ m : ℕ, ∀ w : Legs (Shore G m),
        Tendsto (fun cut : ℝ => cutIntegral ℓ h s cut z (f z) m w)
          atBot (𝓝 (scaleIntegral ℓ h s z (f z) m w))) ∧
        scaleIntegral ℓ h s z (f z) = plow (vamp z h ℓ) s (Bless h ℓ z (f z)) := by
  suffices ht : ∀ᶠ z in dotty, ∀ s : ℝ, ∀ m : ℕ, ∀ w : Legs (Shore G m),
        Tendsto (fun cut : ℝ => cutIntegral ℓ h s cut z (f z) m w)
          atBot (𝓝 (plow (vamp z h ℓ) s (Bless h ℓ z (f z)) m w)) by
    filter_upwards [ht] with z hz
    intro s
    have he : scaleIntegral ℓ h s z (f z) = plow (vamp z h ℓ) s (Bless h ℓ z (f z)) :=
      funext fun m => funext fun w => (hz s m w).limUnder_eq
    exact ⟨he.symm ▸ hz s, he⟩
  by_cases hx : ℓ=0
  · subst ℓ
    exact (hm.and (hp rfl)).mono (fun _ he s _ w => cutIntegral_limit_tree he.1 he.2 s w)
  filter_upwards [hm, vamp_up h ℓ, vamp_room h ℓ (Nat.pos_of_ne_zero hx)] with z he ht hr
  exact fun s m w => cutIntegral_limit_cycles hx he ht hr s w

end YM.MS.Graphical
