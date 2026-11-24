import YM.MS.Hem.Foundation

/-!
# An ordered Schwinger scale integral (for the graph-side construction)

The *upper* endpoint here is a retained, common IR regulator length `exp s`.
Scales are log lengths. The integrating edge is the **last** edge (largest
length, with respect to the edges still present). Its amplitude is fed the
integrals on the component(s) from cutting that edge, computed with this
edge's length as IR cutoff. This prescription for values **near z=0** uses iterated limits (inside
out). As a main check on this regulator, we will also use a definition of
the Feynman integrals which sends a *common* UV cutoff to zero first at
fixed IR cutoff and uses dimensional analytic continuation of the resulting
functions. See `Escorted`, `Athwart`, `SectionWalk` & `Endowment` about
their convergence domains and equivalence -- important because we don't
just want to reinterpret algebra in Leader & Comet.

This file treats the UV endpoint in that rule. We use a Taylor–Mellin
prescription for integration in continued dimension. Use the *actual*
integral with a lower endpoint `a`, and add the integrals up to `a` of the
low Taylor terms, using analytic powers for those elementary integrals. So a
Taylor term scaling as `exp (t x)` integrates from `-∞` to `a` as
`exp (a x) / x`. We should only evaluate the rule off the corresponding
poles. No free Taylor constants. This UV regularization of the radial
integrals is **not** our pole subtraction/forest operation! We still have
Laurent series in dimension parameter z (in particular, poles at z=0).
Lengths in these integrals range over the continuum.

Prove the formula at cutoff with its remainder, and the UV limit on every
list in every auxiliary dimension. Loop 0 uses the *plain*, convergent,
lower endpoint; see the hypothesis and proof below. Here `Tad W j` is
Taylor degree j in engineering units, INCLUDING weights of all fields.
-/

set_option autoImplicit false
noncomputable section
namespace YM.MS.ScaleForest

open Set Filter MeasureTheory Real
open Plane Koszul Heat Flux Landau Arts Arc Spin Pilot Wire Rock Path Oceans Plum Alps Garment Color
open Shine Hem Mell
open scoped Topology ContDiff

variable {G : Gauge} {k h n ell : ℕ} {x z : ℂ} {W : Mob G} {f : ℂ → Mob G}

/-- Mellin integral at *both* cutoffs. No pole extraction. -/
def finiteIntegral (a s : ℝ) (x : ℂ) (W : Mob G) : Mob G :=
  fun _ w => ∫ t in a..s, plow x t W _ w

/-- Below-cutoff Taylor power integrals. Use with nonsingular denominators. -/
def belowCut (a : ℝ) (x : ℂ) (k : ℕ) (W : Mob G) : Mob G :=
  ∑ j ∈ Finset.range k, (x + j)⁻¹ • amount (x + j) a • Tad W j

/-- UV regularization in the scale integral with the indicated engineering and
(explicit) loop powers. Keep the UV cutoff visible. -/
def regulated (a s : ℝ) (z : ℂ) (h ell : ℕ) (W : Mob G) : Mob G :=
  finiteIntegral a s (vamp z h ell) W +
    if ell = 0 then 0 else belowCut a (vamp z h ell) (h + 1) W

/-- One scale integration in the graph rules. Store at unit length; there is
an arbitrary-length rule with the *same regulator* coming from scaling this
answer, proved below. `limUnder` junk outside the germ is immaterial. -/
def scaleIntegral (z : ℂ) (h ell : ℕ) (W : Mob G) : Mob G :=
  fun _ w => limUnder atBot (fun a => regulated a 0 z h ell W _ w)

/-- Finite endpoints integrability on all tests (no course restriction). -/
theorem continuous_plow (hw : kPrice W) (x : ℂ) (w : Legs (Shore G n)) :
    Continuous (fun t => plow x t W _ w) := by
  convert Mell.sturdy_wood (k := 0) (x := x) hw w using 1
  simp [wood, Hem.clear]

theorem interval_plow (hw : kPrice W) (a s : ℝ) (x : ℂ) (w : Legs (Shore G n)) :
    IntervalIntegrable (fun t => plow x t W _ w) volume a s :=
  (continuous_plow hw x w).intervalIntegrable _ _

theorem belowCut_eq (hw : kPrice W) (a : ℝ) (x : ℂ) (k : ℕ) :
    belowCut a x k W = plow x a (cPos k x W) := by
  rw [belowCut, cPos, ← cert, map_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [map_smul, cert, move_tad hw]

/-- Exact identity at finite cutoff with all compensations and remainder. -/
theorem finite_add_belowCut (hw : kPrice W) (hx : 0 < x.re + (↑(h+1 : ℕ) : ℝ))
    (hn : ∀ i : ℕ, i < h+1 → x + i ≠ 0) (a s : ℝ) :
    finiteIntegral a s x W + belowCut a x (h+1) W =
      plow x s (progress (h+1) x W + cPos (h+1) x W) - plow x a (progress (h+1) x W) := by
  let P := progress (h+1) x W
  let C := cPos (h+1) x W
  funext m w
  rw [belowCut_eq hw, Pi.add_apply, Pi.add_apply, finiteIntegral]
  have hI : (∫ t in a..s, plow x t W m w) =
      plow x s (P+C) m w - plow x a (P+C) m w :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => (GaugeTrail hw hx hn).derive t m w) (interval_plow hw a s x w)
  rw [hI, ← cert x a (P+C), map_add]
  change plow x s (P+C) m w - (plow x a P m w + plow x a C m w) + plow x a C m w =
    plow x s (P+C) m w - plow x a P m w
  abel

theorem finite_vanish (hw : kPrice W) (hx : 0 < x.re + (↑(h+1 : ℕ) : ℝ))
    (hn : ∀ i : ℕ, i < h+1 → x + i ≠ 0) (s : ℝ) :
    Shine.Wind (fun a => finiteIntegral a s x W + belowCut a x (h+1) W) atBot
      (plow x s (progress (h+1) x W + cPos (h+1) x W)) := by
  simp_rw [finite_add_belowCut hw hx hn]
  intro m w
  let L := plow x s (progress (h+1) x W + cPos (h+1) x W) m w
  simpa only [Pi.sub_apply, Pi.zero_apply, sub_zero] using
    ((frame_lim (W := W) (x := x) (n := h+1) m w).const_sub L)

/-- Exact identity at the two cutoffs for loop 0. -/
theorem finite_noLoop (hw : kPrice W) (hl : Shine.Wind (fun t => plow (-(h:ℂ)) t W) atBot 0)
    (z : ℂ) (a s : ℝ) :
    finiteIntegral a s (-(h:ℂ)) W =
      plow (-(h:ℂ)) s (Bless h 0 z W) - plow (-(h:ℂ)) a (Bless h 0 z W) := by
  have hx := (pale (x := z) hw hl).1
  rw [vampV] at hx
  funext m w
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hx.derive t m w)
    (interval_plow hw a s _ w)

/-- Don't even need Mellin continuation at loop 0. -/
theorem integrable_noLoop (hw : kPrice W) (hl : Shine.Wind (fun t => plow (-(h:ℂ)) t W) atBot 0)
    (s : ℝ) : Gather (fun t => plow (-(h:ℂ)) t W) s := by
  have hG := frame hw (show 0< (-(h:ℂ)).re + (↑(h+1 : ℕ) : ℝ) by simp) s
  simpa only [wood, Mell.peer hw hl] using hG

theorem uv_limit_aux (hw : kPrice W) (hl : ell=0 → Shine.Wind (fun t => plow (-(h:ℂ)) t W) atBot 0)
    (hx : 0 < (vamp z h ell).re + (↑(h+1 : ℕ) : ℝ))
    (hn : 0 < ell → ∀ i : ℕ, i < h+1 → vamp z h ell + i ≠ 0) (s : ℝ) :
    Shine.Wind (fun a => regulated a s z h ell W) atBot
      (plow (vamp z h ell) s (Bless h ell z W)) := by
  by_cases hh : ell = 0
  · subst ell
    simp_rw [regulated, if_true, add_zero, vampV, finite_noLoop hw (hl rfl) z]
    intro m w
    let L := plow (-(h:ℂ)) s (Bless h 0 z W) m w
    simpa only [Pi.sub_apply,Pi.zero_apply, sub_zero] using (((pale (x := z) hw (hl rfl)).2 m w).const_sub L)
  simpa only [regulated,Bless, if_neg hh] using finite_vanish hw hx (hn (Nat.pos_of_ne_zero hh)) s

theorem evaluated (hw : kPrice W) (hl : ell=0 → Shine.Wind (fun t => plow (-(h:ℂ)) t W) atBot 0)
    (hx : 0 < (vamp z h ell).re + (↑(h+1 : ℕ) : ℝ))
    (hn : 0 < ell → ∀ i : ℕ, i < h+1 → vamp z h ell + i ≠ 0) :
    scaleIntegral z h ell W = Bless h ell z W := by
  have hV := uv_limit_aux hw hl hx hn 0
  rw [posing] at hV
  exact funext fun m => funext fun w => (hV m w).limUnder_eq

theorem uv_limit (hw : mer f)
    (hl : ell=0 → ∀ᶠ z in dotty, Shine.Wind (fun t => plow (-(h:ℂ)) t (f z)) atBot 0) :
    ∀ᶠ z in dotty, scaleIntegral z h ell (f z) = Bless h ell z (f z) ∧
      ∀ s : ℝ, Shine.Wind (fun a => regulated a s z h ell (f z)) atBot
        (plow (vamp z h ell) s (scaleIntegral z h ell (f z))) := by
  have hL : ∀ᶠ z in dotty, ell = 0 → Shine.Wind (fun t => plow (-(h:ℂ)) t (f z)) atBot 0 := by
    by_cases H : ell = 0
    · exact (hl H).mono fun z hz _ => hz
    exact .of_forall fun z he => (H he).elim
  have hN : ∀ᶠ z in dotty, 0 < ell → ∀ i : ℕ, i < h+1 → vamp z h ell + i ≠ 0 := by
    by_cases H : 0 < ell
    · exact (vamp_room h ell H).mono fun z hz _ => hz
    exact .of_forall fun z he => (H he).elim
  filter_upwards [hw.price, hL, vamp_up h ell, hN] with z hz hE hV hD
  rw [evaluated hz hE hV hD]
  exact ⟨rfl,uv_limit_aux hz hE hV hD⟩

/-- The analytically continued value from the scale integral, prior to setting
its Mellin index `x = vamp z h ell` (used for ell positive). -/
def continued (s : ℝ) (x : ℂ) (h : ℕ) (W : Mob G) : Mob G :=
  plow x s (progress (h+1) x W + cPos (h+1) x W)

theorem integrable_right (hw : kPrice W) (hx : 0 < x.re) (s : ℝ) :
    Gather (fun t => plow x t W) s := by
  simpa only [wood,Hem.clear,haze_zero, sub_zero] using
    frame hw (k := 0) (x := x) (by simpa using hx) s

private theorem x_pos_addNat (hx : 0 < x.re) (j : ℕ) : 0 < (x+j).re := by
  rw [Complex.add_re,Complex.natCast_re]
  positivity

theorem continued_right (hw : kPrice W) (hx : 0 < x.re) (h : ℕ) (s : ℝ) :
    continued s x h W = fun m w => ∫ t in Iic s, plow x t W m w := by
  have hz := finite_vanish hw (show 0<x.re+(↑(h+1 : ℕ) : ℝ) from by positivity)
    (fun i _ hp => by
      have hv := x_pos_addNat hx i
      rw [hp] at hv
      norm_num at hv) s
  funext m w
  apply tendsto_nhds_unique (hz m w)
  let F (t : ℝ) := plow x t W m w
  let u : ℂ := ∫ t in Iic s, F t
  have hc : Tendsto (fun a => finiteIntegral a s x W m w) atBot (𝓝 u) := by
    simp_rw [finiteIntegral, ← intervalIntegral.integral_Iic_sub_Iic
      (integrable_right hw hx _ m w) (integrable_right hw hx _ m w)]
    simpa only [u, F, sub_zero, id_eq] using
      (tendsto_integral_Iic_zero (f := F) (μ := MeasureTheory.volume) tendsto_id).const_sub u
  have hv (j : ℕ) : Tendsto (fun a : ℝ => (x + j)⁻¹ • amount (x+j) a • Tad W j m w) atBot (𝓝 0) := by
    simpa only [zero_smul, smul_zero] using
      (((x_scale0 (x_pos_addNat hx j)).smul_const (Tad W j m w)).const_smul (x+j)⁻¹)
  have hV : Tendsto (fun a => belowCut a x (h+1) W m w) atBot (𝓝 0) := by
    simp only [belowCut, Finset.sum_apply, Pi.smul_apply]
    simpa only [Finset.sum_const_zero] using
      (tendsto_finsetSum (Finset.range (h+1)) (fun i _ => hv i))
  simpa only [u,F,Pi.add_apply,add_zero] using hc.add hV

theorem analytic_progress (hw : kPrice W) (hx : 0 < x.re + (k:ℝ)) (w : Legs (Shore G n)) :
    AnalyticAt ℂ (fun u => progress k u W n w) x := by
  rw [Complex.analyticAt_iff_eventually_differentiableAt]
  have hC (z : ℂ) (hz : 0 < z.re+(k:ℝ)) : DifferentiableAt ℂ (fun u => progress k u W n w) z := by
    obtain ⟨δ, hp, hs⟩ := exists_between hz
    let X (s : ℂ) := z + s
    have he : ∀ᶠ i in 𝓝 (0:ℂ), δ ≤ (X i).re + (k:ℝ) := by
      have hv : Continuous (fun i => (X i).re + (k:ℝ)) := by unfold X; fun_prop
      exact (hv.continuousAt.tendsto.eventually (lt_mem_nhds (show δ < (X 0).re + (k:ℝ) by
        simpa [X] using hs))).mono fun i hi => le_of_lt hi
    obtain ⟨R, hR, hU⟩ := Metric.mem_nhds_iff.mp he
    let Y (s : ℂ) := progress k (X s) W n w
    have ht : DifferentiableAt ℂ Y (z - z) := by
      rw [sub_self]
      exact (prog_hol hp (u := X) (R := R) (k := k) (fun i hi => hU hi) (fun i _ => by unfold X; fun_prop)
        (Rock.Hol.stays hw)).top n w 0 (Metric.mem_ball_self hR)
    have eqn : (fun u => progress k u W n w) = Y ∘ fun i : ℂ => i-z := by
      funext i; simp [Y,X,Function.comp,add_comm z]
    rw [eqn]
    exact ht.comp (f := fun i : ℂ => i-z) z (by fun_prop)
  refine Filter.Eventually.mono (p := fun z : ℂ => 0 < z.re + (k:ℝ)) ?_ fun z hz => hC z hz
  exact ((show Continuous (fun x : ℂ => x.re + (k:ℝ)) by fun_prop).continuousAt
    (x := x)).tendsto (lt_mem_nhds hx)

/-- The dimension parameter will be fixed in the regularized scale integral,
but this also verifies the analytic powers prescription as a Mellin
continuation on each tensor/list reading. The input `W` is the value of the
input kernel at that dimension parameter. -/
theorem continued_meromorphicAt (hw : kPrice W) (hx : 0 < x.re + (↑(h+1 : ℕ) : ℝ))
    (s : ℝ) (w : Legs (Shore G n)) : MeromorphicAt (fun u => continued s u h W n w) x := by
  have he : AnalyticAt ℂ (fun u => amount (u+(mass w:ℂ)) s) x := by
    rw [Complex.analyticAt_iff_eventually_differentiableAt]
    refine .of_forall fun i => ?_
    unfold amount
    fun_prop
  refine he.meromorphicAt.mul ((analytic_progress hw hx (sr s w)).meromorphicAt.add ?_)
  let v := sr s w
  change MeromorphicAt (fun z => cPos _ z W n v) x
  simp_rw [cPos, Finset.sum_apply, Pi.smul_apply]
  refine MeromorphicAt.fun_sum fun i _ => ?_
  exact (analyticAt_id.add (analyticAt_const (v := (i:ℂ)))).meromorphicAt.inv.smul
    analyticAt_const.meromorphicAt

theorem uv_power (hw : kPrice W) (hx : 0 < x.re + (↑(h+1 : ℕ) : ℝ))
    (hn : ∀ i : ℕ, i < h+1 → x + i ≠ 0) (s : ℝ) :
    Shine.Wind (fun a => finiteIntegral a s x W + belowCut a x (h+1) W) atBot
      (continued s x h W) := finite_vanish hw hx hn s

end YM.MS.ScaleForest
