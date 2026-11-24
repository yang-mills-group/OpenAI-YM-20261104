import YM.Pert.Kinetic.Port
import YM.Progress.JOINT_CALENDAR.Period

/-!
# Kinetic calibration usable on the shared family

One use in iterating the *unmarked* comparison: after a step we may have a much
better representation (say after a high-order subtraction and its affine reset)
of EXACTLY the pushed density. The newly extracted beta need not be the beta
on the path (equality of densities is not equality of representations). Estimate
the gap rather than substitute the new beta in the next Markov kernel.

Use `Pert.Kinetic`, in particular its Fourier low wave test `small_beta`, but
here the horizon infrastructure `Plenty` of the family in `Pert/Dense/End` isn't
needed and we do *not* use a separate Final. Pay the path constants using
subexponential in log lattice spacing (`Schedule.Gentle` is enough); still
uniform in cutoff and period. Note the `Rep.Lawful` requirements (including
the affine normalization), and equality of full unnormalized `Rep.eval`.

This does not bound the change in a representation caused by changing beta,
which needs separate accounting including masks and flags.
-/
set_option autoImplicit false
noncomputable section
namespace YM.IterationFour.Kinetic
open Function Filter Set Lattice Wilson MeasureTheory RG
open scoped Topology BigOperators
variable {G : Gauge} (C : Family G)

/-- Allow s in `Quotes` bigger than 2*hatBeta m. -/
def price (m : ℕ) : ℝ :=
    2 * C.path.levels.clock.hatBeta m * ((C.S.block m).val : ℝ)

lemma block_one_le (a : Levels G) (m : ℕ) : (1:ℝ) ≤ (a.S.block m).val := by
  exact_mod_cast (a.S.block m).property

lemma two_hat_le (m : ℕ) : 2 * C.path.levels.clock.hatBeta m ≤ price C m := by
  have hp := zero_lt_one.trans (C.path.levels.fits.delayed m)
  exact le_mul_of_one_le_right (by positivity) (block_one_le ..)

lemma price_pos (m : ℕ) : 0 < price C m := by
  have hp := zero_lt_one.trans (C.path.levels.fits.delayed m)
  exact lt_of_lt_of_le (mul_pos zero_lt_two hp) (two_hat_le ..)

omit C in
/-- Logs of the *fine* pre-L constants are paid with that L.
    The next L can pay too (ratios nondecreasing). -/
lemma path_charge (a : Levels G) (m : ℕ) :
    max ((a.params (m+1)).width)⁻¹ (a.params (m+1)).paths ≤ ((a.S.block (m+1)).val : ℝ) := by
  let F := a.params (m+1)
  have hw : 0 < F.width := F.width_pos
  have hw' : 0 < F.width⁻¹ := inv_pos.mpr hw
  let v := 1 + F.paths + F.width⁻¹ + F.columns + F.clip.relaxation + F.supportExponent
  have he : max F.width⁻¹ F.paths ≤ v := by
    have hv := F.paths_pos
    have hh := F.columns_ge
    have hr := F.clip.radius_pos
    have hh' := F.price_pos
    unfold v
    refine max_le ?_ ?_ <;> linarith only [hv, hw', hh, hr, hh']
  have hz := hw'.trans_le ((le_max_left F.width⁻¹ F.paths).trans he)
  let L : ℝ := (a.S.block m).val
  let j : ℝ := a.clock.J (m+1)
  have hL : 1 < L := by
    unfold L; exact_mod_cast (show 1 < (a.S.block m).val from (by linarith only [a.S.block_large m]))
  have hj : 1 ≤ j := by
    unfold j; exact_mod_cast (show 1 ≤ a.clock.J (m+1) from by linarith only [a.clock.adm (m+1)])
  have hm : v ≤ L := by
    have hv : Real.log v / Real.log L ≤ (j^2)⁻¹ := a.fits.logCost m
    have hs : (j^2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hj)
    apply (Real.log_le_log_iff hz (by linarith)).mp
    have hu := Real.log_pos hL
    simpa using (div_le_iff₀ hu).1 (le_trans hv hs)
  have hn : L ≤ (a.S.block (m+1)).val := by
    unfold L
    suffices (a.S.block m).val ≤ (a.S.block (m+1)).val by exact_mod_cast this
    rw [show a.S = a.clock.schedule from rfl, ← a.fits.sameFactor, ← a.fits.sameFactor (m+1)]
    exact a.fits.monotoneL (a.fits.mono (by omega))
  exact (he.trans hm).trans hn

local notation "A₀" => C.path.levels
-- use named binders for the quote end point
lemma quote_eventually (hG : G.Simple) : ∀ᶠ i : ℕ in atTop,
    Pert.Kinetic.Quotes ((A₀).budget i) ((A₀).params i).width
      ((A₀).params i).paths ((A₀).clock.loopCap i) ((A₀).clock.allowance i) (price C i) := by
  have he := Next.Rank.Station.hat_rate C.path.levels hG
  filter_upwards [he.eventually_ge_atTop ((A₀).params 0).supportExponent⁻¹,
    MergeProof.Ribbons.coverGrowth C hG |>.eventually_le_const zero_lt_one,
    eventually_gt_atTop 0] with i hu hh ht
  let p := C.path.levels.budget i
  let b := C.path.levels.clock.hatBeta i
  let g := C.path.levels.clock.hatCoupling i
  have ha : 1 ≤ b := ((A₀).fits.delayed i).le
  have hl := two_hat_le C i
  have hs : b ≤ price C i := (show b ≤ 2*b by linarith only [ha]).trans hl
  have h1 : 1 ≤ price C i := ha.trans hs
  have hg : 0 < g := inv_pos.mpr (Real.sqrt_pos.mpr (zero_lt_one.trans_le ha))
  have hV : g ≤ p.threshold := le_mul_of_one_le_right hg.le (Real.one_le_exp (sq_nonneg _))
  have hQ : ((A₀).S.block i).val ≤ price C i :=
    le_mul_of_one_le_left (by exact_mod_cast Nat.zero_le _) (show 1 ≤ 2*b by linarith only [ha])
  have ht' : i-1+1 = i := Nat.sub_add_cancel ht
  have hpaths := path_charge (A₀) (i-1)
  rw [ht'] at hpaths
  have hp : (p.B:ℝ) ≤ b := by
    have hpow : 1 + (p.B:ℝ) ≤ (1 + (p.B:ℝ))^8 := by
      have h := pow_le_pow_right₀ (show (1:ℝ) ≤ 1 + (p.B:ℝ) by simp) (show 1 ≤ 8 by decide)
      simpa only [pow_one] using h
    change (1+(p.B:ℝ))^8/b ≤ 1 at hh
    rw [div_le_iff₀ (zero_lt_one.trans_le ha), one_mul] at hh
    linarith only [hpow, hh]
  refine ⟨h1, ((A₀).params i).width_pos, ((le_max_left ..).trans hpaths).trans hQ,
    ?_, ?_, ?_, ?_, hp.trans hs, ?_, ?_⟩
  · rw [abs_of_pos ((A₀).params i).paths_pos]
    exact ((le_max_right ..).trans hpaths).trans hQ
  · exact (YM.Progress.Joint.cap_small (A₀) i).trans hl
  · have h : g^((11:ℝ)/5) ≤ 1 := Real.rpow_le_one hg.le (hV.trans p.threshold_le) (by norm_num)
    exact h.trans h1
  · exact Real.rpow_nonneg hg.le _
  · refine le_trans ?_ hs
    exact (inv_anti₀ ((A₀).params 0).price_pos ((A₀).fits.deepExp (Nat.zero_le _))).trans hu
  have h : p.threshold⁻¹ ≤ g⁻¹ := inv_anti₀ hg hV
  have hx : g⁻¹ = Real.sqrt b := inv_inv _
  rw [hx] at h
  exact (h.trans (show Real.sqrt b ≤ b by nlinarith [Real.sq_sqrt (zero_le_one.trans ha)])).trans hs

open MergeProof.Ribbons in
lemma affordable (hG : G.Simple) : Note C.S (price C) 0 := by
  have ht : Note C.S (fun i => ((C.S.block i).val : ℝ)) 0 :=
    ⟨fun i => zero_lt_one.trans_le (block_one_le ..), C.path.levels.fits.mesh⟩
  exact (((Note.notes C.S 2 zero_lt_two).mills (hut C hG)).mills ht).swapP (by norm_num)

open MergeProof.Ribbons in
lemma mesh_payment (hG : G.Simple) (K : ℝ) (q : ℕ) : ∀ᶠ i : ℕ in atTop,
    ∀ z : ℕ, K * price C i ^ q * Pert.Full.mesh (C.side i z) ≤ 1 := by
  let k := max 1 K
  have hk : 1 ≤ k := le_max_left ..
  have ht : Note C.S (fun i => k * price C i ^ q * (2*Real.pi * C.S.a i)) (-1) := by
    have hv := (Note.notes C.S (2*Real.pi) (by positivity)).mills (Note.note_a C.S)
    exact (((Note.notes C.S k (zero_lt_one.trans_le hk)).mills ((affordable C hG).powerN q)).mills hv).swapP (by ring)
  filter_upwards [ht.outweigh (Note.notes C.S 1 zero_lt_one) (by linarith)] with i hi z
  have hz : Pert.Full.mesh (C.side i z) ≤ 2*Real.pi * C.S.a i := by
    apply (div_le_iff₀ (Pert.Full.val_pos _)).2
    rw [mul_assoc]
    apply le_mul_of_one_le_right (by positivity)
    rw [show C.side i z=C.S.side i z from rfl, C.S.span_side]
    exact_mod_cast (C.S.period z).property
  have hs := pow_nonneg (price_pos C i|>.le) q
  exact (mul_le_mul (mul_le_mul_of_nonneg_right (le_max_right ..) hs) hz
    (Pert.Full.mesh_pos|>.le) (mul_nonneg (zero_le_one.trans hk) hs)).trans hi

/-- Any *exact* equal-eval lawful representation of any actual cutoff in the
    tail at these same quotes (or common larger quotes up to `price`). v does
    not enter `price`. Not a theorem about changing the coupling in a kernel. -/
theorem rigidity (hG : G.Simple) (hC : C.Makes) (q : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ (N p : ℕ), m ≤ N → ∀ R : Rep G (C.side m p),
      R.eval = (C.path.rep N p m).eval → ∀ σ L Λ δ w,
      R.Lawful σ L Λ δ w → Pert.Kinetic.Quotes R.p σ L Λ δ (price C m) →
      |R.beta-C.path.β N p m| ≤ (price C m ^ q)⁻¹ := by
  let d : ℝ := Fintype.card PlaqAxes
  filter_upwards [quote_eventually C hG,
    mesh_payment C hG (2*(Real.pi^2*(2*d))) 9,
    mesh_payment C hG (4*Real.pi^2 * Pert.Kinetic.coefK) (9+q)] with i he h1 h2 N p hi R hr σ L Λ δ w hl hp
  let n := C.side i p
  have hs := hC.wilson.represents N p i hi
  have hb : |(C.path.β N p i)| ≤ price C i := by
    rw [abs_of_pos ?pos]; case pos =>
      exact (half_pos (zero_lt_one.trans ((A₀).fits.delayed i))).trans_le hs.band.1
    exact hs.band.2.trans (two_hat_le C i)
  have hv : 4 ≤ n.val := by
    have h := (A₀).fits.sizeT i p
    change _ ≤ n.val at h
    omega
  have hpay : Real.pi^2 * Pert.Full.mesh n * (2*d * price C i ^ 9) ≤ 1/2 := by
    apply (le_div_iff₀ zero_lt_two).2
    refine Eq.trans_le ?_ (h1 p)
    change Real.pi^2 * Pert.Full.mesh n * _ * 2 = _ * _ * Pert.Full.mesh n
    ring
  have hδ := Pert.Kinetic.small_beta hG hr.symm hl hs.good (hs.vac.symm ▸ he) hp hv hb hpay
  rw [abs_sub_comm]
  refine hδ.trans ?_
  rw [← one_div]
  apply (le_div_iff₀ (pow_pos (price_pos C i) q)).2
  refine Eq.trans_le ?_ (h2 p)
  rw [pow_add]
  ring

/-- Explicit adapter: `Conversion` doesn't require the extra calendar bill on
    `Plenty`. Thus usable with the UV witness and therefore the every-character
    `Final` on it. -/
theorem conversion (hG : G.Simple) (hC : C.Makes) : Pert.Kinetic.Conversion C := by
  constructor
  intro q
  filter_upwards [rigidity C hG hC q] with i hi N h p R
  dsimp only
  intro he σ L Λ δ w hr hQ
  refine (hi N p h R he σ L Λ δ w hr (Pert.Kinetic.quotes_le (two_hat_le C i) hQ)).trans (inv_anti₀ ?_ ?_)
  · exact pow_pos (mul_pos zero_lt_two (zero_lt_one.trans (C.path.levels.fits.delayed i))) _
  exact pow_le_pow_left₀ (mul_nonneg zero_le_two (zero_le_one.trans (C.path.levels.fits.delayed i).le)) (two_hat_le C i) _
end YM.IterationFour.Kinetic
