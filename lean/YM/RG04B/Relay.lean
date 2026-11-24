import YM.RG04B.Windows
import YM.Pert.Kinetic.Port
import YM.UVNext.COUPLING_RESET.Probe

/-!
# Admissible reclosure alongside the actual trajectory

Keep *one* actual path. Permit RG03/04A to work on a rerender,
which is needed for iterating the unmarked qev cost. Store the calibration
change (e-natural) as a beta field on this R -- NOT the beta used in the
Markov kernel or the one defining g. It is an exact kinetic perturbation.
We prove it has an arbitrary-order flat coefficient, for *every lawful*
rerender request with the standard support budgets and identical density,
at **every** live step including N. No assumption of uniformity in how
R is picked or of its beta in the band; check the shared schedule on the
full-UV construction via the extra admissible booking, then use the Kinetic
result in the library, not its alternative existential schedules.
Only use the coefficient smallness in analytic consumers after pricing the
actual PathData/kinetic rendering and attachments -- those local estimates
are separate. This file also keeps track of the vacuum scalar.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG04B
open Function Filter Lattice Wilson RG Real MeasureTheory
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {G : Gauge}

/-- Add to the booking of the common Run. -/
def requireConversion : Request := {
  Request.none with
  hat := fun _ S L _ j x => ((S j).supportExponent+1)*((L j).val : ℝ)^4 ≤ Real.sqrt x
  eventualHat := fun _ _ _ _ _ => tendsto_sqrt_atTop.eventually_ge_atTop _ }
section
open MergeProof.Ribbons
variable {C : Family G} (hC : C.Makes) (hG : G.Simple)
set_option quotPrecheck false
local notation "P" => C.path.levels
local notation "T" => C.path.levels.clock
local notation "B" => C.path.levels.clock.hatBeta
local notation "A" => C.path.rep
local notation "S" => C.path.levels.params
local notation "L" => C.path.levels.clock.loopCap
local notation "δ" => C.path.levels.clock.allowance
local notation "w" => C.path.levels.clock.forcedAllowance

include hG
lemma preserve (h : Booked requireConversion P) : Plenty C := by
  intro i
  cases i with
  | zero =>
    have ht:= h.hats 0
    let c:= C.path.levels
    have hv : (c.params 0).supportExponent ≤ (c.params 1).supportExponent := c.fits.deepExp (Nat.zero_le _)
    change ((c.params 1).supportExponent+1)*(↑(c.clock.factor _).val:ℝ)^4 ≤ _ at ht
    rw [c.fits.sameFactor] at ht
    exact le_trans (mul_le_mul_of_nonneg_right (add_le_add_left hv _) (pow_nonneg (Nat.cast_nonneg _) _)) ht
  | succ i =>
    have ht:= h.hats i
    let c:=C.path.levels
    change ((c.params (i+1)).supportExponent+1)*(↑(c.clock.factor _).val:ℝ)^4 ≤ _ at ht
    rw [c.fits.sameFactor] at ht
    change ((c.params (i+1)).supportExponent+1)*(↑(c.S.block (i+1-1)).val:ℝ)^4 ≤ _
    rw [Nat.add_sub_cancel]
    exact ht.trans (sqrt_le_sqrt ((strictHat c hG).monotone i.le_succ))

/-- Closure class of TOTAL rebased representation before reading separate
comparison error: pesetas stay at same stage, clip, path (including all path
and curvature data/control). Does NOT bound `v`: it will necessarily match
the divergent vacuum scalar; do not put this in a contracting iterate. -/
structure Remodeled (C : Family G) (N p m : ℕ) (R : Rep G (C.side m p)) : Prop where
  point : R.p=C.path.levels.budget m
  clip : R.clip=(C.path.levels.params m).clip
  path : R.path = (C.path.rep N p m).path
  valid : R.Lawful (C.path.levels.params m).width (C.path.levels.params m).paths
    (C.path.levels.clock.loopCap m) (C.path.levels.clock.allowance m)
    (C.path.levels.clock.forcedAllowance m)
  exact_eval : R.eval=(C.path.rep N p m).eval

include hG hC
lemma offsets (h : Booked requireConversion P) (d : ℕ) :
    ∀ᶠ m in atTop, ∀ N, m ≤ N → ∀ p R, Remodeled C N p m R →
        |R.beta-(A N p m).beta| ≤ (gAt C N p m)^d := by
  have he:= preserve hG h
  have hc:= Pert.Kinetic.converted C hG he hC
  filter_upwards [Pert.Kinetic.paid_tail C hG he,hc.fits d,coupling_exit hC hG zero_lt_one] with m hr ht hs N hm p R hv
  have hp:= (hr N p).1
  have hz := ht N hm p R hv.exact_eval _ _ _ _ _ hv.valid (hv.point.symm ▸ hp)
  apply hz.trans
  have hβ := (hC.wilson.represents N p _ hm).band.2
  let x := gAt C N p m; have hx:0<x:= running_pos hC N p m hm
  rw [← reset_sq hC N p m hm] at hβ
  change ((2*(B) _)^d)⁻¹ ≤ x^d
  have hw : x⁻¹ ≤ x⁻¹^2:= by
    simpa only [pow_one] using (pow_le_pow_right₀ (one_le_inv₀ hx|>.2 (hs N p hm)) (one_le_two))
  calc
    _ ≤ (((x)⁻¹)^d)⁻¹ := inv_anti₀ (pow_pos (inv_pos.mpr hx) _) (pow_le_pow_left₀ (inv_nonneg.mpr hx.le) (hw.trans hβ) d)
    _ = x^d := by simp

omit hC hG in
lemma Remodeled.calibration (N p m : ℕ) (R : Rep G (C.side m p)) :
    R.path.inChannels R.clip R.p R.beta =
      (fun U : Config G (C.side m p) => R.path.inChannels R.clip R.p (C.path.β N p m) U +
        (R.beta - C.path.β N p m) * Push.BetaTransport.kinetic R.path R.clip R.p U) := by
  funext U
  rw [Push.BetaTransport.channels_split U R.beta, Push.BetaTransport.channels_split U (C.path.β N p m)]; ring

omit hG
open UVNext.CouplingReset Push.BetaTransport
omit hC in
lemma flatLog {n : Side} (R : Rep G n) (h : R.activities.RegularFamily R.p) :
    R.eval (1:Config G n) = Real.exp (R.v * Fintype.card (Site n)) := by
  unfold Rep.eval Rep.exponent
  rw [Activities.gas_one _ _ (flags_one _), channels_split 1 R.beta, kinetic_one, loop_one, additive_one h.at_flat]; simp

lemma Remodeled.scalar {N p m : ℕ} {R : Rep G (C.side m p)} (h : Remodeled C N p m R) (hx : m ≤ N) : R.v=(A N p m).v := by
  have hp := congr_fun h.exact_eval 1
  rw [flatLog R h.valid.labels.regular, flatLog (A N p m) (hC.wilson.represents N p _ hx).good.labels.regular,
    Real.exp_eq_exp] at hp
  exact mul_right_cancel₀ (by positivity) hp

lemma Remodeled.step {N p m : ℕ} {R : Rep G (C.side m p)} {X : Rep G (C.side (m+1) p)} (h : Remodeled C N p m R)
      (hf : Remodeled C N p (m+1) X) (ht : m < N) :
    R.eval=(C.path.levels.clock.op m p).push (C.path.β N p (m+1)) X.eval ∧
      (∀ U, 0 < R.eval U) ∧
      (∫ U, R.eval U ∂prior G (C.side m p)) = partition G (C.side N p) (C.path.β N p N) := by
    rw [h.exact_eval,hf.exact_eval]
    exact ⟨(hC.wilson.steps N p m ht).1,fun U=> Extra.Histories.Tour.bright C.path hC.wilson N p _ ht.le U,C.path.partition_eq hC.wilson N p m ht.le⟩

lemma staying (N p m : ℕ) (h : m ≤ N) : Remodeled C N p m (A N p m) :=
  let H:= hC.wilson.represents N p m h; ⟨H.vac,H.clip,rfl,H.good,rfl⟩
end
end YM.RG04B
