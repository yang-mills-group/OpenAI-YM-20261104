import YM.OPE.Sweep.Camp
import YM.Trace.Physicalv2.GermChain
import YM.Pert.Asymptotics.RawAxis

/-!
# Return map on one (literal, not test-addressed) root

A/Fk comparison prep. This report is on the *actual* torus regulator on the
common UV path. We give the translation from the full marked polynomial and
later the bequeathed physical estimates; this is the receiving signature of an
actual OPE extraction for finite-cutoff matched root errors.

- Input root and output field are **non-coincident literal geometry** for the
  later producer; the definition here allows one-root polynomials/presmeared
  clusters/differences, not claiming prices yet for any of them.
  Reports and conversions use literal points everywhere, with the
  supported stencil of the actual construction. In
  particular the germ fit is the representation-INDEPENDENT true page test of
  Trace.Physicalv2, on the root's testLinks at the actual period. This uses
  stationary tests on the torus (through `F.scaled`, actual `Hol.params`, and
  **all** regular labels incl wrap), not extra spatial cutoff on those jets in
  Fk. Units/addresses matter: a literal point report alone will not suffice
  for Fk even when later proved for Λ^B separation. Smooth test channels with
  all preimages and the addressed germ projection are additional obligations. The root `topReport` alone does not identify
  a product of reports or its perturbative coefficients.
- Here `credit` is in `a_u^d` units; the report returned to k=m
  will include `a_k^-d` below. (`alto` = complex inverse-spacing^d at this
  horizon.) The shadow report's (a_b/a_m)^d in this normalization is
  accounted already for a true literal capture P through its `a_b^d`-encoded
  density; **do not** multiply by it again when using these inputs.
- Density reconstruction/equality only, not yet estimates for FG propagation
  or physical exit. Reuses true single-root APIs of Trace.Germ and underlying
  comparison libraries; no actual Trace asymptotics used.
- Expansion convention g=inverse sqrt actual beta **at this step**. beta is
  the real action's, threshold `plank.threshold`, `κ=safety` is the forced divisor
  (not the Gaussian parameter). No universal scheme conversion.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG16.Literal
open Function Filter Set MeasureTheory Lattice Wilson RG Source Labels
open Extraction Next Push Push.GridApprox Marker Extra.Histories
open Extra.Histories.Relay Bid Cells Motion MergeProof MergeProof.Accent
open Trace.Physical.GermGraph Pert.Asymptotics
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
set_option quotPrecheck false
variable {G:Gauge}
section
variable (C:Family G) (N p d:ℕ)
local notation "P" => C.path
local notation "T" => C.path.rep N p

abbrev Cut := Config G (C.side N p) → ℂ

/-- Full push, on the history without course substitution. A later
match-up at any announced level below the actual top. -/
def credit (f:Cut C N p) (i:ℕ) (hi:i ≤ N) := (C.S.a i : ℂ)^d •
   pushTo C.path N p hi (fun U => (bare (C.beta N p) U : ℂ)* f U)

lemma credit_bare (h:C.Makes) (f:Cut C N p) : credit C N p d f N le_rfl =
    ((C.S.a N:ℂ)^d) • (fun U => ((T N).eval U : ℂ) * f U) := by
  rw [(h.wilson.starts N p).2, credit, pushTo_self]

private lemma fromCut (f: Cut C N p) (hf: Continuous f) : Integrable
    (fun U => (bare (C.beta N p) U : ℂ)* f U)
    (prior G (C.side N p)) :=
  Continuous.integrable_of_hasCompactSupport
    ((Complex.continuous_ofReal.comp (bare_cont ..)).mul hf)
    (HasCompactSupport.of_compactSpace _)

lemma credit_int (f: Cut C N p) (hf: Continuous f) {i:ℕ} (hi:i≤N) :
   Integrable (credit C N p d f i hi) (prior G (C.side i p)) :=
  (pushTo_integrable C.path N p hi _ (fromCut C N p f hf)).smul _

lemma credit_step (f: Cut C N p) (hf: Continuous f) {i:ℕ} (hi:i<N) :
   credit C N p d f i hi.le = transition (C:=C) d N p i (credit C N p d f (i+1) hi) := by
  have he : ((C.S.block i).val:ℂ) * (C.S.a (i+1):ℂ) = (C.S.a i:ℂ) := by
    rw [C.S.a_step, Complex.ofReal_div, Complex.ofReal_natCast, mul_comm]; apply div_mul_cancel₀
    exact_mod_cast (C.S.block i).property.ne'
  unfold credit transition blast
  rw [Birth.push_first _ _ _ hi, StepData.push_smul _ _ _ _
    (pushTo_integrable C.path N p hi _ (fromCut C N p f hf)), smul_smul, ← mul_pow, he]

/-- Audit denormalization. Partition of SAME unaltered path, comparing scalar moments. -/
lemma credit_moment (h:C.Makes) (f:Cut C N p)(hf:Continuous f) {i:ℕ}(hi:i≤N):
    (∫ U, credit C N p d f i hi U ∂prior G (C.side i p)) =
    ((C.S.a i:ℂ)^d) * (∫ V,((T i).eval V:ℂ)∂prior G (C.side i p)) * C.omega N p f := by
  unfold credit
  simp only [Pi.smul_apply, smul_eq_mul]; rw [integral_const_mul]
  have hp : (∫ V, ((T i).eval V:ℂ) ∂prior G (C.side i p)) =
      (Wilson.partition G (C.side N p) (C.beta N p):ℂ) := (integral_ofReal ..).trans (congr_arg Complex.ofReal (History.partition_eq P h.wilson N p i hi))
  unfold Family.omega; rw [moment_formula _ _ (continuous_integrable _ hf), hp, pushTo_integral C.path N p hi _ (fromCut C N p f hf), mul_assoc, mul_inv_cancel_left₀]
  exact Complex.ofReal_ne_zero.mpr (partition_pos _).ne'

/- The page fit of this full pushed density (λ slot already joined). True
reports are representation-INVARIANT on the history; the possible wrap
charges are kept via the test sheet, not dropped. No assertion that later
replacing one λ entry among a complete replicated polynomial could ignore the
partners. -/
def Booked (f:Cut C N p) (i:ℕ) (hi:i ≤ N) : Prop :=
   ∃ (q: store C d p i) (r:ℝ), reads d N p i q r ∧ credit C N p d f i hi = value (C:=C) d N p i q

open scoped Classical in
def sheet (f:Cut C N p)(i:ℕ)(hi:i ≤ N): store C d p i :=
   if e : Booked C N p d f i hi then e.choose else
     (C.factory d N p).entries i 0

lemma Booked.sheet {f:Cut C N p}{i:ℕ}{hi:i ≤ N} (h:Booked C N p d f i hi) :
    ∃ r, reads d N p i (sheet C N p d f i hi) r ∧
      credit C N p d f i hi = value (C:=C) d N p i (sheet C N p d f i hi) := by
  rw [Literal.sheet, dif_pos h]; exact h.choose_spec

def readPage (f:Cut C N p)(i:ℕ)(hi:i ≤ N) := page d p i (sheet C N p d f i hi)

lemma readPage_eq (f:Cut C N p)(h:C.Makes) {i:ℕ} (hi:i ≤ N)(hp:C.ref d ≤ i)
    (q:store C d p i) {r:ℝ}(hq:reads d N p i q r) (hE: credit C N p d f i hi = value (C:=C) d N p i q) :
    readPage C N p d f i hi = page d p i q := by
  have hb : Booked C N p d f i hi := ⟨q,r,hq,hE⟩
  obtain ⟨e,hr,hx⟩:= Booked.sheet C N p d hb
  exact same_page h hi hp hr hq (EventuallyEq.of_eq (hx.symm.trans hE))

variable {C N p d}
lemma g_pos (h:C.Makes) {i:ℕ} (hi:i ≤ N) : 0 < regulatorRun C N p i :=
   inv_pos.mpr (Real.sqrt_pos.mpr (Overlay.beta_positive h.wilson hi))
variable (C d N p)
set_option quotPrecheck false

/-- threshold coordinates = scaled(t/g) coupling coordinates (eq:28599 at
root). This uses the frames ON this C with the engineering momentum/factor
grading, not grading by field dimension alone. -/
def thresholdMap (i:ℕ) := (C.labels.level d).scaled ((T i).p.threshold / regulatorRun C N p i)

def gMap (i:ℕ) := (C.labels.level d).scaled (regulatorRun C N p i / (T i).p.threshold)

lemma g_threshold (h:C.Makes) {i:ℕ} (hi:i ≤ N)(x : C.label d) :
    gMap C N p d i (thresholdMap C N p d i x) = x ∧
    thresholdMap C N p d i (gMap C N p d i x) = x := by
  let t := (T i).p.threshold
  let g:= regulatorRun C N p i
  have ht:0<t:=(T i).p.threshold_pos
  have hg:0<g:= g_pos h hi
  let F:= C.labels.level d
  exact ⟨(show F.scaled (g/t) (F.scaled (t/g) x) = _ from by
    simpa only [inv_div] using F.scaled_inv (div_pos hg ht).ne' x),
    (show F.scaled (t/g) (F.scaled (g/t) x) = _ from by
    simpa only [inv_div] using F.scaled_inv (div_pos ht hg).ne' x)⟩

/-- Reference label of the normalized master at k. With a_k^d factor in the
literal point convention. -/
def master (h:C.Makes)(k:ℕ)(hk:Opened C d k p)(hi:k ≤ N) (x:C.label d) :=
    (C.factory d N p).terminal (((C.S.a k:ℂ)^d) •
       ((fitting d N p k h hk hi).symm (thresholdMap C N p d k x)))

def dress (h:C.Makes)(k:ℕ)(hk:Opened C d k p)(hi:k ≤ N) (y:C.label d) : C.label d :=
   gMap C N p d k (alto C.path k d • fitting d N p k h hk hi y)

theorem dress_inverse (h:C.Makes) (k:ℕ)(hk:Opened C d k p)(hi:k ≤ N)(y:C.label d):
    master C N p d h k hk hi (dress C N p d h k hk hi y) = (C.factory d N p).terminal y := by
  unfold dress master
  rw [(g_threshold _ _ _ _ h hi _).2,map_smul ((fitting d N p k h hk hi).symm),LinearEquiv.symm_apply_apply,
    smul_smul,alto,mul_inv_cancel₀,one_smul]
  exact pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (C.S.a_pos _).ne')

/-- Canonical (intrinsic germ) single-root answer in top label initial frame.
Needs `Booked` to be fit for its denotation; pad defaults in ill-fit use. -/
def topReport (h:C.Makes)(u:ℕ)(hu:Opened C d u p)(hi:u ≤ N)(f:Cut C N p): C.label d :=
    (fitting d N p u h hu hi).symm (readPage C N p d f u hi)

/-- Return it in reporting mesh frame with g convention. This is a concrete
cutoff root operator on full physical product, not on the horizon pivot/limit. -/
def receipt (h:C.Makes)(u k:ℕ)(hu:Opened C d u p)(hk:Opened C d k p)(ht:u ≤ k)(hN:k ≤ N)
    (f:Cut C N p) : C.label d := dress C N p d h k hk hN (topReport C N p d h u hu (ht.trans hN) f)
end
end YM.RG16.Literal
