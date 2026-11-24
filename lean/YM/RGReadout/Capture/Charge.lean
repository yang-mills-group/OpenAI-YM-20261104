import YM.MergeProof.South.Loft
import YM.Trace.Physicalv2.GermChain
/-!
# Exact single-output *densities* from any cutoff product

Normalize source transfer in horizon-d engineering units. Read the full
coefficient of the bare product through the one actual unnormalized RG
push; its integral is exact on **that same** Wilson law. No assertion that
taking products after push is correct. Calibration for comparison with
`GermGraph` uses literal `Germ.projection` (uses full torus `testLinks` with
fixed lift); first spatial endpoint is the single-location/no-address-test
specialization. Appropriate for grid tests; not silently identifying the
full addressed A scheme.
-/

set_option autoImplicit false
noncomputable section
namespace YM.RGReadout.Literal

open Filter Function MeasureTheory Wilson Lattice RG Source Extra.Histories
open Trace.Physical Trace.Physical.GermGraph Push.Local
open MergeProof.Accent
open scoped Classical Topology BigOperators Matrix.Norms.Frobenius

variable {G : Gauge} (C : Family G) {N p i k d : ℕ}

def once (N p) (f : Config G (C.side N p) → ℂ) : Config G (C.side N p) → ℂ :=
  fun U => ((C.path.rep N p N).eval U : ℂ) * f U

/-- Exact unnormalized RG output of one marker selecting a whole cluster `f`.
Provides a common object for identifying different re-expressions. -/
def transmitted (N p i : ℕ) (h : i ≤ N) (f : Config G (C.side N p) → ℂ) :=
  gust C.path N p N (once C N p f) i h

def spacing (i d : ℕ) := (C.S.a i : ℂ)^d

/-- Charge in engineering units at level i. -/
def charge (N p d i : ℕ) (h : i ≤ N) (f : Config G (C.side N p) → ℂ) :=
  spacing C i d • transmitted C N p i h f

theorem spacing_ne (i d : ℕ) : spacing C i d ≠ 0 := pow_ne_zero _ (by exact_mod_cast (C.S.a_pos _).ne')

theorem live_once (hC : C.Makes) (f : Config G (C.side N p) → ℂ) (hf : Continuous f) :
    Integrable (once C N p f) (prior G (C.side N p)) := by
  have hc : Continuous ((C.path.rep N p N).eval) := by rw [(hC.wilson.starts ..).2]; exact bare_cont _
  exact ((Complex.continuous_ofReal.comp hc).mul hf).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem live_charge (hC : C.Makes) (h : i ≤ N) (f : Config G (C.side N p) → ℂ)
    (hf : Continuous f) : Integrable (charge C N p d i h f) (prior G _) :=
  (gust_live C.path N p N (once C N p f) (live_once C hC f hf) h).smul _

theorem transmitted_unscaled (h : i ≤ N) (f : Config G (C.side N p) → ℂ) :
    (spacing C i d)⁻¹ • charge C N p d i h f = transmitted C N p i h f := by
  rw [charge, inv_smul_smul₀ (spacing_ne C i d)]

theorem integral_charge (hC : C.Makes) (h : i ≤ N) (f : Config G (C.side N p) → ℂ)
    (hf : Continuous f) :
    (∫ x, charge C N p d i h f x ∂prior G _) =
      spacing C i d * ((partition G (C.side N p) (C.beta N p) : ℂ) * C.omega N p f) := by
  have he : (partition G (C.side N p) (C.beta N p) : ℂ) ≠ 0 :=
    by exact_mod_cast (partition_pos (G:=G) (n:=C.side N p) (C.beta N p)).ne'
  simp_rw [charge, Pi.smul_apply, smul_eq_mul, transmitted]
  rw [integral_const_mul, gust_sum _ _ _ _ _ (live_once C hC f hf) h]
  simp only [Family.omega, moment_formula _ _ (Wilson.continuous_integrable _ hf), ← mul_assoc]
  unfold once
  rw [(hC.wilson.starts ..).2]
  field_simp -- he

theorem charge_step (hC : C.Makes) (h : i < N) (f : Config G (C.side N p) → ℂ)
    (hf : Continuous f) :
    charge C N p d i h.le f = transition d N p i (charge C N p d (i+1) h f) := by
  let ℓ : ℂ := (C.S.block i).val
  have he : spacing C i d = ℓ^d * spacing C (i+1) d := by
    rw [spacing, spacing, ← mul_pow, C.S.a_step]
    congr 1
    have hl : ℓ ≠ 0 := Nat.cast_ne_zero.mpr (C.S.block i).pos.ne'
    rw [Complex.ofReal_div, Complex.ofReal_natCast]
    change _ = ℓ * (_ / ℓ)
    field_simp
  rw [charge, charge, transmitted, transmitted, gust_step C.path N p N _ h,
    he, transition, blast, StepData.push_smul _ _ _ _
      (gust_live _ _ _ _ _ (live_once C hC f hf) h), smul_smul]

theorem cylinder_charges (hC : C.Makes) (href : C.ref d ≤ i) (h : i ≤ N) (x : C.label d) :
    charge C N p d i h (C.O N p ((C.factory d N p).terminal x) 0) =
      calValues (C:=C) d N p i x := by
  induction h using Nat.decreasingInduction with
  | self =>
    rw [charge, transmitted, gust_base]
    funext U
    symm
    have hO : C.O N p ((C.factory d N p).terminal x) 0 = Source.initial (C.localSection d)
        C.path N p x 0 := by unfold Family.O TransferData.cylinder; rw [LinearEquiv.symm_apply_apply]
    rw [hO, Pi.smul_apply, calValues]
    exact ((hC.calibrated d N p href).encode x U).trans (mul_assoc ..)
  | of_succ j hj ih =>
    rw [charge_step C hC hj _ (C.continuousO ..), ih (href.trans j.le_succ)]
    exact (factory_eq d N p j hC href hj x).symm

/-- Germ coordinate readout, not image or budget equality, denotational
*here* on the original Rep. The only projection convention in
HasProjection is the full (including winding terms) Germ projection. -/
def HasProjection (N p d i : ℕ) (h : i ≤ N) (f : Config G (C.side N p) → ℂ)
    (x : C.label d) : Prop :=
  ∃ q : Coefficient (C.labels.level d) (C.side i p),
    (∃ r, GermGraph.reads (C:=C) d N p i q r) ∧
    q.density 0 (C.localSection d) (C.path.rep N p i) = charge C N p d i h f ∧
    x = page d p i q

lemma HasProjection.unique {h : i ≤ N} {f : Config G (C.side N p) → ℂ} {x y : C.label d}
    (hC : C.Makes) (hO : C.ref d ≤ i)
    (hx : HasProjection C N p d i h f x) (hy : HasProjection C N p d i h f y) : x=y := by
  obtain ⟨P,⟨a,hP⟩,hp,rfl⟩ := hx
  obtain ⟨Q,⟨b,hQ⟩,hq,rfl⟩ := hy
  exact same_page hC h hO hP hQ (EventuallyEq.of_eq (hp.trans hq.symm))

/-- Fitted coordinate, padded off domain. -/
def projection (N p d i : ℕ) (h : i ≤ N) (f : Config G (C.side N p) → ℂ) : C.label d :=
  if he : ∃ x, HasProjection C N p d i h f x then he.choose else 0

lemma projection_eq {h : i ≤ N} {f : Config G (C.side N p) → ℂ} {x : C.label d}
    (hx : HasProjection C N p d i h f x) (hC : C.Makes) (hi : C.ref d ≤ i) :
    projection C N p d i h f = x := by
  unfold projection
  split_ifs with h
  · exact h.choose_spec.unique C hC hi hx
  exact (h ⟨_,hx⟩).elim

end YM.RGReadout.Literal
