import YM.Integration.WilsonExteriorPortfolio
import YM.Integration.PhysicalOPEApproximation

/-! The complete signed numerical truncation error on a physical exterior detector.
The outer length is fixed before the inner length tends to zero. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonFarShell

open Set Filter Function OPE OPE.Orbits PhysMS Spec
open scoped Classical Topology

variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (R : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J : ℝ → PhysMS.tower S)
local notation "S₀" => Climb.Bel C.book

/-- The same exterior locations and labels as in the measured detector matrix. -/
def exterior (τ : ℝ) (e : ExteriorData S₀) : ExteriorData S :=
  classes S (WilsonExteriorPortfolio.carried J τ ∘ OPE.tags S₀ e)
    (τ • OPE.positions S₀ e)

private theorem exterior_apt (τ : ℝ) (hτ : 0 < τ) (e : ExteriorData S₀)
    (he : Apt e) : Apt (exterior J τ e) := by
  let x := Points.cons 0 (τ • OPE.positions S₀ e)
  have hx : x ∈ generic _ := by
    rw [show x = τ • Points.cons 0 (OPE.positions S₀ e) by
      simp only [x, Work.A05.smul_cons, smul_zero]]
    intro a i j hij
    exact he a (mul_left_cancel₀ hτ.ne' (by simpa only [PiLp.smul_apply, smul_eq_mul] using hij))
  have h := OPE.classes_apt (S := S) x hx (WilsonExteriorPortfolio.carried J τ ∘ OPE.tags S₀ e)
  have hy : Points.tail (Points.across (-(x 0)) x) = τ • OPE.positions S₀ e := by
    apply PiLp.ext
    intro i
    change (τ • OPE.positions S₀ e) i + -(0 : E4) = _
    simp
  rw [hy] at h
  exact h

/-- Identify the projection against an actual physical exterior with precisely the matching
row of the measured matrix, after changing the output coordinates at the outer length. -/
theorem measured_row (τ : ℝ) (h : ℕ) (e : ExteriorData S₀) (z : S.Field h) :
    witnessAt S h (exterior J τ e) z =
      WilsonExteriorPortfolio.row J S τ h e ((J τ h).symm z) := by
  rw [exterior, witness_classes, WilsonExteriorPortfolio.row_read]
  unfold WilsonExteriorPortfolio.points
  rw [Work.A05.smul_cons, smul_zero]
  change S.read _ (detectorRaw S ∘ Fin.cons (⟨h,z⟩ : S.Tag)
    (WilsonExteriorPortfolio.carried J τ ∘ OPE.tags S₀ e)) = _
  apply congrArg (S.read _)
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · change (⟨h, S.representative h z⟩ : C.book.Token) =
      ⟨h, S.representative h (J τ h ((J τ h).symm z))⟩
    rw [LinearEquiv.apply_symm_apply]
  · rfl

variable {I : Type} [Fintype I] {d : I → ℕ}
    (v : (i : I) → (Climb.Bel C.book).Field (d i))

/-- The full product before projection. It contains the identical exterior used by the bank. -/
def readings {h : ℕ} (E : Detector S₀ h) (τ r : ℝ) (x : I → E4) : Fin E.size → ℂ :=
  fun i =>
    let e := exterior J τ (E.listen i)
    whole S x (PhysMS.Frame.born J r v) (OPE.positions S e).ofLp
      (e := fun j => (OPE.tags S e j).1) (fun j => (OPE.tags S e j).2)

/-- The independent numerical OPE with its own complete truncation, in inner coordinates. -/
def coefficient (h : ℕ) (r : ℝ) (x : I → E4) :=
  (J r h).symm (R.packet h x (PhysMS.Frame.born J r v) 0)

variable (H : Leading F J) (hR : Foundation F R)
include H hR

/-- A preselected exterior length and its true independently prescribed detector are used
throughout. The inner threshold may depend on that outer length. There is one threshold for
every member of the finite detector and every admissible inner configuration. -/
theorem fixed_outer {h : ℕ} (E : Detector S₀ h) (τ : ℝ) (hτ : 0 < τ)
    (M η ε : ℝ) (hM : 0 ≤ M) (hη : 0 < η) (hε : 0 < ε) :
    ∀ᶠ r in Trace.Pilot.trail, ∀ x : I → E4, WithinRoom r M η x 0 →
      ‖readings J v E τ r x - WilsonExteriorPortfolio.bank J E S τ
        ((J τ h).symm (J r h (coefficient F R J v h r x)))‖ ≤ r^((h : ℝ)+1-ε) := by
  let e i := exterior J τ (E.listen i)
  have he i : Apt (e i) := exterior_apt J τ hτ (E.listen i) (E.awake i)
  choose δ hδ hc using fun i => detector_exterior_clearance (e i) (he i)
  have hh (i : Fin E.size) := PhysMS.Frame.single_report F R J H hR v
    (e := fun j => (OPE.tags S (e i) j).1) (fun j => (OPE.tags S (e i) j).2)
    h M η (δ i) ε hM hη (hδ i) hε
  filter_upwards [eventually_all.mpr hh, self_mem_nhdsWithin] with r hr hrpos x hx
  apply (pi_norm_le_iff_of_nonneg (Real.rpow_nonneg (le_of_lt hrpos) _)).mpr
  intro i
  change ‖readings J v E τ r x i - WilsonExteriorPortfolio.row J S τ h (E.listen i) _‖ ≤ _
  simp only [coefficient, LinearEquiv.apply_symm_apply]
  rw [← measured_row]
  exact (congrArg norm (detector_packet_residual F R h x (PhysMS.Frame.born J r v)
    (e i) (he i))).trans_le ((hr i x (OPE.positions S (e i)).ofLp 0 hx (hc i)).2 none)

/-- The signed omitted contribution seen by the actual inverse with outer length `τ` and
inner length `t * τ`. The constant is one, with all fixed geometry absorbed in the entrance. -/
theorem separation {h : ℕ} (E : Detector S₀ h) (τ : ℝ) (hτ : 0 < τ) (hu : τ ≤ 1)
    (M η ζ : ℝ) (hM : 0 ≤ M) (hη : 0 < η) (hζ : 0 < ζ) (hζ' : ζ < 1) :
    ∀ᶠ t in Trace.Pilot.trail, ∀ x : I → E4, WithinRoom (t*τ) M η x 0 →
      ‖readings J v E τ (t*τ) x - WilsonExteriorPortfolio.bank J E S τ
        ((J τ h).symm (J (t*τ) h (coefficient F R J v h (t*τ) x)))‖ ≤ t^((h : ℝ)+ζ) := by
  have ht : Tendsto (fun t : ℝ => t*τ) Trace.Pilot.trail Trace.Pilot.trail :=
    tendsto_nhdsWithin_iff.mpr ⟨by simpa using
      (tendsto_id.mono_left (nhdsWithin_le_nhds : Trace.Pilot.trail ≤ 𝓝 0)).mul_const τ,
      (show ∀ᶠ t : ℝ in Trace.Pilot.trail, 0 < t from self_mem_nhdsWithin).mono
        (fun _ hi => mul_pos hi hτ)⟩
  filter_upwards [ht.eventually (fixed_outer F R J v H hR E τ hτ M η (1-ζ) hM hη (by linarith)),
    self_mem_nhdsWithin] with t hr hp x hx
  have bound := hr x hx
  rw [show (h : ℝ)+1-(1-ζ)=(h : ℝ)+ζ by ring] at bound
  exact bound.trans (Real.rpow_le_rpow (mul_nonneg (le_of_lt hp) hτ.le)
    (mul_le_of_le_one_right (le_of_lt hp) hu) (add_nonneg (Nat.cast_nonneg _) hζ.le))


end YM.Integration.WilsonFarShell
