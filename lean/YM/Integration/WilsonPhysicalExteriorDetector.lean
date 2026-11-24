import YM.Integration.WilsonPhysicalExteriorFrame
import YM.Integration.WilsonExteriorPortfolio

/-! Read a near-scale field through far physical probes of the same state. The observed
source need not have either sign. A power left beyond the engineering horizon in those
actual correlations remains after the measured inverse. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalExteriorDetector
open Filter Set Spec Climb OPE OPE.Orbits PhysMS Trace.Pilot Labels Pert.Position Table
open scoped Topology Classical
open WilsonExteriorPortfolio

variable {G : Gauge} {C : Family G} {q : Extraction.Order} {S : Table C.book}
local notation "D₀" => Bel C.book
variable (J : ℝ → tower S) {d : ℕ} (U : Detector (Bel C.book) d)

/-- The near field in the *outer* detector's coordinates, with both genuine frame changes. -/
def outer (r t : ℝ) : E C.labels d ≃ₗ[ℂ] E C.labels d :=
  (J (t*r) d).trans (J r d).symm

def read (T : Table C.book) (r t : ℝ) (v : E C.labels d) : Fin U.size → ℂ :=
  bank J U T r (outer J r t v)

def receive (T : Table C.book) (r t : ℝ) (y : Fin U.size → ℂ) : E C.labels d :=
  (outer (d:=d) J r t).symm (decoder U.report (bank J U T r) y)

def invoice (T : Table C.book) (r t ε K : ℝ) : Prop :=
  (∀ v, receive J U T r t (read J U T r t v) = v) ∧
    ∀ y v, ‖receive J U T r t y - v‖ ≤
      K * t^(-(d:ℝ)-ε) * ‖y-read J U T r t v‖

/-- This is exactly the original signed field measurement: only the distinguished
insertion is carried by the inner frame. Every external position and label uses r. -/
theorem original (F : Final C q S) (r t : ℝ) (v : E C.labels d) (a : ℕ × ℕ)
    (j : ℕ) (hj : j ≤ a.1) (i : Fin U.size) :
    read J U (StressFlux.Matching.rounded C a.1 a.2) r t v i =
      SignedPhysicalWords.sample
        (Fin.cons (⟨d,J (t*r) d v⟩ : S.Tag) (carried J r ∘ OPE.tags D₀ (U.listen i)))
        (r • WilsonExteriorPortfolio.points D₀ (U.listen i)) a j hj := by
  change WilsonExteriorPortfolio.row J (StressFlux.Matching.rounded C a.1 a.2)
    r d (U.listen i) (outer J r t v) = _
  rw [WilsonExteriorPortfolio.original F J _ _ _ _ j hj]
  apply congrArg (fun w => SignedPhysicalWords.sample w
    (r • WilsonExteriorPortfolio.points D₀ (U.listen i)) a j hj)
  funext k
  refine Fin.cases ?_ (fun _ => ?_) k
  · change (⟨d,J r d ((J r d).symm (J (t*r) d v))⟩ : S.Tag) = ⟨d,J (t*r) d v⟩
    rw [LinearEquiv.apply_symm_apply]
  · rfl

private theorem at_measure (r t ε K : ℝ) (hK : 0≤K) (T : Table C.book)
    (he : ∀ x : S.Field d,
      ‖(J (t*r) d).symm x‖ ≤ K*t^(-(d:ℝ)-ε)*‖(J r d).symm x‖)
    (hT : priced U.report (bank J U T r)) (ht : 0<t) :
    invoice J U T r t ε (K*(2*‖U.report.toContinuousLinearMap‖)) := by
  constructor
  · intro v
    unfold receive read
    rw [hT.1,LinearEquiv.symm_apply_apply]
  · intro y v
    let z := decoder U.report (bank J U T r) y - outer J r t v
    have hz : receive J U T r t y - v = (J (t*r) d).symm (J r d z) := by
      simp [receive,outer,z,map_sub]
    calc
      ‖receive J U T r t y-v‖ = ‖(J (t*r) d).symm (J r d z)‖ := congrArg norm hz
      _ ≤ K*t^(-(d:ℝ)-ε)*‖z‖ := by simpa only [LinearEquiv.symm_apply_apply] using he (J r d z)
      _ ≤ K*t^(-(d:ℝ)-ε)*((2*‖U.report.toContinuousLinearMap‖)*‖y-read J U T r t v‖) :=
        mul_le_mul_of_nonneg_left (hT.2 y (outer J r t v))
          (mul_nonneg hK (Real.rpow_nonneg ht.le _))
      _ = _ := by ring

/-- Simultaneous on the selected continuum and its own cofinal true Wilson samples.
At either regulator the ratio can be selected *after* the outer window has been paid. -/
theorem priced_windows (F : Final C q S) (H : Leading F J) (hS : Services C q S)
    (ε : ℝ) (hε : 0<ε) :
    ∃ K : ℝ, 0≤K ∧ ∀ᶠ r in trail,
      (∀ t∈Ioc (0:ℝ) 1, invoice J U S r t ε K) ∧
      ∀ᶠ a : ℕ × ℕ in q.fuse, ∀ t∈Ioc (0:ℝ) 1,
        invoice J U (StressFlux.Matching.rounded C a.1 a.2) r t ε K := by
  obtain ⟨K,hK,he⟩ := WilsonPhysicalExteriorFrame.between F d J H ε hε
  obtain ⟨hc,hf⟩ := portfolio F J H hS U
  have hK₀ := zero_le_one.trans hK
  refine ⟨K*(2*‖U.report.toContinuousLinearMap‖),by positivity,?_⟩
  filter_upwards [he,hc,hf] with r hr h₁ h₂
  constructor
  · exact fun t ht => at_measure J U r t ε K hK₀ S (hr t ht) h₁ ht.1
  · filter_upwards [h₂] with a ha
    exact fun t ht => at_measure J U r t ε K hK₀ _ (hr t ht) ha ht.1

/-- Apply to the signed difference between an independently measured product and its
chosen finite horizon field, before division by the physical detector. -/
theorem omitted (T : Table C.book) (r t ε ζ K B : ℝ) (ht : 0 < t) (hK : 0 ≤ K)
    (h : invoice J U T r t ε K) (y : Fin U.size → ℂ) (v : E C.labels d)
    (hs : ‖y-read J U T r t v‖ ≤ B*t^((d:ℝ)+ζ)) :
    ‖receive J U T r t y-v‖ ≤ (K*B)*t^(ζ-ε) := by
  apply (h.2 y v).trans
  calc
    _ ≤ K*t^(-(d:ℝ)-ε)*(B*t^((d:ℝ)+ζ)) :=
      mul_le_mul_of_nonneg_left hs (mul_nonneg hK (Real.rpow_nonneg ht.le _))
    _ = K*B*(t^(-(d:ℝ)-ε)*t^((d:ℝ)+ζ)) := by ring
    _ = _ := by rw [←Real.rpow_add ht]; congr 2; ring

end YM.Integration.WilsonPhysicalExteriorDetector
