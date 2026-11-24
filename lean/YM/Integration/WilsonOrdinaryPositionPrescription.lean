import YM.Integration.WilsonOrdinaryWardPivot
import YM.Integration.WilsonOrdinaryWardGenerator

/-! A genuinely rotation-, unit-, reality- and grade-compatible position
frame on the original interacting continuum before all perturbation orders.
The matrix conditions measure every allowed real top-grade field change. -/
noncomputable section
namespace YM.Integration.WilsonOrdinaryPositionPrescription
open Function Filter Matrix Pert Pert.Position MS MS.Theater MS.Menus MS.Land MS.Local.Physical
open FVA2 FVA2.ColorCode Extra.FD OPE.Levy RG11.Fields Table Spec Climb PhysMS Maxwell Trace.Pilot
open Extra.WeakScaling WilsonOrdinaryWardSpace
open scoped Topology Classical BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
  (B : Deck G) {O : Booked B} (M : MS_Data G O) (F : Final C f S)
  (J : ℝ→PhysMS.tower S) (H : (Bel C.book).Hierarchy)
  (g : ℕ→Test 2) (μ : ℕ→ℝ) (γ : ℝ→ℝ)

def trial (r : ℝ) : PhysMS.tower S := fun d=>WilsonOrdinaryWardPivot.field B M F J d (g d) (μ d) H γ r
def positioned (r : ℝ) : PhysMS.tower S := PhysMS.Frame.compatible F (trial B M F J H g μ γ r)

variable (hG : G.Simple) (L : PhysMS.Leading F J)
  (live : ∀d,IsUnit (MSSeparatedTestGram.matrix M d (μ d) 0 (g d))) (hγ : Coupling G γ)
  (original : ∀d,∀ᶠ r in trail,PhysMS.Frame.obedient F H (J r) d)

include hG L live hγ in
theorem adjacent : PhysMS.Frame.Adjacent F (trial B M F J H g μ γ) trail := by
  apply PhysMS.Frame.neighboring (X:=J) F
  · intro d v
    apply (tendsto_const_nhds (x:=(Free.scheme C.labels).rise (Nat.le_succ d) v)).congr'
    filter_upwards [L.raised (Nat.le_succ d)] with r he
    rw [←he v,LinearEquiv.symm_apply_apply]
  · intro d v
    exact WilsonOrdinaryWardPivot.relative B M F J d (g d) (μ d) H γ L hG (live d) hγ v

include hG L live hγ original in
theorem symmetries (d : ℕ) : ∀ᶠ r in trail,PhysMS.Frame.obedient F H (positioned B M F J H g μ γ r) d := by
  apply PhysMS.Frame.plan_angle F hG H (adjacent B M F J H g μ γ hG L live hγ)
  intro e
  filter_upwards [original e,WilsonOrdinaryWardPivot.paid B M F J e (g e) (μ e) H γ L hG (live e) hγ] with r old tested
  exact WilsonOrdinaryWardSpace.physical C B e H F (J r) (trial B M F J H g μ γ r) old
    (WilsonOrdinaryWardPivot.change B M F J e (g e) (μ e) H γ r) tested

include hG L live hγ in
theorem relative (d : ℕ) (v : (Bel C.book).Field d) :
    Tendsto (fun r=>(J r d).symm (positioned B M F J H g μ γ r d v)) trail (𝓝 v) := by
  let A := trial B M F J H g μ γ
  have first (x : (Bel C.book).Field d) : Tendsto (fun r=>(J r d).symm (A r d x)) trail (𝓝 x) :=
    WilsonOrdinaryWardPivot.relative B M F J d (g d) (μ d) H γ L hG (live d) hγ x
  have next := PhysMS.Frame.fitted_up F (adjacent B M F J H g μ γ hG L live hγ) d v
  let U (r : ℝ) := ((J r d).symm.toLinearMap.comp (A r d).toLinearMap)
  apply (Dash.arcing (Dash.fit_plane U LinearMap.id first) next).congr
  intro r
  change (J r d).symm ((A r d) ((A r d).symm (positioned B M F J H g μ γ r d v))) = _
  rw [LinearEquiv.apply_symm_apply]

include hG L live hγ original in
/-- All four original leading requirements: exact symmetry, exact grade
inclusions, exact vacuum, and the full uniform position-jet limit at all
arities. Its test profile, physical continuum and MS program are fixed. -/
theorem leading : PhysMS.Leading F (positioned B M F J H g μ γ) := by
  constructor
  · intro d
    exact (symmetries B M F J H g μ γ hG L live hγ original d).mono (fun _ hh=>PhysMS.Frame.obedient_realH F hG H hh)
  · intro d e he
    exact PhysMS.Frame.accounted F d e he (adjacent B M F J H g μ γ hG L live hγ)
  · intro d
    exact (symmetries B M F J H g μ γ hG L live hγ original d).mono (fun _ hh=>hh.unit)
  · intro n d v j K hc within
    let w : ℝ→MaxwellSlots C d := fun r i=>(J r (d i)).symm (positioned B M F J H g μ γ r (d i) (v i))
    have small (i) : Tendsto (fun r=>w r i) trail (𝓝 (v i)) :=
      relative B M F J H g μ γ hG L live hγ (d i) (v i)
    have pos : ∀ᶠ r : ℝ in trail,0<r := self_mem_nhdsWithin
    have got := PhysMS.Frame.measured_tensor (v:=fun _=>none) (P:=J) (r:=fun r : ℝ=>r) F pos d j
      (fun i=>WilsonMacroscopicRichFree.basis C B (d i)) hc within
      (fun y=>L.lead n d (fun i=>WilsonMacroscopicRichFree.basis C B (d i) (y i)) j K hc within) small
    have same (r : ℝ) : PhysMS.measured F none (J r) (w r) r=PhysMS.measured F none (positioned B M F J H g μ γ r) v r := by
      funext x;unfold PhysMS.measured w;simp only [LinearEquiv.apply_symm_apply]
    simpa only [same] using got

end YM.Integration.WilsonOrdinaryPositionPrescription
end

