import YM.Integration.OPEScalarAsymptotic
import YM.Integration.OPEScalarOutput

/-! The entire measured scalar output field has an ordinary MS expansion
through a fixed order exactly when the original complete marked correlation
has that expansion. Both estimates use one tail for all points of the
selected compact and every phase, in the calibrated running coupling. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.OPEScalarFieldAsymptotic
open Filter Set FVA2 PhysMS Spec OPE OPE.Orbits Trace.Pilot Trace.Sundial
open Pert.Position Maxwell OPEScalarAsymptotic
open scoped Classical Topology

variable {G : Gauge} {n i : ℕ}

def estimates {U P : Type*} [SeminormedAddCommGroup U] (K : Set (Points n))
    (g : ℝ → ℝ) (N : ℕ) (a b : ℝ → Points n → P → U) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ r in trail, ∀ x ∈ K, ∀ p, ‖a r x p-b r x p‖ ≤ ε*(g r)^N

theorem lift_iff {U P : Type*} [NormedAddCommGroup U] [NormedSpace ℂ U] (z : U) (hz : z ≠ 0)
    {K : Set (Points n)} {g : ℝ → ℝ} {N : ℕ} (a b : ℝ → Points n → P → ℂ) :
    estimates K g N (fun r x p => a r x p • z) (fun r x p => b r x p • z) ↔ fits K g N a b := by
  have hu := norm_pos_iff.mpr hz
  constructor
  · intro h ε hε
    filter_upwards [h (ε*‖z‖) (mul_pos hε hu)] with r hr x hx p
    have h := hr x hx p
    rw [← sub_smul,norm_smul,mul_right_comm ε] at h
    exact (mul_le_mul_iff_left₀ hu).mp h
  intro h ε hε
  filter_upwards [h (ε/‖z‖) (div_pos hε hu)] with r hr x hx p
  rw [← sub_smul,norm_smul]
  calc
    _ ≤ (ε/‖z‖*(g r)^N)*‖z‖ := mul_le_mul_of_nonneg_right (hr x hx p) hu.le
    _ = _ := by field_simp [hu.ne']

variable {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (R : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J : ℝ → PhysMS.tower S) (hJ : Leading F J) (hG : G.Simple) (X : Climb.Scaling S)
    (hR : Foundation F R) (v : Fin n → E C.labels i) (K : Set (Points n))
    (hK : IsCompact K) (hsep : K ⊆ conf n)

theorem unit_nonzero : (Climb.Bel C.book).unit 0 ≠ 0 := by
  intro he
  have h := congrArg (Extra.FD.writes C.labels 0) he
  rw [Extra.FD.writes_unit,map_zero] at h
  exact one_ne_zero h

def observed (r : ℝ) (x : Points n) (_ : Viewers F) :=
  PhysicalMSOPECandidate.actualOutput (D := 0) F R J v r (r • x).ofLp

include hJ hG X in
theorem packet_iff (g : ℝ → ℝ) (N : ℕ) (b : ℝ → Points n → Viewers F → ℂ) :
    estimates K g N (observed F R J v) (fun r x p => b r x p • (Climb.Bel C.book).unit 0) ↔
      fits K g N (scalar F R J v) b := by
  rw [← lift_iff ((Climb.Bel C.book).unit 0) (unit_nonzero (C := C)) (scalar F R J v) b]
  have he := OPEScalarOutput.packet F R J hJ hG X
  constructor
  · intro h ε hε
    filter_upwards [h ε hε,he] with r hr he x hx p
    change ‖Short.scalar F R (r • x).ofLp (tags (Frame.born J r v)) 0 • (Climb.Bel C.book).unit 0 -
      b r x p • (Climb.Bel C.book).unit 0‖ ≤ ε*(g r)^N
    rw [← he n i v (r • x).ofLp]
    exact hr x hx p
  intro h ε hε
  filter_upwards [h ε hε,he] with r hr he x hx p
  rw [observed,he n i v (r • x).ofLp]
  exact hr x hx p

include hJ hG X hR hK hsep

theorem measured_iff {g : ℝ → ℝ} (hg : Coupling G g) (N : ℕ)
    (b : ℝ → Points n → Viewers F → ℂ) :
    estimates K g N (observed F R J v) (fun r x p => b r x p • (Climb.Bel C.book).unit 0) ↔
      fits K g N (full F J v) b :=
  (packet_iff F R J hJ hG X v K g N b).trans
    (equivalent F R J hJ hG X hR v K hK hsep hg N b)

theorem selected (hC : C.Makes) (hV : ∀ a, Bid.pop (C.localSection a))
    {B : MS.Land.Booked (ColorCode.wings G)} (M : MS.Land.MS_Data G B) (μ : ℝ)
    {k : ℝ} (T : PositionX.Bend.Booth k C.labels)
    (W : Pic.pass (Atoll.share C hC hV) hG M T)
    {H : (Climb.Bel C.book).Hierarchy} {Z : Trace.Terrace.Arch C}
    {P P' : ℝ → Spin.change S 4} {a d e : ℝ → ℝ}
    (hf : Trace.Target.FieldComparison F H Z P P' a d e) (j N : ℕ) :
    let V := Atoll.share C hC hV
    let g := fun r => OPETraceCoupling.finiteCoupling (Forge.transfer V M T μ W) j (glo P' r)
    let target := fun r x (_ : Viewers F) => truncation V M μ g N v r x
    estimates K g N (observed F R J v)
      (fun r x p => target r x p • (Climb.Bel C.book).unit 0) ↔
      fits K g N (full F J v) target :=
  measured_iff F R J hJ hG X hR v K hK hsep
    (OPETraceCoupling.selected_trace hC hV M T μ hG W hf j).1 N _

end YM.Integration.OPEScalarFieldAsymptotic
end
