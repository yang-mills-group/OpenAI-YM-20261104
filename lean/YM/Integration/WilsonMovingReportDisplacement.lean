import YM.Integration.WilsonMovingReportLedger
import YM.Integration.WilsonReportPrescribedFrame
import YM.Pier.Blocks.Plate

/-! The signed difference of two genuinely registered finite Wilson moments
on the moving observation scale. The spatial price is measured in units
of the true inner radius.  The two cutoff positions can vary separately. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMovingReportDisplacement
open Function Filter Set Metric MeasureTheory Lattice Wilson RG Source Extraction Spec
open PhysicalNext.Repeat.Legato RG17 FullVolume Table Climb
open scoped Classical BigOperators Topology ContDiff
variable {G : Gauge} (R : Run G) (hG : G.Simple) {n : ℕ}
    {f : Extraction.Order} {S : Table R.family.book} {F : Spec.Final R.family f S}

def read (L : Layout F) (r : ℝ) (d : Caps n) (w : R.family.book.Vector d)
    (i : ℕ×ℕ) (z : Positions n) : ℂ :=
  R.family.numeric i.1 i.2 (fun j=>⟨d j,atRef L (d j) r i (w j)⟩) (wrap _ ∘ z)

include hG in
theorem purchased (L : Layout F) (J : ℝ→PhysMS.tower S) (H : PhysMS.Leading F J)
    {B : (Bel R.family.book).Hierarchy}
    (sheaf : ∀ d : ℕ, ∀ᶠ r in Trace.Pilot.trail,PhysMS.Frame.obedient F B (J r) d)
    (d : Caps n) (K : Set (Points n)) (hk : IsCompact K) (sep : K ⊆ conf n) :
    ∃ M a : ℝ,0<M ∧ 0<a ∧ ∀ᶠ r in Trace.Pilot.trail, 0<r →
      ∀ (v : (j:Fin n)→RG17.Free R.family (d j)) (w : R.family.book.Vector d),
      (∀ j,R.family.ref (d j)≤L.level r) → (∀ j,master L (d j) r (w j)=J r (d j) (v j)) →
      ∀ ε : ℝ,0<ε → ∀ᶠ i : ℕ×ℕ in L.lens,
        ∀ x∈K,∀ y : Points n,‖y-x‖≤a → ∀ z z' : Positions n,
          tag (R.family.S.a i.1) z=r • x → tag (R.family.S.a i.1) z'=r • y →
          ‖read R L r d w i z'-read R L r d w i z‖ < 2*ε+M*(∏ j,‖v j‖)*‖y-x‖ := by
  have P := WilsonReportPrescribedFrame.present F J H sheaf
  obtain ⟨M,c,hM,hc,paid⟩ := P.confines d K hk sep
  obtain ⟨b,hb,hW⟩ := hk.exists_cthickening_subset_open (conf_open n) sep
  have hU : IsCompact (cthickening b K) := hk.cthickening
  refine ⟨M,min c b,hM,lt_min hc hb,?_⟩
  filter_upwards [paid] with r sale hr v w ref labels ε he
  let A := (fun x : Points n => r • x) '' (cthickening b K)
  have ca : IsCompact A := hU.image (continuous_const_smul r)
  have sa : A ⊆ conf n := by
    rintro _ ⟨z,hz,rfl⟩; exact Work.A04.scale_conf r hr (hW hz)
  have fields := WilsonMovingReportLedger.original R hG L r d w ref A ca sa ε he
  filter_upwards [fields] with i regulator x hx y hh z z' hz hz'
  have hidden : y ∈ cthickening b K :=
    mem_cthickening_of_dist_le y x b K hx (by rw [dist_eq_norm]; exact hh.trans (min_le_right _ _))
  have xs : r • x ∈ A := ⟨x,mem_cthickening_of_dist_le x x b K hx (by simpa using hb.le),rfl⟩
  have ys : r • y ∈ A := ⟨y,hidden,rfl⟩
  have dx := regulator z (by rw [hz]; exact xs)
  have dy := regulator z' (by rw [hz']; exact ys)
  let value (u : Points n) := S.classMoment S d (r • u) (fun j=>J r (d j) (v j))
  have labels' : (fun j=>master L (d j) r (w j)) = (fun j=>J r (d j) (v j)) := funext labels
  rw [hz,labels'] at dx; rw [hz',labels'] at dy
  change dist (read R L r d w i z) (value x)<ε at dx
  change dist (read R L r d w i z') (value y)<ε at dy
  have diff : dist (value y) (value x) ≤ M*(∏ j,‖v j‖)*‖y-x‖ := by
    rw [dist_eq_norm]; exact (sale x hx y (hh.trans (min_le_left _ _))).2 v
  rw [←dist_eq_norm]
  have h₁:=dist_triangle (read R L r d w i z') (value y) (value x)
  have h₂:=dist_triangle (read R L r d w i z') (value x) (read R L r d w i z)
  rw [dist_comm (value x) (read R L r d w i z)] at h₂
  linarith only [dx,dy,diff,h₁,h₂]

end YM.Integration.WilsonMovingReportDisplacement
