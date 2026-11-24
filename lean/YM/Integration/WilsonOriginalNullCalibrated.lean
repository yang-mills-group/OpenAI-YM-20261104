import YM.Integration.WilsonOriginalNullPhysicalHistory
import YM.Trace.Physicalv2.GermGraph

/-! The emitted original local primary splits on canonical P into its own
complete, physically normalized field and a genuine canonical-P null source. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalNullCalibrated
open Function Filter MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Relay
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext Repeat Legato Graces Roost Org Push.Local
open scoped Classical BigOperators Topology Matrix.Norms.Frobenius
variable {G:Gauge}

theorem raw_page {d:ℕ} {n:Side} (F:Frame G d) (A:Hol G) (P:Rep G n) (o:Site n)
    (α:F.Coeff) (dw:d≤P.p.order) (pw:d≤P.p.power) :
    projection F A P.p.threshold o (primary o α)=α := by
  have bound:‖projection F A P.p.threshold o (primary o α)-α‖≤0:=by
    have h:=(germ_close F A).choose_spec.2 P (primary o α) (primary_format (H:=A) α)
      (primary_rem α (show 0<(1:ℝ) from zero_lt_one)) dw pw
    rw [show (Extra.Histories.primary o α).x=α by rfl,mul_zero] at h;exact h
  exact sub_eq_zero.mp (norm_le_zero_iff.mp bound)

variable (C:Family G) (d N p i:ℕ)
local notation "F₀" => C.labels.level d
local notation "P₀" => C.path.rep N p i

theorem aligned (H:C.Makes) (home:Opened C d i p) (live:i≤N) (α:C.label d) :
    let x:=(fitting d N p i H home live).symm α
    ∃ z:Coefficient F₀ (C.side i p),
      reads (C:=C) d N p i z (2*stock C i*(F₀).coeffSize α) ∧ page (C:=C) d p i z=0 ∧
      (primary (0:Site (C.side i p)) α).density 0 (C.localSection d) P₀ =
        value (C:=C) d N p i z+calValues (C:=C) d N p i x := by
  intro x
  let Y := (C.factory d N p).entries i x
  let fee := 2*stock C i*(F₀).coeffSize α
  obtain ⟨dw,pw⟩:=dimensions d N p i H home.post live
  have fit: fitting d N p i H home live x=α:=(fitting d N p i H home live).apply_symm_apply α
  have one : reads (C:=C) d N p i Y fee:=by
    have quotation:=graph_cost d N p i H home live x;rw [fit] at quotation;exact quotation
  have vac := (H.wilson.represents N p i live).vac
  have pageY:projection F₀ C.params (P₀).p.threshold 0 Y=α := by
    rw [vac];exact (fitting_apply d N p i H home live x).symm.trans fit
  have aligned : projection F₀ C.params (P₀).p.threshold 0 Y=
      projection F₀ C.params (P₀).p.threshold 0 (primary 0 α) := pageY.trans (raw_page F₀ C.params P₀ 0 α dw pw).symm
  have κpos:0 < safety C i:=Real.sqrt_pos.mpr (Real.exp_pos _)
  obtain ⟨z,shaped,paid,null,reader⟩:=WilsonOriginalNullColumnSplit.original C.params (C.localSection d)
    P₀ 0 (primary 0 α) Y (H.wilson.represents N p i live).good dw pw (primary_format α) (primary_rem α κpos)
      one.1 one.2 aligned
  refine ⟨z,⟨shaped,by simpa only [zero_add] using paid⟩,?_,funext reader⟩
  change projection F₀ C.params (plank C i).threshold 0 z=0
  rw [vac] at null;exact null

end YM.Integration.WilsonOriginalNullCalibrated
