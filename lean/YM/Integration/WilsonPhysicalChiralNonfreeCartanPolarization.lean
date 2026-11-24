import YM.Integration.WilsonPhysicalChiralNonfreeCartanPart

/-! Evaluate the returned signed direction before taking any absolute
coefficient prices, in the physical filtered basis. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPhysicalChiralNonfreeCartanPolarization
open Finset RG Labels Wilson Source Lattice Next.Rank Next.Rank.Price Next.Rank.Atlas
open Further.CorrectedLift Cells Extraction Table Climb Trace Trace.Pilot
open WilsonPositionThermometerGradedSource Spec OPE OPE.Orbits RG17 PhysMS PhysMS.Frame
open Maxwell XSpace XSpace.Normalize Maxwell.Free ProjectorNext.Calibration
open WilsonPhysicalChiralNonfreeCurvatureTest Tensor Analysis
open scoped Classical BigOperators Topology
variable {G:Gauge}{d:ℕ}

def panel (X:Fin 3→PositionX.Tri.PanelL G):Label G d→ₗ[ℂ] ℂ:=
  ∑ S:Finset (Fin 3),(-1:ℂ)^(3-S.card) •
    ((Labels.read (PositionX.Tri.chunk (chart X S))).toLinearMap.comp (localFields G d).subtype)

theorem evaluated (X:Fin 3→PositionX.Tri.PanelL G)(v:Label G d):
    panel X v=∑ S:Finset (Fin 3),(-1:ℂ)^(3-S.card)*Labels.read (PositionX.Tri.chunk (chart X S)) v.val:=by
  simp [panel,LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul]

theorem pricedPart (F:Labels.Frame G d)(X:Fin 3→PositionX.Tri.PanelL G)(u:F.Coeff):
    reading F X u=panel X (gradePart (d,d/2) (F.coords.symm u)):=by
  have hf : ∑ i:F.Index,u i • F.basis i = F.coords.symm u := by
    convert F.basis.sum_repr (F.coords.symm u) using 1
    apply sum_congr rfl; intro i _
    rw [show F.basis.repr (F.coords.symm u) i=u i from congrFun (F.coords.apply_symm_apply u) i]
  rw [←hf,map_sum,map_sum,WilsonPhysicalChiralNonfreeCurvatureTest.reading]
  apply sum_congr rfl; intro i _
  rcases eq_or_ne (F.grades i) (d,d/2) with h|h
  · rw [if_pos h,map_smul,←h,gradePart_self _ _ (F.pure i),map_smul,evaluated,ear,smul_eq_mul,mul_comm]
  · rw [if_neg h,map_smul,gradePart_zero _ _ _ h.symm (F.pure i),smul_zero,map_zero]

theorem named (C:Family G)(s:Rose.Badge)(i:Fin 3)(hi:i∈s)(X:Fin 3→PositionX.Tri.PanelL G):
    ∃T:Finset (Fin 3)→Maxwell.TaylorTower G,
      (∀S,(fun n=>gaugeJet (T S n))=PositionX.Tri.chunk (chart X S)) ∧
      reading (C.labels.level (grade i)) X (ladder C (grade i) (source C s i))=
        ∑S:Finset (Fin 3),(-1:ℂ)^(3-S.card)*Maxwell.probe (T S) (base G i).val:=by
  choose T placed signed using fun S:Finset (Fin 3)=>
    WilsonPhysicalChiralNonfreeCartanPart.MaxwellTest C s i hi (chart X S)
  exact ⟨T,placed,by rw [pricedPart,evaluated]; exact sum_congr rfl fun S _=>congrArg _ (signed S)⟩

end YM.Integration.WilsonPhysicalChiralNonfreeCartanPolarization
