import YM.Integration.WilsonOffsetIntervalDensity
import YM.Integration.WilsonReportForwardTransfer

/-! The signed charged offset, normalized on the original running coarse
field; its sole microscopic numerator retains both of the actual sites. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOffsetPosteriorInterval
open Function MeasureTheory Lattice Wilson RG Source Push.GridApprox RG16.Literal OPE.Therm
open Extraction WilsonTranslatedFactory WilsonOffsetTraceHistory WilsonOffsetIntervalDensity
open scoped Classical
variable {G : Gauge} {C : Family G} (H : C.Makes) {d N p k : ℕ}

def physicalPair (hk : k ≤ N) (y : Site (C.side k p)) (x : C.label d) (o : Site (C.side N p)) :=
  C.O N p x o-C.O N p x (anchor C.S p hk y)

def read (hk : k ≤ N) (y : Site (C.side k p)) (x : C.label d) (o : Site (C.side N p))
    (U : Config G (C.side k p)) : ℂ :=
  (credit C N p d (C.O N p x o) k hk U-material H hk y ((C.factory d N p).terminal.symm x) U)/
    ((C.S.a k:ℂ)^d*((C.path.rep N p k).eval U:ℂ))

include H in
private theorem weighted {X : Cut C N p} :
    WilsonReportForwardTransfer.weighted (C:=C) (N:=N) X =
      fun U => (bare (C.beta N p) U:ℂ)*(((partition G (C.side N p) (C.beta N p):ℝ):ℂ)⁻¹ • X) U := by
  funext U; unfold WilsonReportForwardTransfer.weighted dose
  rw [(H.wilson.starts N p).2,Complex.ofReal_div]
  simp only [Pi.smul_apply,smul_eq_mul,div_eq_mul_inv,mul_assoc]

private theorem scaled_push (hk : k ≤ N) (X : Cut C N p) (cx : Continuous X)
    (c : ℂ) (V : Config G (C.side k p)) :
    pushTo C.path N p hk (fun U => (bare (C.beta N p) U:ℂ)*(c • X) U) V =
    c*pushTo C.path N p hk (fun U => (bare (C.beta N p) U:ℂ)*X U) V := by
  have h := IntrinsicProductLinearity.credit_sum C N p 0 k hk (fun _:Unit => c) (fun _:Unit => X) (fun _ => cx)
  simpa [credit] using congrFun h V

theorem original (hr : C.ref d ≤ k) (hk : k ≤ N) (y : Site (C.side k p)) (x : C.label d)
    (o : Site (C.side N p)) :
    read H hk y x o = WilsonReportForwardTransfer.exterior (N:=N) hk (physicalPair hk y x o) := by
  let X := physicalPair hk y x o
  have cx : Continuous X := (C.continuousO N p d x o).sub (C.continuousO N p d x _)
  funext U
  have same := congrFun (WilsonOffsetIntervalDensity.physical H hr hk y o x) U
  change (credit C N p d (C.O N p x o) k hk U-material H hk y ((C.factory d N p).terminal.symm x) U) =
    credit C N p d X k hk U at same
  unfold read; rw [same]
  change _ = WilsonReportForwardTransfer.exterior (N:=N) hk X U
  unfold WilsonReportForwardTransfer.exterior; rw [weighted H,scaled_push hk X cx]
  unfold credit dose
  have bank : ((partition G (C.side N p) (C.beta N p):ℝ):ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (partition_pos _).ne'
  have a : (C.S.a k:ℂ)^d ≠ 0 := pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (C.S.a_pos k).ne')
  have u : ((C.path.rep N p k).eval U:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (SectorNext.Vacuum.strictly C.path H.wilson N p k hk U).ne'
  simp only [Pi.smul_apply,smul_eq_mul,Complex.ofReal_div]
  change _ = _/(((C.path.rep N p k).eval U:ℂ)/((partition G (C.side N p) (C.beta N p):ℝ):ℂ))
  field_simp

theorem price (hr : C.ref d ≤ k) (hk : k ≤ N) (y : Site (C.side k p)) (x : C.label d)
    (o : Site (C.side N p)) :
    Integrable (read H hk y x o) (scene C.path N p k) ∧
      (∫ U, ‖read H hk y x o U‖ ∂scene C.path N p k) ≤
        ∫ U, ‖physicalPair hk y x o U‖ ∂law G (C.side N p) (C.beta N p) := by
  rw [original H hr hk y x o,← WilsonReportForwardTransfer.top H N p]
  apply WilsonReportForwardTransfer.contract H hk (le_refl N)
  letI : IsProbabilityMeasure (scene C.path N p N) := probability H.wilson (le_refl N)
  exact ((C.continuousO N p d x o).sub (C.continuousO N p d x _)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

end YM.Integration.WilsonOffsetPosteriorInterval
