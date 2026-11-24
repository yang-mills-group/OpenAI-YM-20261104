import YM.Integration.WilsonThermalReadout
import YM.Integration.WilsonWeakStepPairing

/-! The high curvature ranks in a joint original Wilson blocking step can
be removed inside the true weak response against the same coarse phase. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPairedRankCutoff
open MeasureTheory Filter Set Finset Lattice Wilson RG Marker OPE.Therm
open Comparison.Density.RenderM LocalComparison LocalComparison.MarkedPackets Push.AbsoluteSums Push.GridApprox
open WilsonThermalPacketSum WilsonThermalReadout
open scoped Classical BigOperators Topology
variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] {R : Census V}
variable {D : V → ComparisonDensity.Address.Orbit}

def rate (c cap marks : ℕ) (t δ budget : ℝ) : ℝ :=
  amplifier c cap marks budget * cost c cap marks t δ budget

section Field
variable {n : Side} {P : MarkedPackets D G n R} {p : BudgetPoint} {w : V → ℝ}
variable {g width budget : ℝ} {address : V → Support n}
variable {region : Comparison.Density.Testing.Region (fun v => (D v).Mood) n} {o d : ℕ}

theorem envelope (H : P.Paid p address region w g width budget o d) (x : IndependentTests D)
    (c cap : ℕ) (hcap : P.rankCap ≤ cap) (L : Poly R →L[ℂ] ℂ) (hL : ∀ a, ‖L a‖ ≤ Poly.price w a) :
    Envelope (fun U => L (gap P g x c U)) := by
  let K := amplifier c cap (Fintype.card V) budget
  let C := cost c cap (Fintype.card V) 2 0 budget
  have hp := at_field x H c cap hcap (1:Config G n)
  have ha := (Poly.nonnegative H.positive _).trans (H.uniform_read cap hcap x (1:Config G n)).2
  have hK : 0 ≤ K := WilsonThermalMultiplier.slope_nonneg _ (add_nonneg ha (budget_nonneg hp))
  refine ⟨L.continuous.measurable.comp (WilsonThermalReadout.measurable P g x c),K*C,fun U => ?_⟩
  exact (hL _).trans ((field x H c cap hcap U).trans
    (mul_le_mul_of_nonneg_left (at_field x H c cap hcap U).2.2 hK))
end Field

variable {C : Family G} {N m p : ℕ}
local notation "nc" => C.side m p
local notation "nf" => C.side (m+1) p
local notation "op" => C.path.levels.clock.op m p
local notation "b" => C.path.β N p (m+1)
local notation "μc" => scene C.path N p m
local notation "μf" => scene C.path N p (m+1)
variable {Pf : MarkedPackets D G (C.side (m+1) p) R} {Pc : MarkedPackets D G (C.side m p) R}
variable {dF dC : BudgetPoint} {adrF : V → Support (C.side (m+1) p)} {adrC : V → Support (C.side m p)}
variable {regF : Comparison.Density.Testing.Region (fun v => (D v).Mood) (C.side (m+1) p)}
variable {regC : Comparison.Density.Testing.Region (fun v => (D v).Mood) (C.side m p)}
variable {wF wC : V → ℝ} {gF gC widthF widthC feeF feeC : ℝ} {offF covF offC covC : ℕ}

/-- Both endpoint integrals are on the same original Run with its genuine
normalizers. The incoming test is the original positive finite-step adjoint. -/
theorem joint (hC : C.Makes) (hm : m < N)
    (fpaid : Pf.Paid dF adrF regF wF gF widthF feeF offF covF)
    (cpaid : Pc.Paid dC adrC regC wC gC widthC feeC offC covC)
    (xF xC : IndependentTests D) (c capF capC : ℕ)
    (hF : Pf.rankCap ≤ capF) (hK : Pc.rankCap ≤ capC)
    (tf δf tc δc : ℝ) (htf : 0 ≤ tf) (hdf : 0 ≤ δf) (htc : 0 ≤ tc) (hdc : 0 ≤ δc)
    (fr : ∀ z : Face (Per nf), (μf).real (trigger z tf) ≤ δf)
    (cr : ∀ z : Face (Per nc), (μc).real (trigger z tc) ≤ δc)
    (ζ : Config G nc → ℂ) (hz : Measurable ζ) (hζ : ∀ U, ‖ζ U‖ ≤ 1)
    (L : Poly R →L[ℂ] ℂ) (Lf : ∀ a, ‖L a‖ ≤ Poly.price wF a) (Lc : ∀ a, ‖L a‖ ≤ Poly.price wC a) :
    ‖∫ W, ζ W * (actualAverage C (N:=N) (fun U => L (gap Pf gF xF c U)) W -
      L (gap Pc gC xC c W)) ∂μc‖ ≤ rate c capF (Fintype.card V) tf δf feeF +
      rate c capC (Fintype.card V) tc δc feeC := by
  letI : IsProbabilityMeasure μc := probability (H:=C.path) (p:=p) hC.wilson hm.le
  letI : IsProbabilityMeasure μf := probability (H:=C.path) (p:=p) hC.wilson hm
  let f : Config G nf → ℂ := fun U => L (gap Pf gF xF c U)
  let h : Config G nc → ℂ := fun W => L (gap Pc gC xC c W)
  change ‖∫ W,ζ W * (actualAverage C (N:=N) f W-h W) ∂μc‖ ≤ _
  have Ef : Envelope f := envelope fpaid xF c capF hF L Lf
  have Eh : Envelope h := envelope cpaid xC c capC hK L Lc
  have Ez : Envelope ζ := ⟨hz,1,hζ⟩
  have Eav := WilsonForwardMeasurable.average hC hm Ef
  have Eb := back_env (C.path.levels.transition_mass m p b) Ez
  have hb (U) : ‖back op b ζ U‖ ≤ 1 := back_bound (C.path.levels.transition_mass m p b) hz 1 hζ U
  have hf := (tested xF fpaid μf c capF hF tf δf htf hdf fr (back op b ζ) Eb.meas hb L Lf).2
  have hc := (tested xC cpaid μc c capC hK tc δc htc hdc cr ζ hz hζ L Lc).2
  calc
    _ = ‖(∫ U, back op b ζ U * f U ∂μf) - (∫ W, ζ W * h W ∂μc)‖ := by
      simp only [mul_sub]
      rw [integral_sub ((Ez.mulC Eav).integrableC _) ((Ez.mulC Eh).integrableC _)]
      congr 2
      simpa only [mul_comm] using WilsonWeakStepPairing.forward hC hm Ez Ef
    _ ≤ _ := (norm_sub_le ..).trans (add_le_add hf hc)

end YM.Integration.WilsonPairedRankCutoff
end
