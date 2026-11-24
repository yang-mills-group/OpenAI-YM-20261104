import YM.Integration.WilsonForwardMeasurable
import YM.Integration.SelectedWilsonMarginalPairing

/-! Exact normalized fine-source adjoint of the joint signed last-step comparison.
The prescribed and incoming factors retain their own genuine native fields. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonWeakStepPairing
open Function Set MeasureTheory Lattice Wilson RG Push.GridApprox OPE.Therm
open scoped BigOperators Classical
variable {G : Gauge} {C : Family G} {m N p : ℕ}
local notation "nf" => C.side (m+1) p
local notation "nc" => C.side m p
local notation "Pf" => C.path.rep N p (m+1)
local notation "Pc" => C.path.rep N p m
local notation "op" => C.path.levels.clock.op m p
local notation "b" => C.path.β N p (m+1)
local notation "μc" => scene C.path N p m
local notation "μf" => scene C.path N p (m+1)

/-- Physical adjoint of the entire signed fine input tested at coarse cutoff.
The actual positive outgoing density cancels pointwise. -/
theorem forward (hC : C.Makes) (hm : m<N) {t : Config G nc → ℂ} {g : Config G nf → ℂ}
    (ht : Envelope t) (hg : Envelope g) :
    (∫ W,actualAverage C (N:=N) g W*t W ∂μc) = ∫ U,g U*back op b t U ∂μf := by
  have hf := (Pf).envelope (hC.wilson.represents N p (m+1) hm).good
  have hkg := Push.SectorMeasure.Env.smul_L1 hf (hg.integrableC (prior G nf))
  have hadj := back_dual (C.path.levels.transition_mass m p b) ht (fun U => (Pf).eval U • g U) hkg
  have h (W) : ((Pc).eval W : ℂ)*(actualAverage C (N:=N) g W*t W) =
      ((op).push b (fun U => (Pf).eval U • g U) W)*t W := by
    have hne := Complex.ofReal_ne_zero.mpr (Multi.AxisShift.chosen_positive hC.wilson hm.le W).ne'
    rw [actualAverage_push,Complex.real_smul,Complex.ofReal_inv]
    field_simp [hne]
  rw [violet (H:=C.path) (p:=p) hC.wilson hm.le,violet (H:=C.path) (p:=p) hC.wilson hm]
  congr 1
  simpa only [h,Complex.real_smul,mul_assoc] using hadj

/-- Unchanged native Wilson adjoint of an actual coarse multiplier. -/
theorem backward (hC : C.Makes) (hm : m<N) {f : Config G nc → ℂ} (hf : Envelope f) :
    (∫ W,f W ∂μc) = ∫ U,back op b f U ∂μf := by
  have h := (retro (H:=C.path) (p:=p) hC.wilson (Nat.le_succ m) hm f hf).symm
  simpa only [backTo_next C.path N p (le_refl m),backTo_self] using h

/-- The complete registered defect has exactly this true fine signed pair.
Both adjoints of local coarse registers retain native finite reach. -/
theorem difference (hC : C.Makes) (hm : m<N) {t M : Config G nc → ℂ} {g : Config G nf → ℂ}
    (ht : Envelope t) (hM : Envelope M) (hg : Envelope g) :
    (∫ W,t W*(actualAverage C (N:=N) g W-M W) ∂μc) =
      ∫ U,g U*back op b t U-back op b (fun W=>t W*M W) U ∂μf := by
  letI : IsProbabilityMeasure μc := probability (H:=C.path) (p:=p) hC.wilson hm.le
  letI : IsProbabilityMeasure μf := probability (H:=C.path) (p:=p) hC.wilson hm
  have h1 := WilsonForwardMeasurable.average hC hm hg
  have h2 := ht.mulC hM
  have h3 := back_env (C.path.levels.transition_mass m p b) ht
  have h4 := back_env (C.path.levels.transition_mass m p b) h2
  simp only [mul_sub,mul_comm (t _) (actualAverage C (N:=N) g _)]
  rw [integral_sub ((h1.mulC ht).integrableC _) (h2.integrableC _),
    integral_sub ((hg.mulC h3).integrableC _) (h4.integrableC _),forward hC hm ht hg,backward hC hm h2]

end YM.Integration.WilsonWeakStepPairing
