import YM.Integration.WilsonOriginalNullPlacedLinearPanel

/-! Complex-linear hearing on the complete original finite sequence.
Only the actual incoming placement enters the operator. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalNullPlacedFlowPanel
open Function Filter Lattice RG Wilson Extra.Histories Source Labels
open Extra.Histories.Relay Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph MeasureTheory
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato RG05Readout RG05Readout.Address
open WilsonOriginalNullCorridor
open scoped Classical BigOperators Topology
variable {G:Gauge} (C:Family G) (R:Run G) (d N p b:ℕ)
local notation "C₀" => R.family

theorem scalar (n:ℕ) (a:ℂ) (f:Config G (C.side (b+n) p)→ℂ) (hf:Integrable f (prior G _)) :
    flow C d N p b n (a • f)=a • flow C d N p b n f := by
  induction n with
  | zero=>rfl
  | succ n ih=>
    have push:transition (C:=C) d N p (b+n) (a • f)=a • transition (C:=C) d N p (b+n) f:=by
      unfold transition blast
      rw [StepData.push_smul _ _ _ _ hf]
      exact smul_comm ..
    rw [flow,flow,push]
    exact ih _ (integrable C d N p hf)

def field (n:ℕ) (y:Site ((C₀).side (b+n) p)) (x:(C₀).label d) : Config G ((C₀).side b p)→ℂ :=
  flow C₀ d N p b n (calValues (C:=C₀) d N p (b+n) x ∘ Lattice.translate y)

def panel (n:ℕ) (live:b+n ≤ N) (home:Opened C₀ d (b+n) p) (y:Site ((C₀).side (b+n) p)) :
    (C₀).label d →ₗ[ℂ] (Config G ((C₀).side b p)→ℂ) where
  toFun:=field R d N p b n y
  map_add' x z:=by
    unfold field
    rw [cal_add (C:=C₀) d N p (b+n) R.makes home.post live x z]
    exact flow_add C₀ d N p b n _ _ (WilsonOriginalNullPlacedLinearPanel.tested R d live home y x)
      (WilsonOriginalNullPlacedLinearPanel.tested R d live home y z)
  map_smul' a x:=by
    have eq:calValues (C:=C₀) d N p (b+n) (a • x)=a • calValues (C:=C₀) d N p (b+n) x:=
      (WilsonMatrixOriginalGermBasis.density C₀ R.makes d N p (b+n) home.post live).map_smul a x
    unfold field;rw [eq]
    exact scalar C₀ d N p b n a _ (WilsonOriginalNullPlacedLinearPanel.tested R d live home y x)

end YM.Integration.WilsonOriginalNullPlacedFlowPanel
