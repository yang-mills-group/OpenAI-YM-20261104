import YM.Integration.WilsonOriginalNullFiledStep

/-! A finite sequence of the actual engineering-weighted Wilson conditional
integrals. The local-primary deposits are integrated on their own dates. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalNullCorridor
open Function Filter MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Relay
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext Repeat Legato Graces Roost Org Push.Local
open scoped Classical BigOperators Topology Matrix.Norms.Frobenius
variable {G:Gauge} (C:Family G) (d N p b:ℕ)

def flow : (n:ℕ) → (Config G (C.side (b+n) p) → ℂ) → Config G (C.side b p) → ℂ
  | 0,f=>f
  | n+1,f=>flow n (GermGraph.transition (C:=C) d N p (b+n) f)

theorem integrable {j:ℕ} {f:Config G (C.side (j+1) p)→ℂ} (hf:Integrable f (prior G _)) :
    Integrable (GermGraph.transition (C:=C) d N p j f) (prior G _) := by
  exact ((C.path.levels.clock.op j p).push_integrable (C.path.levels.transition_mass j p (C.path.β N p (j+1)))
    _ hf).const_mul _

theorem flow_add (n:ℕ) (f h:Config G (C.side (b+n) p) → ℂ)
    (hf:Integrable f (prior G _)) (hh:Integrable h (prior G _)) :
    flow C d N p b n (f+h)=flow C d N p b n f+flow C d N p b n h := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [flow]
    rw [GermGraph.transition_add (C:=C) (i:=b+n) d N p hf hh]
    exact ih _ _ (integrable C d N p hf) (integrable C d N p hh)

def gain (j t:ℕ) : ℝ := Real.exp (-(1/8:ℝ)*(C.S.scale t-C.S.scale j))

theorem gain_step (j t:ℕ) :
    gain C j (t+1)=gain C j t*((C.S.block t).val:ℝ)^(-(1/8:ℝ)) := by
  have good:0 < ((C.S.block t).val:ℝ):=zero_lt_one.trans_le (GermGraph.factor_positive C t).le
  rw [gain,Schedule.scale_succ,gain,Real.rpow_def_of_pos good,←Real.exp_add]
  congr 1;ring

theorem gain_self (i:ℕ) : gain C i i=1 := by simp [gain]

end YM.Integration.WilsonOriginalNullCorridor
