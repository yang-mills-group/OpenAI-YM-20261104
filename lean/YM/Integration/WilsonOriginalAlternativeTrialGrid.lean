import YM.Integration.WilsonOriginalAlternativeTrialTravel
import YM.Integration.WilsonMeasuredPublicEntranceGridDebit

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalAlternativeTrialGrid
open Finset Lattice Wilson RG Source Labels Extra.Histories Marker QuadraticLocal.Affinity
open PhysicalNext.Repeat.Legato WilsonMeasuredPublicEntranceGridDebit
open WilsonPositionProgramOriginalBlockedTrial WilsonAddressedRestartedColumn
open WilsonOriginalNullCorridor
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G) {I:Type} [DecidableEq I] [Fintype I] (d:I→ℕ) (N p f n:ℕ)
  (o:I→Site (R.family.side f p)) (v:∀i,R.family.label (d i))
local notation "K_" => f+n
def pins (j:I) := (R.family.S.toDepth (Nat.le_add_right f n) p).embed (o j)
def factor (j:I) : ℂ := ((R.family.S.a K_:ℂ)^(d j))⁻¹
local notation "arm_" => WilsonOriginalAlternativeTrialSource.arm R d N p K_ (pins R p f n o) v (factor R d f n)

omit [Fintype I] [DecidableEq I] in
theorem guard (j:I):
    (arm_ j)=trial R (d j) f n N p (o j) (v j):=rfl

local notation "P_" => R.family.path.rep N p f
/-- The original fitted public scalar and the guarded source enrolled on the
second carrier are compared on the same held field, with each hard census on
its own representation. -/
theorem dual {grade j:ℕ} {high:f+n≤N} (A:R.family.label grade≃ₗ[ℂ]R.family.label grade)
    (Y:R.family.label grade) (y:Site (R.family.side f p)) (W:Rep G (R.family.side f p))
    (quiet:W.eval=(P_).eval)
    (landed:settled R grade j f n N p high A Y y)
    (q:Coefficient (R.family.labels.level grade) (R.family.side f p))
    (issued:∀U,q.density y (R.family.localSection grade) W U=W.eval U •
      actualTransport R.family (N:=N)
        (trial R grade f n N p y (A.symm (fitted R grade j N p Y))) (Nat.le_add_right f n) U):
    let w:=A.symm (fitted R grade j N p Y)
    let κ:=bill R grade (f+n) f w
    ∃ h:Coefficient (R.family.labels.level grade) (R.family.side f p),
      WilsonAddressedRestartedFiled.Filed R grade N p f y
        (track R grade N p (f+n) (numerator R grade N p (f+n) 0 w) f-
          Trace.Physical.GermGraph.calValues (C:=R.family) grade N p f ((R.family.factory grade N p).terminal.symm Y)) κ h ∧
      ∀U,(W.eval U:ℂ)*actualTransport R.family (N:=N) (named R grade f N p (by omega) y Y) (by omega) U=
        q.density y (R.family.localSection grade) W U-
          h.density y (R.family.localSection grade) (P_) U/((R.family.S.a f:ℂ)^grade):=by
  intro w κ
  obtain ⟨h,paid,eq⟩:=landed
  refine ⟨h,paid,fun U=>?_⟩
  rw [issued U,quiet,Complex.real_smul]
  have signed:=eq U
  have nz:((P_).eval U:ℂ)≠0:=by exact_mod_cast (Multi.AxisShift.chosen_positive R.makes.wilson (by omega:f≤N) U).ne'
  have az:((R.family.S.a f:ℂ)^grade)≠0:=pow_ne_zero _ (by exact_mod_cast (R.family.S.a_pos f).ne')
  field_simp [nz,az] at signed ⊢
  linear_combination signed

end YM.Integration.WilsonOriginalAlternativeTrialGrid
