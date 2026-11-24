import YM.Integration.WilsonPositionOriginalDressedQFourTerms
import YM.Integration.QLocalPhysicalPathKernel

/-! The signed upper Q in the two-clock assay is the conditional read on
the original Markov fibre, at every coarse field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionOriginalDressedQFibre
open Lattice Wilson RG MeasureTheory OPE.Therm PhysicalNext.Repeat.Legato Push.GridApprox
open WilsonMacroscopicForwardTransfer QLocalPhysicalPathKernel
open scoped Classical
variable {G:Gauge}(R:Run G){N per i:ℕ}

theorem measured (live:i<N)(Q:Config G (R.family.side (i+1) per)→ℂ)
    (W:Config G (R.family.side i per)):
    (∫U,Q U ∂(next R.family N per i W))=exterior (C:=R.family) (N:=N) (Nat.le_succ i) Q W:=by
  rw [held R.family R.makes live,ActualWilsonConditionalRoots.average R.family R.makes live,
    exterior,pushTo_next R.family.path N per (le_refl i),pushTo_self]
  let di:=R.family.path.rep N per i
  let Z:=partition G (R.family.side N per) (R.family.path.β N per N)
  have good:di.eval W≠0:=(Multi.AxisShift.chosen_positive R.makes.wilson live.le W).ne'
  have hp:Z≠0:=(partition_pos _).ne'
  change (∫U,actualConditionalDensity R.family N per i W U • Q U ∂prior G _)=
    (∫ U,(R.family.path.levels.clock.op i per).density (R.family.path.β N per (i+1)) U W •
      weighted (C:=R.family) (N:=N) Q U ∂prior G _)/(dose (H:=R.family.path) (p:=per) i W N:ℂ)
  rw [←integral_div]
  apply integral_congr_ae
  filter_upwards with U
  simp only [actualConditionalDensity,weighted,dose,Complex.real_smul,Complex.ofReal_div,Complex.ofReal_mul]
  change (((_ : ℂ)*_/((di.eval W):ℂ))*Q U)=(_*((_/(Z:ℂ))*_))/((di.eval W:ℂ)/(Z:ℂ))
  field_simp [Complex.ofReal_ne_zero.mpr hp,Complex.ofReal_ne_zero.mpr good]

end YM.Integration.WilsonPositionOriginalDressedQFibre
