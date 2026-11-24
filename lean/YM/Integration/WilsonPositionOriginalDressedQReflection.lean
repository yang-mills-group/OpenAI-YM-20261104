import YM.Integration.WilsonPositionOriginalDiagnosticReflected
import YM.Integration.WilsonMacroscopicForwardTransfer
import YM.Push.GRID_APPROXIMATION.Iterate

/-! A bounded right insertion born on an aged Wilson level can be
paired with a dressed left field from the microscopic cutoff. The
physical site/bond tags and normalized noise are drawn on every step of
the backward test. Its whole support stays in the declared chamber. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionOriginalDressedQReflection
open Finset Set Function MeasureTheory Lattice Wilson RG Source Labels Cells
open OPE.Therm PhysicalNext.Repeat.Legato Push.GridApprox WilsonMacroscopicForwardTransfer
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G){cellDate birthDate N per:ℕ}

theorem charged (hk:cellDate≤birthDate)(live:birthDate≤N)(o:Site (R.family.side cellDate per))(r:ℕ)
    (cut:Cut (R.family.side N per))(X:Config G (R.family.side N per)→ℂ)
    (E:Config G (R.family.side birthDate per)→ℂ)(M:ℝ)(nonneg:0≤M)
    (right:Interior (window (anchor R.family.S per hk o) r) E)
    (left:Interior cut.sector X)(bound:∀V,‖E V‖≤M)
    (cl:Continuous X)
    (inside:window (anchor R.family.S per (hk.trans live) o)
        (grows R.family.path.levels birthDate r live) ⊆ cut.sector):
    let Y:=fun U=>star (X (cut.pullC G U))
    ‖∫ W,exterior (C:=R.family) (N:=N) live Y W*E W ∂scene R.family.path N per birthDate‖^2 ≤
      M^2*‖∫ U,X U*Y U ∂scene R.family.path N per N‖:=by
  intro Y
  have cy : Continuous Y:=cl.comp (Wilson.continuous_pull cut.flip cut.slide) |>.star
  have iq:Integrable Y (scene R.family.path N per N):=by
    rw [WilsonPositionOriginalDiagnosticReflected.same]
    exact cy.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have dual:=joint (C:=R.family) R.makes live (le_refl N) Y iq E ⟨right.borel,M,bound⟩
  rw [dual]
  simp_rw [mul_comm (Y _)]
  exact WilsonPositionOriginalDiagnosticReflected.paid R cut _ X M nonneg
    ((backTo_local R.family.path N per hk live o r right).enlarges inside) left
    (backTo_bound R.family.path N per live right.borel M bound)

theorem room_charged (hk:cellDate≤birthDate)(live:birthDate≤N)(o:Site (R.family.side cellDate per))(r:ℕ)
    (cut:Cut (R.family.side N per))(X:Config G (R.family.side N per)→ℂ)
    (E:Config G (R.family.side birthDate per)→ℂ)(M:ℝ)(nonneg:0≤M)
    (right:Interior (window (anchor R.family.S per hk o) r) E)
    (left:Interior cut.sector X)(bound:∀V,‖E V‖≤M)(cl:Continuous X)
    (spent:room R.family.path.levels cellDate birthDate r)
    (tile:(tilesAt R.family.S per (hk.trans live)).chamber o⊆cut.sector):
    let Y:=fun U=>star (X (cut.pullC G U))
    ‖∫ W,exterior (C:=R.family) (N:=N) live Y W*E W ∂scene R.family.path N per birthDate‖^2 ≤
      M^2*‖∫ U,X U*Y U ∂scene R.family.path N per N‖:=
  charged R hk live o r cut X E M nonneg right left bound cl
    ((room_fits per R.family.path.levels r hk live spent o).trans tile)

end YM.Integration.WilsonPositionOriginalDressedQReflection
