import YM.Integration.WilsonPositionOriginalDressedQWindow
import YM.Integration.WilsonPositionOriginalDressedQReflection
import YM.Integration.WilsonPositionOriginalDiagnosticAgedQFare

/-! The complete truncated clock substitution at its true nonbare birth,
against a cutoff-dependent dressed field on the original Wilson law.
The right placement is independent of the reflected left field and may
vary across the booked physical subcell. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionOriginalDressedQHearing
open Finset Filter Set Function MeasureTheory Lattice Wilson RG Source Labels Cells
open OPE.Therm PhysicalNext.Repeat.Legato Push.GridApprox WilsonMacroscopicForwardTransfer
open WilsonPositionOriginalDiagnosticHalfSpace WilsonPositionOriginalDressedQCylinder
open MS MS.Land MS.Menus MS.Local.Physical WilsonPositionProgramReporterBand
open WilsonPositionOriginalDiagnosticRightSeries WilsonPositionOriginalDiagnosticRightAssay
open WilsonPositionOriginalDiagnosticRightReading WilsonPositionOriginalDiagnosticReflected
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G){B:Deck G}(Q:MS.Land.Prescription B)(h:ℕ)
local notation "A" => R.family.path.levels
local notation "I" => Glyph B h

private theorem at_birth (m per:ℕ)(o:Site (R.family.side m per)) :
    anchor R.family.S per (le_refl m) o=o:=by
  let Z:=R.family.S.toDepth (le_refl m) per
  have one:Z.count.val=1:=by simpa using Z.exact_size
  change Z.embed o=o
  simp [Ratio.embed,one]

theorem original {D:XSpace.Run}{stage:ℕ}(T:Band R D stage)(Y:Poetry R.family.path.levels)
    (simple:G.Simple)(fee:ℝ)(pos:0≤fee):
    ∃ C:ℝ, 0≤C ∧ ∀p:ℕ,∀ᶠ t:ℕ in atTop,∀ N per,∀live:T.reporter+t≤N,
      ∀θ ψ:ℝ, ‖θ‖+‖ψ‖≤fee → ∀r:ℝ,0<r → r≤1 → 2*R.family.S.a (T.reporter+t)*(RG16.Lambda A (T.reporter+t))^2≤r →
      ∀w:ℕ,8*R.family.S.a (T.reporter+t)*w≤r → ∀a:Axis,
      ∀o v:Site (R.family.side (T.reporter+t) per),v ∈ window o w → ∀j:I,
      let top:=anchor R.family.S per live o
      let cut:=sheet R N per a top (2*width R r N)
      let Δ:=R.family.S.scale (T.reporter+t+T.upper t)-R.family.S.scale (T.reporter+t)
      let g:=Pert.Asymptotics.regulatorRun R.family N per (T.reporter+t)
      let E:=remainder R Q h (θ-Δ) (ψ-Δ) (p+2) g (T.reporter+t) per j v
      ∀X:Config G (R.family.side N per)→ℂ,Continuous X → Interior cut.sector X →
      let Z:=fun U=>star (X (cut.pullC G U))
      ‖∫W,exterior (C:=R.family) (N:=N) live Z W*E W ∂scene R.family.path N per (T.reporter+t)‖^2 ≤
        (C*g^(p+1))^2 * ‖∫U,X U*Z U ∂scene R.family.path N per N‖:=by
  obtain ⟨C,hC,paid⟩:=WilsonPositionOriginalDiagnosticAgedQFare.original R Q h T simple fee pos
  refine ⟨C,hC,fun p=>?_⟩
  have late:Tendsto (fun t:ℕ=>T.reporter+t) atTop atTop:=tendsto_atTop_mono (fun t=>Nat.le_add_left ..) tendsto_id
  filter_upwards [paid p,late.eventually (WilsonPositionOriginalDressedQWindow.charged R Y simple h)] with t invoice placed
  intro N per live θ ψ bounded r hr small enough w collar a o v near j top cut Δ g E X cl hx Z
  have scope:Interior (window o (w+stencil R h)) E:=by
    refine markedInterior R Q h (θ-Δ) (ψ-Δ) (p+2) (g:ℂ) (T.reporter+t) per j v ?_
    intro b
    have inner : ↑((R.family.localSection b.size).footprint v) ⊆ window v (stencil R h):=
      footprint R (h:=h) (d:=b.size) (Nat.le_of_lt_succ b.1.2) (T.reporter+t) per v
    exact inner.trans (fun _ inside=>window_add near inside)
  have line:∀V,‖E V‖≤C*g^(p+1):=by
    intro V
    dsimp only [E,remainder];simp_rw [fields]
    exact invoice N per live θ ψ bounded (T.reporter+t) j v V
  have gpos:0≤g:=(ActualRunKernelPackets.regulator_pos R N per (T.reporter+t) live).le
  exact WilsonPositionOriginalDressedQReflection.charged R (cellDate:=T.reporter+t)
    (le_refl _) live o (w+stencil R h) cut X E (C*g^(p+1)) (mul_nonneg hC (pow_nonneg gpos _))
    (by rw [at_birth];exact scope) hx line cl (placed r hr small enough w collar N per live a top)

end YM.Integration.WilsonPositionOriginalDressedQHearing
