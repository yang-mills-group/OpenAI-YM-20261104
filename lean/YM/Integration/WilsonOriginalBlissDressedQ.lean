import YM.Integration.WilsonPositionOriginalDressedQMeasured
import YM.Integration.WilsonOriginalBlissObserved

/-! A signed dressed-Q remainder and the exact transported cutoff label from the
same physical Bliss extraction and the same ultrafilter. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalBlissDressedQ
open Finset Filter Set Function MeasureTheory Lattice Wilson RG Source Labels Cells
open OPE.Therm PhysicalNext.Repeat.Legato Push.GridApprox WilsonMacroscopicForwardTransfer
open MS MS.Land MS.Menus MS.Local.Physical WilsonPositionProgramReporterBand
open WilsonPositionOriginalDressedQCylinder WilsonPositionOriginalDiagnosticRightSeries
open WilsonPositionOriginalDiagnosticRightAssay WilsonPositionOriginalDiagnosticRightReading
open WilsonPositionOriginalDiagnosticReflected WilsonPositionOriginalDiagnosticMeasuredGram
open Extraction Extraction.Banks RG17 Spec Table
open scoped BigOperators Classical Topology
variable {G:Gauge}(R:Run G){B:Deck G}(Q:MS.Land.Prescription B)(h:ℕ)
  {f:Extraction.Order}{S:Table R.family.book}(F:Spec.Final R.family f S)
  {H:(Climb.Bel R.family.book).Hierarchy}{l:Ultrafilter (ℕ×ℕ)}
  {arch:Trace.Terrace.Arch R.family}(bliss:Trace.Pilot.Bliss F l arch H)
  (J:ℝ→PhysMS.tower S)(level:ℝ→ℕ)
  (shift:∀ d,ℝ→R.family.label d ≃ₗ[ℂ] R.family.label d)
local notation "A"=>R.family.path.levels
local notation "L"=>WilsonOriginalBlissObserved.layout F bliss J level shift

theorem original {D:XSpace.Run}{stage:ℕ}(T:Band R D stage)(Y:Poetry A)(simple:G.Simple)(fee:ℝ)(pos:0≤fee):
    ∃c:ℝ,0≤c ∧ ∀p:ℕ,∀ᶠt:ℕ in atTop,∀θ ψ:ℝ,‖θ‖+‖ψ‖≤fee →
      ∀r:ℝ,0<r → r≤1 → 2*R.family.S.a (T.reporter+t)*(RG16.Lambda A (T.reporter+t))^2≤r →
      ∀w:ℕ,8*R.family.S.a (T.reporter+t)*w≤r → ∀a:Axis,∀d:ℕ,∀χ:Test 1,
      ∀ok:∀x∈tsupport χ,Points.allAbove a 0 x,∀rr:ℝ,∀v:R.family.label d,R.family.ref d≤level rr →
      ∀η:ℝ,0<η → ∀ᶠz:ℕ×ℕ in (l:Filter (ℕ×ℕ)),
      (∀v':R.family.label d,Trace.Terrace.Cturn R.family d (level rr) z.1 z.2
        (atRef L d rr z v')=((R.family.S.a (level rr)^d:ℝ):ℂ) • shift d rr v') ∧
      ∀live:T.reporter+t≤z.1,∀u:Cover,r/2≤R.family.S.a (T.reporter+t)*(u a:ℝ) →
      R.family.S.a (T.reporter+t)*(u a:ℝ)≤1 → ∀o∈window (wrap (R.family.side (T.reporter+t) z.2) u) w,∀j:Glyph B h,
      let Δ:=R.family.S.scale (T.reporter+t+T.upper t)-R.family.S.scale (T.reporter+t)
      let g:=Pert.Asymptotics.regulatorRun R.family z.1 z.2 (T.reporter+t)
      let E:=remainder R Q h (θ-Δ) (ψ-Δ) (p+2) g (T.reporter+t) z.2 j o
      let X:=smear R F L d a χ ok rr v z.1 z.2
      let cut:=plane R.family z.1 z.2 a
      let Z:=fun U=>star (X (cut.pullC G U))
      let M:=S.integralOn (fun _:Fin 2=>d) (two R d a (locatedRef L d rr v)) (doubled R d a χ ok)
      ‖∫W,exterior (C:=R.family) (N:=z.1) live Z W*E W ∂scene R.family.path z.1 z.2 (T.reporter+t)‖^2≤
        (c*g^(p+1))^2*(‖M‖+η):=by
  obtain ⟨c,hc,paid⟩:=WilsonPositionOriginalDressedQMeasured.original R Q h F L T Y simple fee pos
  refine ⟨c,hc,fun p=>?_⟩
  filter_upwards [paid p] with t approved
  intro θ ψ price r hr small enough w offset a d χ ok rr v ref η positive
  exact (WilsonOriginalBlissObserved.measured F bliss J level shift d rr ref).and
    (approved θ ψ price r hr small enough w offset a d χ ok rr v ref
      (l:Filter (ℕ×ℕ)) le_rfl η positive)

end YM.Integration.WilsonOriginalBlissDressedQ
