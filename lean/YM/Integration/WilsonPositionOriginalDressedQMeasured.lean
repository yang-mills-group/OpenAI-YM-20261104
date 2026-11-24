import YM.Integration.WilsonPositionOriginalDressedQHearing
import YM.Integration.WilsonPositionOriginalDressedQFixedPlane
import YM.Integration.WilsonPositionOriginalDiagnosticPastSource

/-! The measured two-clock replacement on a genuinely aged Wilson field
against one actual cutoff-dressed original label.  Its reflected price is
the measured continuum self-Gram at the submitted physical radius. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionOriginalDressedQMeasured
open Finset Filter Set Function MeasureTheory Lattice Wilson RG Source Labels Cells
open OPE.Therm PhysicalNext.Repeat.Legato Push.GridApprox WilsonMacroscopicForwardTransfer
open MS MS.Land MS.Menus MS.Local.Physical WilsonPositionProgramReporterBand
open WilsonPositionOriginalDressedQCylinder WilsonPositionOriginalDiagnosticRightSeries
open WilsonPositionOriginalDiagnosticRightAssay WilsonPositionOriginalDiagnosticRightReading
open WilsonPositionOriginalDiagnosticReflected WilsonPositionOriginalDiagnosticMeasuredGram
open Extraction Extraction.Banks RG17 Spec Table
open scoped BigOperators Classical Topology
open private at_birth from YM.Integration.WilsonPositionOriginalDressedQHearing
variable {G:Gauge}(R:Run G){B:Deck G}(Q:MS.Land.Prescription B)(h:ℕ)
  {f:Extraction.Order}{S:Table R.family.book}(F:Spec.Final R.family f S)(L:Layout F)
local notation "A"=>R.family.path.levels

theorem original {D:XSpace.Run}{stage:ℕ}(T:Band R D stage)(Y:Poetry A)(simple:G.Simple)(fee:ℝ)(pos:0≤fee):
    ∃c:ℝ,0≤c ∧ ∀p:ℕ,∀ᶠt:ℕ in atTop,∀θ ψ:ℝ,‖θ‖+‖ψ‖≤fee →
      ∀r:ℝ,0<r → r≤1 → 2*R.family.S.a (T.reporter+t)*(RG16.Lambda A (T.reporter+t))^2≤r →
      ∀w:ℕ,8*R.family.S.a (T.reporter+t)*w≤r → ∀a:Axis,∀d:ℕ,∀χ:Test 1,
      ∀ok:∀x∈tsupport χ,Points.allAbove a 0 x,∀rr:ℝ,∀v:R.family.label d,R.family.ref d≤L.level rr →
      ∀(l:Filter (ℕ×ℕ))[l.NeBot],l≤L.lens → ∀η:ℝ,0<η → ∀ᶠz:ℕ×ℕ in l,
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
  obtain ⟨c,hc,paid⟩:=WilsonPositionOriginalDiagnosticAgedQFare.original R Q h T simple fee pos
  refine ⟨c,hc,fun p=>?_⟩
  have late:Tendsto (fun t:ℕ=>T.reporter+t) atTop atTop:=tendsto_atTop_mono (fun t=>Nat.le_add_left ..) tendsto_id
  filter_upwards [paid p,late.eventually (WilsonPositionOriginalDressedQFixedPlane.original R Y simple h)] with t quoted placed
  intro θ ψ bounded r hr small enough w offset a d χ ok rr v entered l inst goes η positive
  let M:=S.integralOn (fun _:Fin 2=>d) (two R d a (locatedRef L d rr v)) (doubled R d a χ ok)
  have gram:=WilsonPositionOriginalDiagnosticMeasuredGram.original R F L d a χ ok rr v entered l goes
  have gn:=gram.norm.eventually (eventually_lt_nhds (show ‖M‖<‖M‖+η by linarith))
  have left:=(WilsonPositionOriginalDiagnosticPastSource.rows R f d a χ ok).filter_mono (goes.trans L.certified)
  filter_upwards [gn,left] with z measured supports
  intro live u lower upper o near j Δ g E X cut Z junk
  let center:=wrap (R.family.side (T.reporter+t) z.2) u
  have right:Interior (window center (w+stencil R h)) E:=by
    apply markedInterior
    intro b
    exact (footprint R (h:=h) (d:=b.size) (Nat.le_of_lt_succ b.1.2) (T.reporter+t) z.2 o).trans
      (fun _ inside=>window_add near inside)
  have xf:Interior cut.sector X:=by
    dsimp only [X,smear];rw [←WilsonPositionOriginalDiagnosticPastSource.single];exact supports _
  have cl:Continuous X:=by
    dsimp only [X,smear,stem]
    exact continuous_finsetSum _ fun i _=>elementary R.family _ _
  have size:∀W,‖E W‖≤c*g^(p+1):=by
    intro W;dsimp only [E,remainder];simp_rw [fields]
    exact quoted z.1 z.2 live θ ψ bounded (T.reporter+t) j o W
  have gp:0≤g:=(ActualRunKernelPackets.regulator_pos R z.1 z.2 (T.reporter+t) live).le
  have invoice:=WilsonPositionOriginalDressedQReflection.charged R (cellDate:=T.reporter+t) (le_refl _) live center
    (w+stencil R h) cut X E (c*g^(p+1)) (mul_nonneg hc (pow_nonneg gp _)) (by rw [at_birth];exact right)
    xf size cl (placed r hr small enough w offset z.1 z.2 live a u lower upper)
  refine invoice.trans (mul_le_mul_of_nonneg_left ?_ (sq_nonneg _))
  rw [WilsonPositionOriginalDiagnosticReflected.same]
  exact measured.le

end YM.Integration.WilsonPositionOriginalDressedQMeasured
