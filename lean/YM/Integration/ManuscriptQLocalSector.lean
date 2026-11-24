import YM.Integration.ManuscriptQLocalActualLog
import YM.AnalyticBridge.SECTOR_MARKED_IDENTITY.Committed

/-! The actual sector change of variables for the complete signed analytic
incoming source on every nonterminal step of the original history. The same
chosen allocation, forest, flags and original conditional denominator serve
every independent test and every source-coordinate derivative. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.ManuscriptQLocalSector

open Filter Function MeasureTheory Lattice Wilson RG RG.Shoot Supply Input Precision Marker Multi Exterior Tree Pressure
open Progress.DirectedRecipe PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open RG3.Script.Picnic LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open FullQLocal.RenderedStep.Numeric Comparison.RG02 Integral Actual
open Pressure.Testing Pressure.Stores Next.SectorChange Push.SectorMeasure
open scoped BigOperators Classical Topology ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {I : Type} [DecidableEq I] [Fintype I] {Γ : Census I}
    (R : Run G) {J : Request I} {A : NumericSchedule R.family J}
    (d : LocalFormal.Datum R.family Γ)
local notation "P" => R.family.path.rep d.cutoff d.period (d.level+1)
local notation "P₀" => R.family.path.rep d.cutoff d.period d.level
local notation "Δ" => R.family.path.levels.clock.op d.level d.period
local notation "Θ" => R.alloy.B.a.clock.hatBeta d.level
local notation "T" => ships R.alloy.B d.cutoff d.level d.period
local notation "i₀" => R.alloy.B.a.clock.J d.level
local notation "i₁" => R.alloy.B.a.clock.J (d.level+1)
local notation "w" => R.kit.walls i₁ i₀
local notation "b" => radiusW R.kit.rider i₁ i₀ * R.alloy.B.a.clock.threshold (d.level+1)

omit [Fintype I] in
theorem bought (Q : Allocation G Δ Θ w) (q : Chi) :
    Marked.Bought T Θ P d.forest Q q R.metals.O b := by
  obtain ⟨hLives,hBand⟩ := (R.T.sticks d.cutoff d.period).prices
    (d.level+1) (Nat.zero_le _) d.below
  exact (Marked.honored R.alloy.B R.kit.machine.ring R.kit.machine.bill
    d.cutoff d.level d.period d.below P hLives hBand).2.2 Q d.forest q

variable (F : AnalyticInput J A d) (x : TestSpace J.tests)
local notation "Π" => ManuscriptQLocalActualLog.source R d F x
local notation "u" => fun s : Γ.Mode => Actual.atMark s Π


/-- In particular the empty selection is the genuine original coarse
represented density. This fixes its normalization before the log. -/
theorem denominator (Q : Allocation G Δ Θ w) (q : Chi) (V : Config G (R.family.side d.level d.period)) :
    Marked.paidSum T Θ P d.forest Q q R.metals.O b (u Γ.quiet) V = ((P₀).eval V : ℂ) := by
  have H := ManuscriptQLocalActualLog.floor R d F x
  have hgi : GaugeInvariant (u Γ.quiet) := fun k U =>
    congrArg (fun z : Poly Γ => z.part Γ.quiet) (H.gauges k U)
  calc
    _ = (Δ).push (P).beta (Actual.atMark Γ.quiet Π) V :=
      (congrFun ((bought R d Q q).apply_push (H.safe Γ.quiet) hgi) V).symm
    _ = (Actual.Push Δ (P).beta Π V).part Γ.quiet :=
      (congrFun (Actual.grades (S:=Δ) (D:=Π) (J:=V) (β:=(P).beta)) Γ.quiet).symm
    _ = _ := (Local.RealStep.advance R.family d.cutoff d.period d.level d.below Π
      R.makes H).vacancy V

/-- The mixed derivatives are signed before integration at independently
chosen amplitudes. Each sector retains its frozen-link Haar variables and
its active Gaussian with the actual window and translated mean. -/
theorem mixed (Q : Allocation G Δ Θ w) (q : Chi) (l : List I) (t : I → ℝ) (V : Config G (R.family.side d.level d.period)) :
    let v := Marked.SourceJet.combine (u) l t
    Marked.SourceJet.mixed (fun a => (Δ).push (P).beta (Marked.SourceJet.combine (u) [] a) V) l t =
        (Δ).push (P).beta v V ∧
      (Δ).push (P).beta v V = Marked.paidSum T Θ P d.forest Q q R.metals.O b v V ∧
      ∀ (C : Stores Δ) (k : (Δ).Choices),
        Marked.Permission T Θ V k C P (shots Δ Θ) d.forest Q q R.metals.O b
          (fog C d.forest T Θ V k) (meanLog C d.forest T Θ V k q b) v := by
  have H := ManuscriptQLocalActualLog.floor R d F x
  exact Marked.SourceJet.push_with (bought R d Q q) (u) H.safe
    (fun s k U => congrArg (fun z : Poly Γ => z.part s) (H.gauges k U)) l t V

/-- Every coordinate of the original conditional numerator uses the very
same purchased change of variables, at every physical coarse field. -/
theorem numerator (Q : Allocation G Δ Θ w) (q : Chi) (V : Config G (R.family.side d.level d.period)) (s : Γ.Mode) :
    (Actual.Push Δ (P).beta Π V).part s = Marked.paidSum T Θ P d.forest Q q R.metals.O b (u s) V := by
  have H := ManuscriptQLocalActualLog.floor R d F x
  rw [congrFun (Actual.grades (S:=Δ) (D:=Π) (J:=V) (β:=(P).beta)) s]
  exact congrFun ((bought R d Q q).apply_push (H.safe s)
    (fun k U => congrArg (fun z : Poly Γ => z.part s) (H.gauges k U))) V

/-- The single logarithm on the full source algebra, with the physical
denominator charged on precisely the same store allocation in every mode. -/
theorem connected (Q : Allocation G Δ Θ w) (q : Chi) (V : Config G (R.family.side d.level d.period)) :
    Local.cumulant P Π Δ V =
      Extra.Trajectories.connected (((P₀).eval V : ℂ)⁻¹ •
        (fun s : Γ.Mode => Marked.paidSum T Θ P d.forest Q q R.metals.O b (u s) V : Poly Γ)) := by
  have hpoly : Actual.Push Δ (P).beta Π V = (fun s : Γ.Mode => Marked.paidSum T Θ P d.forest Q q R.metals.O b (u s) V : Poly Γ) :=
    funext fun s => numerator R d F x Q q V s
  rw [Local.cumulant,Local.normalized,Local.yield,Order.unitScale,hpoly]
  congr 2
  exact congrArg (fun z : ℂ => z⁻¹) (denominator R d F x Q q V)

end YM.Integration.ManuscriptQLocalSector
end
