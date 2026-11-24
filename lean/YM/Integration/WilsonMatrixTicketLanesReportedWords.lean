import YM.Integration.WilsonCoherentTerminalFrame

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesReportedWords
open RGComparison.Core16 RGComparison.Core16.Spool PhysicalNext.Repeat.Legato
open scoped Classical
variable {G : Gauge}

/-- A letter is chosen from the original microscopic basis, already specified by
the gauge group before any continuum extraction, calendar, or family. -/
abbrev Letter (G : Gauge) := Σ d : ℕ,(Labels.frames G |>.level d).Index

/-- A countable purchase can cover every finite angular word, Taylor order and
integer lower-field cap before the original run is chosen. -/
abbrev Menu (G : Gauge) := (Σ n : ℕ,Fin n → Letter G) × ℕ × ℕ

theorem countable (G : Gauge) : Countable (Menu G) := by infer_instance

def lamp (t : Letter G) : Spool.Lamp G :=
  Spool.investment (Next.Foundations.sound G t.1) (Next.Foundations.valuation G t.1) t.2

def code {n : ℕ} (d : Fin n → ℕ) (j : ∀ i,(Labels.frames G |>.level (d i)).Index) (q cap : ℕ) : Menu G :=
  (⟨n,fun i=>⟨d i,j i⟩⟩,q,cap)

theorem original (R : Run G) {n : ℕ} (d : Fin n → ℕ) (j : ∀ i,(R.family.labels.level (d i)).Index)
    (q cap : ℕ) (i : Fin n) :
    lamp (((code d j q cap).1.2) i) = WilsonCoherentTerminalFrame.lamp R (d i) (j i) := rfl

end YM.Integration.WilsonMatrixTicketLanesReportedWords
