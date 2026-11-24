import YM.Integration.WilsonMeasuredCompanionFace
import YM.Integration.WilsonThermometerSolitaryExchange

/-! A signed pair of original owners on the same held torus and its two unchanged ordered peer functions. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonThermometerHostedPeers
open Function Finset MeasureTheory Lattice Wilson RG Labels Source Marker Overlay QuadraticLocal QuadraticLocal.Earn Ac
open WilsonMeasuredCompanionFace WilsonPhysicalMarkedDefect.RegularProjection
open scoped Classical BigOperators
variable {G:Gauge}{n:Side}{V T I:Type}[DecidableEq V][Fintype V]{J:Census V}{o:V→Site n}
  {d:ℕ}{F:Frame G d} {W P:Rep G n}

def transport {p q:BudgetPoint} (same:p=q) (E:Lamps T I G q o J):Lamps T I G p o J:=same.symm ▸ E

omit [Fintype V] in
theorem log {p q:BudgetPoint} (same:p=q) (E:Lamps T I G q o J) (x:T) (U:Config G n):
    (transport same E).log x U=E.log x U:=by cases same; rfl

omit [Fintype V] in
theorem paid {p q:BudgetPoint} (same:p=q) (E:Lamps T I G q o J) {w:V→ℝ} {b:ℕ} {a B:ℝ}
    (bill:E.Paid w b a B):(transport same E).Paid w b a B:=by cases same; exact bill

theorem peers_eq (same:P.p=W.p) (E:Lamps T I G W.p o J) (v:V) (s:J.Mode) (x:T) (U:Config G n):
    peers (W:=P) (transport same E) v s x U=peers (W:=W) E v s x U:=by
  unfold peers;rw [log]

theorem soft_eq (same:P.p=W.p) (quiet:P.eval=W.eval) (a:Site n) (S:SectionData F)
    (h:Coefficient F n) (U:Config G n):
    (soft h).density a S P U=(soft h).density a S W U:=by
  rw [density,density,quiet]
  simp only [Coefficient.exponentialEntry,Coefficient.maskedTerm,same]

/-- Only the canonical original hard surplus needs its own kappa-paid peer read. -/
theorem signed (same:P.p=W.p) (quiet:P.eval=W.eval) (E:Lamps T I G W.p o J)
    (v:V) (s:J.Mode) (x:T) (S:SectionData F) (h k:Coefficient F n) (U:Config G n):
    (h.density (o v) S W U+k.density (o v) S P U)*peers (W:=W) E v s x U=
      h.density (o v) S W U*peers (W:=W) E v s x U+
      (soft k).density (o v) S W U*peers (W:=W) E v s x U+
      (k.density (o v) S P U-(soft k).density (o v) S P U)*peers (W:=P) (transport same E) v s x U:=by
  rw [peers_eq,soft_eq same quiet]
  ring

end YM.Integration.WilsonThermometerHostedPeers
