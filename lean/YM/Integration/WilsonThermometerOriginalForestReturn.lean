import YM.Integration.WilsonThermometerOriginalForestTable

/-! The original returned finite pupil inside the first nonbare forest contraction. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerOriginalForestReturn
open Function MeasureTheory Lattice RG Tree Wilson Exterior Precision Marker Multi Comparison.RG02
open Comparison.RG02.Assembly Comparison.RG02.Order FVA1Physical.Wilson FVA1Physical.TwoReset
open QuadraticLocal QuadraticLocal.Sunrise QuadraticLocal.Earn AllOrder.Floe
open scoped Classical BigOperators

variable {G:Gauge} {c n f:Side} {V:Type} [DecidableEq V] {R:Census V} {ι α:Type} {J:Passport n V}

def straight (mult:n.val∣f.val) (M:ι→Row J R G α) (w:V→ℕ) (upper lower:Layout G)
    (T:Finset Age) (v:α) (p:ℕ) : Bulk.Colors R G f :=
  let pupil:=copyColor mult M w (fun i=>(M i).paint v) upper T
  WilsonOriginalCoverJetColors.colors (QuadraticLocal.Fk.money lower T) (fun s=>Launch.index R w s.val+1) p
    (fun s d y=>(Air.discharge pupil d y).part s.val)

variable [Fintype V] {clip:Clip} {P:PathData G} {O:ChartRatio G}

omit [Fintype V] in
private theorem sharedQuiet {S:StepData c f} (K:Bulk.Kernel S clip P O) (F:Forest S.ratio)
    (t:S.Choices) (X Y:Bulk.Colors R G f) (h:X.vac=Y.vac) :
    Bulk.geometric K F t X=Bulk.geometric K F t Y := by
  funext z
  simp only [Bulk.geometric,Bulk.fee,Bulk.supplement,h]

private theorem combine {S:StepData c f} (K:Bulk.Kernel S clip P O) (F:Forest S.ratio)
    (t:S.Choices) (X Y:Bulk.Colors R G f) (p:ℕ) (live:0<p) (angle:fieldDir G c 1)
    (quiet:X.vac=Y.vac)
    (heads:∀ (s:Hot R) j, j≤1 → ∀ u:Bulk.Joint S F (G:=G),
      jet (Bulk.markFn S F X s) (X.power s+j) u=jet (Bulk.markFn S F Y s) (Y.power s+j) u) :
    let lhs:=Bulk.Fk K F t X angle p
    let rhs:=Bulk.Fk K F t Y angle p
    (∀j≤1,observe R p lhs j=observe R p rhs j) ∧
      First.buc (logMarked lhs)=First.buc (logMarked rhs) ∧ First.ind (logMarked lhs)=First.ind (logMarked rhs) := by
  have geo:=sharedQuiet K F t X Y quiet
  exact ⟨fun j hj=>WilsonThermometerOriginalForestTable.original F K t X Y 1 p angle geo heads j hj (hj.trans live),
    WilsonThermometerOriginalForestTable.ground F K t X Y p angle geo heads,
    WilsonThermometerOriginalForestTable.connected F K t X Y p live angle geo heads⟩

/-- The measured reset on the deposited pupil gives the same lower ordinary and normalized
connected coefficients as its filed straight program. Both contractions share the true quiet row. -/
theorem received (mult:n.val∣f.val) (M:ι→Row J R G α) (w:V→ℕ) (upper lower:Layout G)
    (T:Finset Age) (v:α) (p depth:ℕ) (live:0<p) (q:Pace.Coin) (a:ℝ) (earned:Pace.Earn q a)
    (input:WilsonOriginalCopiedHistory.Values G R n)
    (agree:∀d≤p,∀y,input f mult d y=peek mult M w upper T v d y)
    (S:StepData c f) (K:Bulk.Kernel S clip P O) (F:Forest S.ratio) (t:S.Choices)
    (angle:fieldDir G c 1) :
    let X:=WilsonOriginalCopiedHistory.receive input lower T w q earned.1 depth p f mult
    let Y:=straight mult M w upper lower T v p
    let lhs:=Bulk.Fk K F t X angle p
    let rhs:=Bulk.Fk K F t Y angle p
    (∀j≤1,observe R p lhs j=observe R p rhs j) ∧
      First.buc (logMarked lhs)=First.buc (logMarked rhs) ∧ First.ind (logMarked lhs)=First.ind (logMarked rhs) := by
  let X:=WilsonOriginalCopiedHistory.receive input lower T w q earned.1 depth p f mult
  let Y:=straight mult M w upper lower T v p
  apply combine K F t X Y p live angle (by rfl)
  intro s j hj u
  exact WilsonThermometerOriginalForestLetters.copied mult M w upper T v p depth live q a earned
    (input f mult) agree (QuadraticLocal.Fk.money lower T) S F s j hj u

end YM.Integration.WilsonThermometerOriginalForestReturn
