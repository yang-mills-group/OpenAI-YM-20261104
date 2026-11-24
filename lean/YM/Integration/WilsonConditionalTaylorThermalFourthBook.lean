import YM.Integration.WilsonConditionalTaylorThermalFourthActivity
import YM.Integration.WilsonConditionalTaylorThermalFirstDifferential

/-! Explicit fourth-grade score and vacuum densities on the same Gaussian,
before source placement or integration. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorThermalFourthBook
open Function Filter MeasureTheory Lattice RG Tree Wilson Precision Push.BetaTransport
open RGComparison.Core16 RGComparison.Core16.Descent PertExtension PertExtension.Series Tested Radial GaussianScore
open WilsonConditionalTaylorThermalLaplace WilsonConditionalTaylorThermalInteraction
open WilsonConditionalTaylorThermalBook WilsonConditionalTaylorThermalWeight WilsonConditionalTaylorThermalFourthActivity
open scoped Classical BigOperators ContDiff Topology
variable {G : Gauge} {n c : Side} {d : Descent n c}
local notation "E" => Coordinates G d
local notation "μ" => Chart.tangent G d.Links

def quartic (t : d.Tags) (a : ℕ→ℝ) := jet (WilsonConditionalTaylorThermalWeight.account (G:=G) t a ∘ d.tablePath) 4

theorem labels (ok : d.OK G) (P : ChartRatio G) (s t : d.Tags) (a : ℕ→ℝ) :
    second P s = second P t ∧ quartic (G:=G) s a=quartic t a := by
  constructor
  · funext x;unfold second;rw [phase_jet ok s t,phase_jet ok s t]
  · have h := branch_independent (v:=fun x : E=>x) (Bg:=fun _=>0) ok contDiffAt_id rfl s t a
    simp only [link_one] at h
    funext x;unfold quartic jet WilsonConditionalTaylorThermalWeight.account
    simp only [Function.comp_def];rw [(h.iteratedFDeriv ℝ 4).eq_of_nhds]

def prior (P : ChartRatio G) (t : d.Tags) (f : Config G n→ℝ) (w : ℕ) :=
  field (d:=d) f (w+2)+field f (w+1)*interaction P t+field f w*second P t

def submitted (P : ChartRatio G) (t : d.Tags) (a : ℕ→ℝ) (f : Config G n→ℝ) (w : ℕ) :=
  field (d:=d) f (w+2)*vertex t a+field f (w+1)*(nextVertex t a+vertex t a*interaction P t)+
    field f w*(quartic t a+nextVertex t a*interaction P t+vertex t a*second P t)

theorem vacuum (P : ChartRatio G) (R : LocalRatio P) (room : d.Room G) (t : d.Tags)
    {f : Config G n→ℝ} (test : d.Testable f) {w : ℕ} (old : d.grade f w) :
    bareRank P d 0 f (w+2)=scale P t*(ambient t room).average μ (prior P t f w) := by
  unfold bareRank;simp only [Finset.sum_apply]
  apply WilsonConditionalTaylorThermalInteractionBook.registered
  intro s
  have eq : d.resetTerms 0 f s = f ∘ d.fine 1 := by funext x;simp [resetTerms,account_zero]
  rw [eq];funext x
  rw [WilsonConditionalTaylorThermalFourthActivity.angular P R room s test.smooth old x,
    (WilsonConditionalTaylorThermalInteraction.tag (room_ok d room) P s t 0).1,(labels (room_ok d room) P s t 0).1]
  rfl

theorem scored (P : ChartRatio G) (R : LocalRatio P) (room : d.Room G) (t : d.Tags)
    (a : ℕ→ℝ) {f : Config G n→ℝ} (test : d.Testable f) {w : ℕ} (old : d.grade f w) :
    WilsonConditionalTaylorThermalOddInsertion.raw P d a f (w+4) =
      scale P t*(ambient t room).average μ (submitted P t a f w) := by
  apply WilsonConditionalTaylorThermalInteractionBook.registered
  intro s;funext x
  let A := WilsonConditionalTaylorThermalWeight.account (G:=G) s a ∘ d.tablePath
  let F := f ∘ d.fine 1 ∘ d.tablePath
  let ok := room_ok d room
  have sa := smoothAccount ok s a
  have gr := accountGrade ok s a
  have j0 := head_product sa test.smooth gr old x
  have j1 := WilsonConditionalTaylorThermalNextProduct.jets sa test.smooth gr old x
  have j2 := WilsonConditionalTaylorThermalSecondProduct.jets sa test.smooth gr old x
  rw [Nat.add_comm 2 w] at j0 j1 j2
  rw [WilsonConditionalTaylorThermalFourthActivity.angular P R room s (Y:=score s a f)
    (sa.mul test.smooth) (scoreGrade ok s a old) x]
  change density d P*(jet (A*F) (w+2+2) x+jet (A*F) (w+2+1) x*interaction P s x+
    jet (A*F) (w+2) x*second P s x)=_
  rw [j0,j1,j2]
  change density d P*((vertex s a x*field f (w+2) x+nextVertex s a x*field f (w+1) x+
    quartic s a x*field f w x)+(vertex s a x*field f (w+1) x+nextVertex s a x*field f w x)*interaction P s x+
    (vertex s a x*field f w x)*second P s x)=_
  have ds := WilsonConditionalTaylorThermalInteraction.tag ok P s t a
  have fourth := labels ok P s t a
  rw [vertex_tag ok s t a,ds.1,ds.2,fourth.1,fourth.2]
  simp only [submitted,Pi.add_apply,Pi.mul_apply];ring

end YM.Integration.WilsonConditionalTaylorThermalFourthBook
