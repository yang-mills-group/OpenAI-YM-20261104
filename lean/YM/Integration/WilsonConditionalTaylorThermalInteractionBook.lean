import YM.Integration.WilsonConditionalTaylorThermalInteraction

/-! The original finite tag sum one order beyond the head, including the
higher source, the cubic signed temperature vertex and the common interaction. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorThermalInteractionBook
open Function Filter MeasureTheory Lattice RG Tree Wilson Precision Push.BetaTransport
open RGComparison.Core16 RGComparison.Core16.Descent PertExtension PertExtension.Series Tested Radial GaussianScore
open WilsonConditionalTaylorThermalLaplace WilsonConditionalTaylorThermalBook
open WilsonConditionalTaylorThermalWeight WilsonConditionalTaylorThermalInteraction
open scoped Classical BigOperators ContDiff Topology
variable {G : Gauge} {n c : Side} {d : Descent n c}
local notation "E" => Coordinates G d
local notation "μ" => Chart.tangent G d.Links

def stored (P : ChartRatio G) (t : d.Tags) (f : Config G n → ℝ) (w : ℕ) :=
  field (d:=d) f (w+1) + field f w * interaction P t

def inserted (P : ChartRatio G) (t : d.Tags) (v : ℕ→ℝ) (f : Config G n → ℝ) (w : ℕ) :=
  nextVertex (G:=G) t v * field (d:=d) f w + vertex t v * field f (w+1) +
    (vertex t v*field f w)*interaction P t

theorem registered (P : ChartRatio G) (room : d.Room G) (t : d.Tags)
    (Y : d.Tags → Fields G d→ℝ) (B : E→ℝ) (k : ℕ)
    (h : ∀s, integrandSeries (d.phase G s) (nearFee P s (Y s)) k = fun x => density d P*B x) :
    (∑s, gaussianTerm P s (Y s) k) = scale P t * (ambient t room).average μ B := by
  have slot (s) : gaussianTerm P s (Y s) k = density d P*(ambient t room).average μ B*mass (G:=G) t := by
    rw [moment_diagram s P room,h s]
    change _ * mass (G:=G) s = _
    rw [mass_tag room s t,average_tag room s t]
    unfold Law.average
    simp only [Pi.mul_apply,mul_assoc,integral_const_mul]
    ring
  simp only [slot,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,scale]
  ring

theorem source (P : ChartRatio G) (R : LocalRatio P) (room : d.Room G) (t : d.Tags)
    (u : ℕ→ℝ) {f : Config G n→ℝ} (test : d.Testable f) {w : ℕ} (grade : d.grade f w) :
    bareRank P d u f (w+1) = scale P t * (ambient t room).average μ (stored P t f w) := by
  rw [WilsonConditionalTaylorThermalBook.lower P R room u 0 test grade (w+1) (by omega),bareRank,Finset.sum_apply]
  apply registered
  intro s
  have eq : d.resetTerms 0 f s = f ∘ d.fine 1 := by
    funext y
    simp [resetTerms,account_zero]
  rw [eq]
  funext x
  rw [angular P R room s test.smooth grade x, (tag (room_ok d room) P s t 0).1]
  rfl

theorem charged (P : ChartRatio G) (R : LocalRatio P) (room : d.Room G) (t : d.Tags)
    (v : ℕ→ℝ) {f : Config G n→ℝ} (test : d.Testable f) {w : ℕ} (grade : d.grade f w) :
    (∑s : d.Tags, gaussianTerm P s (score s v f) (w+3)) =
      scale P t*(ambient t room).average μ (inserted P t v f w) := by
  apply registered
  intro s
  funext x
  let A := account (G:=G) s v ∘ d.tablePath
  let F := f ∘ d.fine 1 ∘ d.tablePath
  have sa := smoothAccount (room_ok d room) s v
  have gr := accountGrade (room_ok d room) s v
  have nw := WilsonConditionalTaylorThermalNextProduct.jets sa test.smooth gr grade x
  have hd := head_product sa test.smooth gr grade x
  rw [Nat.add_comm 2 w] at nw hd
  have a := angular P R room s (Y:=score s v f) (sa.mul test.smooth)
    (scoreGrade (room_ok d room) s v grade) x
  change _ = density d P*(jet (A*F) (w+2+1) x + jet (A*F) (w+2) x * _) at a
  rw [nw,hd] at a
  change _ = density d P*(vertex s v x * field (d:=d) f (w+1) x +
    nextVertex s v x * field f w x + (vertex s v x*field f w x)*interaction P s x) at a
  rw [vertex_tag (room_ok d room) s t v,(tag (room_ok d room) P s t v).1,
    (tag (room_ok d room) P s t v).2] at a
  change _ = density d P * (inserted P t v f w x)
  rw [a]
  dsimp only [inserted,Pi.add_apply,Pi.mul_apply]
  ring

end YM.Integration.WilsonConditionalTaylorThermalInteractionBook
