import YM.Integration.WilsonConditionalTaylorThermalCubicPair
import YM.Integration.WilsonConditionalTaylorThermalLogHaar

/-! The surviving extensive second activity enters only through its actual
logarithmic bond sum, a single Wilson quartic, and a fourth cumulant
with two cubic vertices. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorThermalFourthLinked
open Function Filter MeasureTheory Lattice RG Tree Wilson Precision Push.BetaTransport
open RGComparison.Core16 RGComparison.Core16.Descent PertExtension PertExtension.Series Tested Radial GaussianScore
open WilsonConditionalTaylorThermalCumulant WilsonConditionalTaylorThermalWeight WilsonConditionalTaylorThermalLaplace
open WilsonConditionalTaylorThermalInteraction WilsonConditionalTaylorThermalFourthActivity WilsonConditionalTaylorThermalCubicPair
open scoped Classical BigOperators
variable {G : Gauge} {n c : Side} {d : Descent n c}
local notation "E" => Coordinates G d
local notation "μ" => Chart.tangent G d.Links

def localTerm (P : ChartRatio G) (t : d.Tags) (x : E) :=
  (∑i:d.Links,WilsonConditionalTaylorThermalLogHaar.logarithmic (WilsonConditionalTaylorThermalLogHaar.leaf P i) x)-
    jet (d.phase G t) 4 x

def reading (P : ChartRatio G) (room : d.Room G) (t : d.Tags) (a : ℕ→ℝ) (f : Config G n→ℝ) (w : ℕ) :=
  let A := (ambient t room).average μ
  let F := field (d:=d) f w
  let F1 := field (d:=d) f (w+1)
  let F2 := field (d:=d) f (w+2)
  let Q := vertex (G:=G) t a
  let Q3 := nextVertex (G:=G) t a
  let Q4 := WilsonConditionalTaylorThermalFourthBook.quartic (G:=G) t a
  let H := interaction P t
  Neg.neg (covariance A F2 Q+covariance A F1 Q3+covariance A F Q4+
    third A F1 Q H+third A F Q3 H+third A F Q (localTerm P t)+fourth A F Q H/2)

theorem original (P : ChartRatio G) (R : LocalRatio P) (room : d.Room G) (t : d.Tags)
    (a : ℕ→ℝ) {f : Config G n→ℝ} (test : d.Testable f) {w : ℕ} (old : d.grade f w) :
    WilsonConditionalTaylorThermalFirstDifferential.response P d a f (w+4)=reading P room t a f w := by
  let H := interaction P t
  let B := localTerm P t
  let Γ := ambient t room
  have h : priced H := prior P t
  have twice := pricedHalf (product h h)
  have parts : second P t = B+half (H*H) := by
    funext x
    rw [WilsonConditionalTaylorThermalLogHaar.official P R t]
    change _=localTerm P t x+(interaction P t x*interaction P t x)/2
    unfold localTerm;ring
  have b : priced B := by
    have eq : B=second P t-half (H*H) := by rw [parts,add_sub_cancel_right]
    rw [eq];exact priceDifference (WilsonConditionalTaylorThermalFourthConnected.activity P t) twice
  have sym := WilsonConditionalTaylorThermalFourthConnected.symmetry P t a Γ
  have add : third (Γ.average μ) (field (d:=d) f w) (vertex t a) (B+half (H*H)) =
      third (Γ.average μ) (field (d:=d) f w) (vertex t a) B+
      third (Γ.average μ) (field (d:=d) f w) (vertex t a) (half (H*H)) := combineThird Γ μ (angular (f ∘ d.fine 1 ∘ d.tablePath) w)
    (angular (WilsonConditionalTaylorThermalWeight.account (G:=G) t a ∘ d.tablePath) 2) b twice
  have identity : third (Γ.average μ) (field (d:=d) f w) (vertex t a) (second P t)=
      third (Γ.average μ) (field (d:=d) f w) (vertex t a) B+
      fourth (Γ.average μ) (field (d:=d) f w) (vertex t a) H/2 := by
    rw [parts,add,halfThird,paired Γ μ _ _ _ sym.1 sym.2.2]
  rw [WilsonConditionalTaylorThermalFourthConnected.original P R room t a test old]
  unfold WilsonConditionalTaylorThermalFourthConnected.attached WilsonConditionalTaylorThermalFourthConnected.contribution reading
  rw [identity]
  ring

end YM.Integration.WilsonConditionalTaylorThermalFourthLinked
