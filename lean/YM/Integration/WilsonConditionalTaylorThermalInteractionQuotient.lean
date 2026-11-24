import YM.Integration.WilsonConditionalTaylorThermalInteractionDifference
import YM.Integration.WilsonConditionalTaylorThermalInteractionDivision

/-! The normalized Wilson response at relative order three, on its own full
Gaussian. The cubic action and the source interact before division by the
whole unmarked vacuum. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorThermalInteractionQuotient
open Function Filter MeasureTheory Lattice RG Tree Wilson Precision Push.BetaTransport
open RGComparison.Core16 RGComparison.Core16.Descent PertExtension PertExtension.Series Tested Radial GaussianScore
open WilsonConditionalTaylorThermalLaplace WilsonConditionalTaylorThermalBook
open WilsonConditionalTaylorThermalInteraction WilsonConditionalTaylorThermalInteractionBook
open WilsonConditionalTaylorThermalDivision PowerSeries
open scoped Classical BigOperators ContDiff Topology
variable {G : Gauge} {n c : Side} {d : Descent n c}
local notation "E" => Coordinates G d
local notation "μ" => Chart.tangent G d.Links

theorem unitNext : field (d:=d) (1 : Config G n→ℝ) 1 = 0 := by
  change jet (fun _ : E => (1:ℝ)) 1 = _
  funext x
  simp [jet,iteratedFDeriv_one_apply]

theorem original (P : ChartRatio G) (R : LocalRatio P) (room : d.Room G) (t : d.Tags)
    (u v : ℕ→ℝ) {f : Config G n→ℝ} (test : d.Testable f) {w : ℕ} (grade : d.grade f w) :
    let Γ := ambient t room
    let Q := vertex t (u-v)
    let F := field (d:=d) f w
    let H := interaction P t
    let A := Γ.average μ
    ranking P d u f (w+3)-ranking P d v f (w+3) =
      -A (inserted P t (u-v) f w) + A F * A (nextVertex t (u-v)+Q*H) +
      (A (stored P t f w)-A F*A H)*A Q + (A (F*Q)-A F*A Q)*A H := by
  intro Γ Q F H A
  let B (z : ℕ→ℝ) (g : Config G n→ℝ) := PowerSeries.mk (bareRank P d z g)
  let old := B v f*(B v 1)⁻¹
  let newer := B u f*(B u 1)⁻¹
  have pv (z : ℕ→ℝ) : coeff 0 (B z 1) ≠ 0 := by simpa [B] using (pivot P R z room).ne'
  have low : zeroBefore old w := fun k hk => ranking_grade P R room v test grade k hk
  have er : zeroBefore (newer-old) (w+2) := by
    intro k hk
    rw [map_sub,sub_eq_zero]
    exact WilsonConditionalTaylorThermalObserved.before P R room u v test grade k hk
  have vac : zeroBefore (B u 1-B v 1) 2 := by
    intro k hk
    rw [map_sub,sub_eq_zero]
    simpa only [B,coeff_mk] using WilsonConditionalTaylorThermalBook.lower P R room u v (unit_test d) unitGrade k hk
  have oldEq := WilsonConditionalTaylorThermalInteractionDivision.incoming (pv v) low
  have curve := WilsonConditionalTaylorThermalInteractionDivision.differing (pv u) (pv v) low er vac
  simp only [B,map_sub,coeff_mk] at oldEq curve
  change ranking P d v f w*bareRank P d v 1 0=bareRank P d v f w ∧
    ranking P d v f w*bareRank P d v 1 1 + ranking P d v f (w+1)*bareRank P d v 1 0 =
      bareRank P d v f (w+1) at oldEq
  change (ranking P d u f (w+2)-ranking P d v f (w+2))*bareRank P d u 1 1 +
    (ranking P d u f (w+3)-ranking P d v f (w+3))*bareRank P d u 1 0 +
    (ranking P d v f w*(bareRank P d u 1 3-bareRank P d v 1 3) +
     ranking P d v f (w+1)*(bareRank P d u 1 2-bareRank P d v 1 2)) =
      bareRank P d u f (w+3)-bareRank P d v f (w+3) at curve
  let m := scale P t
  have mass : m≠0 := by rw [show m=bareRank P d v 1 0 from (vacuum P R room t v).symm]; exact (pivot P R v room).ne'
  have prev : bareRank P d v f w=m*A F := WilsonConditionalTaylorThermalBook.source P R room t v test grade
  have following : bareRank P d v f (w+1)=m*A (stored P t f w) :=
    WilsonConditionalTaylorThermalInteractionBook.source P R room t v test grade
  have empty (z : ℕ→ℝ) : bareRank P d z (1:Config G n→ℝ) 1=m*A H := by
    have h := WilsonConditionalTaylorThermalInteractionBook.source P R room t z (unit_test d) unitGrade
    simpa only [stored,unitNext,unitField,one_mul,zero_add] using h
  have unmarked : bareRank P d u (1:Config G n→ℝ) 3-bareRank P d v 1 3= -(m*A (nextVertex t (u-v)+Q*H)) := by
    have h := WilsonConditionalTaylorThermalInteractionDifference.signed P R room t u v (unit_test d) unitGrade
    simpa only [inserted,Nat.zero_add,unitNext,unitField,mul_one,mul_zero,add_zero] using h
  have cov : ranking P d u f (w+2)-ranking P d v f (w+2) = -(A (F*Q)-A F*A Q) := by
    have h := WilsonConditionalTaylorThermalQuotient.original P R room t u v test grade
    have q : ThermalShortcuts.ConnectedWick.quadratic (ThermalShortcuts.ThermalJets.signedForm G d t (u-v)) = Q :=
      funext fun x => (ThermalShortcuts.ThermalJets.signed_half t (u-v) x).symm
    simpa only [ThermalShortcuts.ConnectedWick.connected,q] using h
  rw [vacuum P R room t v,prev,empty v,following] at oldEq
  have head : ranking P d v f w=A F := mul_right_cancel₀ mass (oldEq.1.trans (mul_comm _ _))
  have second : ranking P d v f (w+1) = A (stored P t f w)-A F*A H := by
    apply mul_right_cancel₀ mass
    rw [head] at oldEq
    linear_combination oldEq.2
  rw [head,second,cov,empty u,vacuum P R room t u,unmarked,
    vacuumChange P R room t u v,WilsonConditionalTaylorThermalInteractionDifference.signed P R room t u v test grade] at curve
  apply mul_right_cancel₀ mass
  linear_combination curve

end YM.Integration.WilsonConditionalTaylorThermalInteractionQuotient
