import YM.Integration.WilsonConditionalTaylorThermalMixedBook
import YM.Integration.WilsonConditionalTaylorThermalMixedDivision
import YM.Integration.WilsonConditionalTaylorThermalCumulant

/-! On the original finite descent, two distinct signed temperature variations
first meet in the third Gaussian cumulant of their scores and the held field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorThermalMixedQuotient
open Function Filter MeasureTheory Lattice RG Tree Wilson Precision Push.BetaTransport
open RGComparison.Core16 RGComparison.Core16.Descent PertExtension PertExtension.Series Tested Radial GaussianScore
open WilsonConditionalTaylorThermalLaplace WilsonConditionalTaylorThermalBook
open WilsonConditionalTaylorThermalDivision WilsonConditionalTaylorThermalMixedDivision PowerSeries
open scoped Classical BigOperators ContDiff Topology
variable {G : Gauge} {n c : Side} {d : Descent n c}
local notation "μ" => Chart.tangent G d.Links

def difference (P : ChartRatio G) (d : Descent n c) (z a b : ℕ→ℝ) (f : Config G n→ℝ) (k : ℕ) :=
  WilsonConditionalTaylorThermalMixedDivision.square (ranking P d z f k) (ranking P d (z+a) f k) (ranking P d (z+b) f k) (ranking P d (z+a+b) f k)

theorem original (P : ChartRatio G) (R : LocalRatio P) (room : d.Room G) (t : d.Tags)
    (z a b : ℕ→ℝ) {f : Config G n→ℝ} (test : d.Testable f) {w : ℕ} (grade : d.grade f w) :
    (∀k < w+4, difference P d z a b f k=0) ∧ difference P d z a b f (w+4) =
      WilsonConditionalTaylorThermalCumulant.third ((ambient t room).average μ) (vertex t a) (vertex t b) (field (d:=d) f w) := by
  let B (u : ℕ→ℝ) (g : Config G n→ℝ) := PowerSeries.mk (bareRank P d u g)
  let C (u : ℕ→ℝ) := B u f*(B u 1)⁻¹
  have piv (u : ℕ→ℝ) : coeff 0 (B u 1)≠0 := by simpa [B] using (pivot P R u room).ne'
  have norm (u : ℕ→ℝ) : C u*B u 1=B u f :=
    WilsonConditionalTaylorThermalInteractionDivision.normalized (piv u)
  have early : zeroBefore (C z) w := fun k hk => ranking_grade P R room z test grade k hk
  have first (v : ℕ→ℝ) : zeroBefore (C (z+v)-C z) (w+2) := by
    intro k hk
    rw [map_sub,sub_eq_zero]
    exact WilsonConditionalTaylorThermalObserved.before P R room (z+v) z test grade k hk
  have vac (u v : ℕ→ℝ) : zeroBefore (B u 1-B v 1) 2 := by
    intro k hk
    rw [map_sub,sub_eq_zero]
    simpa only [B,coeff_mk] using WilsonConditionalTaylorThermalBook.lower P R room u v (unit_test d) unitGrade k hk
  have mix {g : Config G n→ℝ} (h : d.Testable g) {v : ℕ} (s : d.grade g v) :
      zeroBefore (WilsonConditionalTaylorThermalMixedDivision.square (B z g) (B (z+a) g) (B (z+b) g) (B (z+a+b) g)) (v+4) := by
    intro k hk
    simpa only [WilsonConditionalTaylorThermalMixedDivision.square,map_sub,B,coeff_mk,WilsonConditionalTaylorThermalMixedBook.change]
      using WilsonConditionalTaylorThermalMixedBook.before P R room z a b h s hk
  have mixV := mix (unit_test d) (unitGrade (G:=G) (d:=d))
  have mixF : zeroBefore (WilsonConditionalTaylorThermalMixedDivision.square (C z*B z 1) (C (z+a)*B (z+a) 1) (C (z+b)*B (z+b) 1) (C (z+a+b)*B (z+a+b) 1)) (w+4) := by
    simp only [norm]
    exact mix test grade
  have calc4 := purchased (piv (z+a+b)) early (first a) (first b) (vac _ _) (vac _ _) mixV mixF
  simp only [norm] at calc4
  have pay (u : ℕ→ℝ) (k : ℕ) : coeff k (C u)=ranking P d u f k := rfl
  refine ⟨fun k hk => by simpa only [difference,WilsonConditionalTaylorThermalMixedDivision.square,map_sub,pay] using calc4.1 k hk,?_⟩
  let A := (ambient t room).average μ
  let F := field (d:=d) f w
  let Qa := vertex (G:=G) t a
  let Qb := vertex (G:=G) t b
  let m := scale P t
  have mass : m≠0 := by rw [show m=bareRank P d z 1 0 from (vacuum P R room t z).symm]; exact (pivot P R z room).ne'
  have flat := WilsonConditionalTaylorThermalInteractionDivision.incoming (piv z) early
  have originalField : ranking P d z f w = A F := by
    have h := flat.1
    simp only [B,coeff_mk] at h
    change ranking P d z f w*bareRank P d z 1 0=bareRank P d z f w at h
    rw [vacuum P R room t z,WilsonConditionalTaylorThermalBook.source P R room t z test grade] at h
    exact mul_right_cancel₀ mass (h.trans (mul_comm _ _))
  have point (u : ℕ→ℝ) : ranking P d (z+u) f (w+2)-ranking P d z f (w+2) =
      - (A (F*vertex t u)-A F*A (vertex t u)) := by
    have h := WilsonConditionalTaylorThermalQuotient.original P R room t (z+u) z test grade
    have q : ThermalShortcuts.ConnectedWick.quadratic (ThermalShortcuts.ThermalJets.signedForm G d t u) = vertex t u :=
      funext fun x => (ThermalShortcuts.ThermalJets.signed_half t u x).symm
    simpa only [add_sub_cancel_left,ThermalShortcuts.ConnectedWick.connected,q] using h
  have leftVac : bareRank P d (z+a+b) (1:Config G n→ℝ) 2 - bareRank P d (z+a) 1 2 = -(m*A Qb) := by
    simpa only [add_sub_cancel_left] using vacuumChange P R room t (z+a+b) (z+a)
  have rightVac : bareRank P d (z+a+b) (1:Config G n→ℝ) 2 - bareRank P d (z+b) 1 2 = -(m*A Qa) := by
    simpa only [show z+a+b-(z+b)=a by abel] using vacuumChange P R room t (z+a+b) (z+b)
  have mixedVac : WilsonConditionalTaylorThermalMixedBook.change P d z a b (1:Config G n→ℝ) 4 =
      m*A (Qa*Qb) := by
    simpa only [Nat.zero_add,unitField,mul_one] using WilsonConditionalTaylorThermalMixedBook.source P R room t z a b (unit_test d) unitGrade
  have h := calc4.2
  simp only [WilsonConditionalTaylorThermalMixedDivision.square,map_sub,pay,B,coeff_mk] at h
  change difference P d z a b f (w+4)*bareRank P d (z+a+b) 1 0 =
    WilsonConditionalTaylorThermalMixedBook.change P d z a b f (w+4) -
    ranking P d z f w*WilsonConditionalTaylorThermalMixedBook.change P d z a b 1 4 -
    (ranking P d (z+a) f (w+2)-ranking P d z f (w+2))*(bareRank P d (z+a+b) 1 2-bareRank P d (z+a) 1 2) -
    (ranking P d (z+b) f (w+2)-ranking P d z f (w+2))*(bareRank P d (z+a+b) 1 2-bareRank P d (z+b) 1 2) at h
  rw [vacuum P R room t (z+a+b),WilsonConditionalTaylorThermalMixedBook.source P R room t z a b test grade,
    originalField,mixedVac,point a,point b,leftVac,rightVac] at h
  change difference P d z a b f (w+4)*m=m*A ((Qa*Qb)*F) - A F*(m*A (Qa*Qb)) -
    (-(A (F*Qa)-A F*A Qa))*(-(m*A Qb)) - (-(A (F*Qb)-A F*A Qb))*(-(m*A Qa)) at h
  change difference P d z a b f (w+4)=WilsonConditionalTaylorThermalCumulant.third A Qa Qb F
  unfold WilsonConditionalTaylorThermalCumulant.third
  rw [mul_comm Qa F,mul_comm Qb F]
  apply mul_right_cancel₀ mass
  linear_combination h

end YM.Integration.WilsonConditionalTaylorThermalMixedQuotient
