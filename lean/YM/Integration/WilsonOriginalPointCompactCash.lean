import YM.Integration.WilsonOriginalPointCompactProgram

/-! The published one-source tickets give an explicit common three-color wallet. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPointCompactCash
open Function Finset Lattice Laurent RG Wilson Marker Gauge
open Push Push.AbsoluteSums Paths Animals ConnectedActivityE6 QuadraticLocal QuadraticLocal.Sunrise
open QuadraticLocal.Poetry QuadraticLocal.Earn QuadraticLocal.Mentor AllOrder AllOrder.Ink QuadraticLocal.Affinity
open WilsonOriginalPointCompactRoster
open scoped Classical BigOperators
variable {G:Gauge}{n:Side}{I:Type}[Fintype I]{q:ℕ}{σ:ℝ}
  (owner:I→Fin 3) (grades:Fin 3→ℕ) (sites:Fin 3→Site n)
  (T:(i:I)→WilsonOlderFreshGraphSlate.Copy G (grades (owner i)) q σ) (charge:I→ℂ)

omit [Fintype I] in
theorem own_source (i:I) : (T i).cost (home sites (owner i))=∑j,(T i).fare j := by
  simp [WilsonOlderFreshGraphSlate.Copy.cost,WilsonOlderFreshGraphArmada.gross,home,
    WilsonOriginalStarSceneRows.length]

theorem total (r:ℝ) :
    WilsonOriginalPointCompactSalary.invoice owner grades sites T charge (fun _=>r) =
      r*∑i:I,(1+‖charge i‖)*(∑j,(T i).fare j) := by
  unfold WilsonOriginalPointCompactSalary.invoice
  simp only [own_source,Finset.mul_sum,mul_assoc]

def ceiling (I:Type) [Fintype I] (maxCharge ticket:ℝ) : ℝ :=
  (Fintype.card I:ℝ)*(1+maxCharge)*ticket

theorem bound {cap ticket:ℝ} (funded:∀i:I,(∑j,(T i).fare j) ≤ ticket)
    (amounts:∀i:I,‖charge i‖ ≤ cap) (room:0 ≤ ticket) :
    (∑i:I,(1+‖charge i‖)*(∑j,(T i).fare j)) ≤ ceiling I cap ticket := by
  calc
    _ ≤ ∑_i:I,(1+cap)*ticket:=Finset.sum_le_sum fun i _=>
      (mul_le_mul_of_nonneg_left (funded i) (by positivity)).trans
        (mul_le_mul_of_nonneg_right (by linarith [amounts i]) room)
    _=ceiling I cap ticket:=by simp [ceiling,mul_assoc]

theorem share {b s size:ℝ} (bp:0<b) (size0:0 ≤ size) (s0:0 ≤ s) (covered:s ≤ size) :
    0 ≤ (b/(1+size))*s ∧ (b/(1+size))*s ≤ b := by
  constructor
  · positivity
  · rw [div_mul_eq_mul_div,div_le_iff₀ (by linarith : 0<1+size)]
    exact mul_le_mul_of_nonneg_left (by linarith) bp.le

theorem restored {b size halo gross used:ℝ} (bp:0<b) (size0:0 ≤ size) (hp:0<halo)
    (fee:0 ≤ used) (budget:used ≤ b) :
    let shrink:=1+|gross| * b/halo
    let radius:=(b/(1+size))/shrink
    1 ≤ shrink ∧ 0 < radius ∧ shrink⁻¹*(gross*used) ≤ halo ∧
      radius⁻¹=(1+size)*(b⁻¹+|gross|/halo) := by
  intro shrink radius
  have bound:0 ≤ |gross| * b/halo:=by positivity
  have one:1 ≤ shrink:=by dsimp [shrink]; linarith
  have pos:0 < shrink:=lt_of_lt_of_le zero_lt_one one
  have sized:0<1+size:=by linarith
  refine ⟨one,div_pos (div_pos bp sized) pos,?_,?_⟩
  · rw [inv_mul_eq_div,div_le_iff₀ pos]
    have dominated: gross*used ≤ |gross| * b:=(mul_le_mul_of_nonneg_right (le_abs_self _) fee).trans
      (mul_le_mul_of_nonneg_left budget (abs_nonneg _))
    have receipted:halo*shrink=halo+|gross| * b:=by
      dsimp [shrink]
      field_simp
    linarith
  · dsimp [radius,shrink]
    field_simp [bp.ne',hp.ne',sized.ne']

end YM.Integration.WilsonOriginalPointCompactCash
