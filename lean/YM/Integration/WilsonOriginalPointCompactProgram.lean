import YM.Integration.WilsonOriginalPointCompactSalary

/-! All three independently placed compact fields form one testable, paid genuine semester pupil. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPointCompactProgram
open Function Finset Lattice Laurent RG Wilson Marker Gauge
open Push Push.AbsoluteSums Paths Animals ConnectedActivityE6 QuadraticLocal QuadraticLocal.Sunrise
open QuadraticLocal.Poetry QuadraticLocal.Earn QuadraticLocal.Mentor AllOrder AllOrder.Ink QuadraticLocal.Affinity
open WilsonOriginalPointCompactRoster WilsonOriginalPointCompactSalary
open scoped Classical BigOperators

private theorem test_at (A:Fin 3→Set ℂ) (v:Fin 3) (c:ℂ) :
    Attn (fun _=>(⊥:Submodule ℝ ℂ)) A {v} (fun t=>c*(t v).val) := by
  refine ⟨fun t u p=>congrArg (fun y=>c*y) (congrArg Subtype.val (p v (by simp))),?_,?_⟩
  · intro i hi t x y z a b hy
    obtain rfl:=Finset.mem_singleton.mp hi
    simp only [Function.update_self]
    rw [hy]
    simp only [Complex.real_smul]
    ring
  · intro i hi t ht
    obtain rfl:=Finset.mem_singleton.mp hi
    simp [(Submodule.mem_bot ℝ).mp ht]

variable {G:Gauge} {n:Side} {I:Type} [Fintype I] {q:ℕ} {σ:ℝ}
  (owner:I→Fin 3) (grades:Fin 3→ℕ) (sites:Fin 3→Site n)
  (T:(i:I)→WilsonOlderFreshGraphSlate.Copy G (grades (owner i)) q σ)
  (A:Fin 3→Set ℂ) (charge:I→ℂ)
local notation "M" => rows owner grades sites T A charge

omit [Fintype I] in
theorem tested : Tableau (fun _=>(⊥:Submodule ℝ ℂ)) A M := by
  constructor
  intro z
  let amt:=WilsonOlderFreshGraphMount.fare (((T z.1).roll z.2.1).leg z.2.2.val) σ
  have paid:=test_at A (owner z.1) (charge z.1*(amt:ℂ))
  change Attn (fun _=>(⊥:Submodule ℝ ℂ)) A {owner z.1}
    (fun t=>charge z.1*((amt:ℂ)*(t (owner z.1)).val))
  simpa only [mul_assoc] using paid


theorem original (σ0:0 ≤ σ) (unit:∀v (t:ℂ), t∈A v→‖t‖ ≤ 1)
    {b:ℝ} (pos:0<b) {order seats stage vac shelf:ℕ} (size:3 ≤ seats)
    (reserve:(∑v:Fin 3,grades v) ≤ shelf) (qo:q ≤ order) (qs:q ≤ shelf)
    (start:order+1 ≤ stage) (expense:order+(∑v:Fin 3,grades v) ≤ Burn.horizon vac+2) :
    ∃ w:Fin 3→ℝ,(∀v,0<w v) ∧ WilsonOriginalPointCompactSalary.invoice owner grades sites T charge w ≤ b ∧
      Scene.Armada M w grades σ (WilsonOriginalPointCompactSalary.invoice owner grades sites T charge w) order seats shelf ∧
      Tableau (fun _=>(⊥:Submodule ℝ ℂ)) A M ∧ Cruise.Voter M σ order seats stage vac shelf := by
  let total:=WilsonOriginalPointCompactSalary.invoice owner grades sites T charge (fun _=>1)
  have non:0 ≤ total:=by
    unfold total WilsonOriginalPointCompactSalary.invoice
    exact Finset.sum_nonneg (fun i _=> mul_nonneg (by positivity)
      (budget_nonneg (original_salary owner grades sites T A i σ0)))
  let w:Fin 3→ℝ:=fun _=>b/(1+total)
  have hw (v:Fin 3):0<w v:=div_pos pos (by linarith)
  have bill:WilsonOriginalPointCompactSalary.invoice owner grades sites T charge w=(b/(1+total))*total:=by
    unfold WilsonOriginalPointCompactSalary.invoice w total
    simp only [one_mul,WilsonOriginalPointCompactSalary.invoice,Finset.mul_sum,mul_assoc]
  have limit:WilsonOriginalPointCompactSalary.invoice owner grades sites T charge w ≤ b:=by
    rw [bill,div_mul_eq_mul_div,div_le_iff₀ (by linarith)]
    nlinarith
  have held:=stocks owner grades sites T A charge σ0 w hw unit order seats shelf qo size reserve
  have due:=held.purchases.2
  refine ⟨w,hw,limit,held,tested owner grades sites T A charge,fun z=>?_,fun s=>?_,start,fun club=>?_⟩
  · exact ⟨held.honor z,held.purchases.1 z,(Nat.le_of_lt_succ z.2.1.isLt).trans qs,
      (Finset.single_le_sum (f:=grades) (fun _ _=>Nat.zero_le _) (Finset.mem_univ (owner z.1))).trans reserve⟩
  · exact (Finset.card_le_univ s.val).trans (by simpa using size)
  · rw [Press.tall M club grades due]
    exact (Nat.add_le_add_left (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ (Club.alliance M club).val) (fun _ _ _=>Nat.zero_le _)) order).trans expense

end YM.Integration.WilsonOriginalPointCompactProgram
