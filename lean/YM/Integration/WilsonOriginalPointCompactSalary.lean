import YM.Integration.WilsonOriginalPointCompactRoster

/-! The joint original salaries for compact words with independently located roots. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalPointCompactSalary
open Function Finset Lattice Laurent RG Wilson Marker Gauge
open Push Push.AbsoluteSums Paths Animals ConnectedActivityE6 QuadraticLocal QuadraticLocal.Sunrise
open QuadraticLocal.Poetry QuadraticLocal.Earn QuadraticLocal.Mentor AllOrder AllOrder.Ink QuadraticLocal.Affinity
open WilsonOriginalPointCompactRoster
open scoped Classical BigOperators

variable {G:Gauge} {n:Side} {I:Type} [Fintype I] {q:ℕ} {σ:ℝ}
  (owner:I→Fin 3) (grades:Fin 3→ℕ) (sites:Fin 3→Site n)
  (T:(i:I)→WilsonOlderFreshGraphSlate.Copy G (grades (owner i)) q σ)
  (A:Fin 3→Set ℂ) (charge:I→ℂ)

local notation "J" => Stock.census (Fin 3)
local notation "here" i:max => home sites (owner i)
local notation "unitSet" i:max => alone A (owner i)
local notation "coin" i:max => (1+‖charge i‖)
local notation "cost" i:max => (T i).cost (here i)
local notation "single" i:max z:max => (T i).rows (here i) (unitSet i) z
local notation "M" => rows owner grades sites T A charge

def invoice (w:Fin 3→ℝ) : ℝ := ∑i:I,(w (owner i)*(coin i))*(cost i)

omit [Fintype I] in
theorem original_salary (i:I) (σ0:0 ≤ σ) :
    SumBudget (fun z:(T i).Roster=>(single i z).height σ) (cost i) :=
  WilsonOlderFreshGraphVote.before_tests (here i) (T i).roll (T i).fare σ (T i).paid
    (T i).legal (T i).positive (WilsonOlderFreshGraphArmada.value (unitSet i)) σ0

theorem booked (σ0:0 ≤ σ) (w:Fin 3→ℝ) (hw:∀v,0<w v) :
    Offers M w σ (invoice owner grades sites T charge w) := by
  intro x
  let loaded (i:I) (z:(T i).Roster):=if (M ⟨i,z⟩).center=x then
    Poly.toll w (M ⟨i,z⟩).mode * (M ⟨i,z⟩).height σ else 0
  have each (i:I):SumBudget (loaded i) ((w (owner i)*(coin i))*(cost i)) := by
    have real:=original_salary owner grades sites T A i σ0
    have non:0 ≤ w (owner i)*(coin i):=mul_nonneg (hw _).le (by positivity)
    have zmod (z:(T i).Roster):Poly.toll w (M ⟨i,z⟩).mode=w (owner i):=by
      rw [support]
      simp [Poly.toll,Census.fire]
    apply Push.Local.sumBudget_mono (budget_scale non real)
    · intro z
      dsimp only [loaded]
      split_ifs
      · rw [zmod]
        exact mul_nonneg (hw _).le (mul_nonneg (M ⟨i,z⟩).sound.le (Real.exp_pos _).le)
      · exact le_rfl
    · intro z
      dsimp only [loaded]
      split_ifs
      · rw [zmod,WilsonOriginalPointCompactRoster.height]
        exact le_of_eq (mul_assoc _ _ _).symm
      · exact mul_nonneg non (mul_nonneg (single i z).sound.le (Real.exp_pos _).le)
    · exact le_rfl
  apply Push.Local.sumBudget_sigma each
  exact budget_finite (fun i=>budget_nonneg (each i)) le_rfl

theorem stocks (σ0:0 ≤ σ) (w:Fin 3→ℝ) (hw:∀v,0<w v)
    (unit:∀v (t:ℂ), t∈A v→‖t‖ ≤ 1) (order seats shelf:ℕ) (qo:q ≤ order)
    (size:3 ≤ seats) (room:(∑v:Fin 3,grades v) ≤ shelf) :
    Scene.Armada M w grades σ (invoice owner grades sites T charge w) order seats shelf := by
  have bill (i:I):0 ≤ cost i:=budget_nonneg (original_salary owner grades sites T A i σ0)
  have localStock (i:I):Scene.Armada ((T i).rows (here i) (unitSet i)) (fun _=>1)
      (fun _=>grades (owner i)) σ (1+cost i) order seats shelf := by
    apply (T i).earnings (here i) (unitSet i) σ0 _
    · exact zero_lt_one
    · linarith [bill i]
    · simp
    · exact qo
    · omega
    · exact (Finset.single_le_sum (f:=grades) (fun _ _=>Nat.zero_le _) (Finset.mem_univ (owner i))).trans room
    · intro a
      exact unit (owner i) (a ()).val (a ()).property
  refine ⟨⟨?_,?_⟩,hw,booked owner grades sites T A charge σ0 w hw,⟨?_,?_⟩,?_⟩
  · intro s
    exact (Finset.card_le_univ s.val).trans (by simpa using size)
  · intro s
    exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s.val) (fun _ _ _=>Nat.zero_le _)).trans room
  · intro z
    exact (localStock z.1).purchases.1 z.2
  · intro z
    change z.2.1.val ≤ order ∧ grades (owner z.1)=∑v∈({owner z.1}:Finset (Fin 3)),grades v
    exact ⟨(Nat.le_of_lt_succ z.2.1.isLt).trans qo,by simp⟩
  · intro z
    exact WilsonOriginalPointCompactRoster.honored owner grades sites T A charge z ((localStock z.1).honor z.2)

end YM.Integration.WilsonOriginalPointCompactSalary
