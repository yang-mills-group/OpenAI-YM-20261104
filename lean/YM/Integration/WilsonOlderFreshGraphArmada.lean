import YM.Integration.WilsonOlderFreshGraphVote
import YM.QuadraticLocal.Germ.Annual

/-! The all-rank independent graph has an actual physical source wallet and
a single occupied test. Its once-chosen radius pays the original row salary.
The kernel at that scalar name is zero. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonOlderFreshGraphArmada
open Function Filter Finset Lattice Laurent RG Wilson Marker Gauge
open Push Push.AbsoluteSums Paths Animals ConnectedActivityE6 QuadraticLocal QuadraticLocal.Sunrise
open QuadraticLocal.Poetry QuadraticLocal.Earn QuadraticLocal.Mentor AllOrder AllOrder.Ink
open scoped Classical BigOperators Topology
open WilsonOlderFreshGraphVote
variable {G:Gauge}{n:Side}{Q d:ℕ}
variable {P:Earn.Passport n Unit}{H:Marker.Census Unit}(S:Earn.Binder P H)
variable (W:Fin (Q+1)→Poetry.Roll G Unit) (C:Fin (Q+1)→ℝ) (σ:ℝ)
variable (paid:∀j,(W j).Faith {()} () (j.val+d+2) (2*σ) (C j))
variable (legal:∀j,(W j).honest) (d0:0<d)
variable (A:Unit→Set ℂ)
def value (t:Affinity.Wallet A):ℂ:=(t ()).val
local notation "M"=>material S W C σ paid legal d0 (value A)
def gross:ℝ:=Real.exp (σ*S.length)*(∑j,C j)
lemma full_mode : S.mode.val=univ:=by
  apply Finset.eq_univ_of_forall
  intro v
  exact (Subsingleton.elim v S.front) ▸ S.east

include paid in
theorem countable : Countable (Name W) := by
  haveI (j:Fin (Q+1)):Countable {u:(W j).Ty//0<((W j).leg u).atom.magnitude}:=by
    apply Set.countable_coe_iff.mpr
    apply (paid j).price.2.1.countable_support.mono
    intro u hu
    exact ne_of_gt (mul_pos hu (Real.exp_pos _))
  infer_instance

theorem tests : Earn.Tableau (fun _=>(⊥:Submodule ℝ ℂ)) A M:=by
  constructor
  intro z
  have seed:Affinity.Attn (fun _=>(⊥:Submodule ℝ ℂ)) A S.mode.val (value A):=by
    refine ⟨fun t u eq=>congrArg Subtype.val (eq () ?_), ?_, ?_⟩
    · simp [full_mode S]
    · intro i hi t x y z a b add
      cases i
      simpa [value] using add
    · intro i hi t zero
      cases i
      exact (Submodule.mem_bot ℝ).mp zero
  simpa only [material,WilsonOlderFreshGraphMount.ballot,Complex.real_smul] using
    seed.scale (WilsonOlderFreshGraphMount.fare ((W z.1).leg z.2.1) σ)

theorem original (σ0:0 ≤ σ) (cap:∀t,‖value A t‖≤1)
    (w:ℝ) (gain:0<w) (budget:w*gross S C σ≤1)
    {ord seats shelf:ℕ}(qo:Q ≤ ord)(seats1:1 ≤ seats)(ds:d ≤ shelf):
    Scene.Armada M (fun _=>w) (fun _=>d) σ 1 ord seats shelf:=by
  constructor
  · constructor
    · intro mode
      exact (card_le_univ _).trans (by simpa using seats1)
    · intro mode
      have h:(∑ _i∈mode.val,d)≤∑ _i:Unit,d:=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _=>Nat.zero_le _)
      exact h.trans (by simpa using ds)
  · exact fun _=>gain
  · intro x
    apply Push.Local.sumBudget_mono (budget_scale gain.le (before_tests S W C σ paid legal d0 (value A) σ0)) _ _ budget
    · intro z
      have toll:Poly.toll (fun _:Unit=>w) (M z).mode=w:=by
        change (∏ _v ∈ S.mode.val,w)=w
        simp [full_mode S]
      try dsimp only
      rw [toll]
      split_ifs
      · exact mul_nonneg gain.le  (mul_nonneg (M z).sound.le (Real.exp_pos _).le)
      · exact le_rfl
    · intro z
      have toll:Poly.toll (fun _:Unit=>w) (M z).mode=w:=by
        change (∏ _v ∈ S.mode.val,w)=w
        simp [full_mode S]
      try dsimp only
      rw [toll]
      split_ifs
      · exact le_rfl
      · exact mul_nonneg gain.le (mul_nonneg (M z).sound.le (Real.exp_pos _).le)
  · constructor
    · intro z
      exact (WilsonOlderFreshGraphMount.enrolled S ((W z.1).leg z.2.1) z.1 d d0
        ((paid z.1).pinned z.2.1) (legal z.1 z.2.1) z.2.2 σ (value A) cap).2.1
    · intro z
      change z.1.val ≤ ord ∧ d=∑ v∈S.mode.val,d
      exact ⟨(Nat.le_of_lt_succ z.1.isLt).trans qo,by simp [full_mode S]⟩
  · intro z
    exact (WilsonOlderFreshGraphMount.enrolled S ((W z.1).leg z.2.1) z.1 d d0
      ((paid z.1).pinned z.2.1) (legal z.1 z.2.1) z.2.2 σ (value A) cap).1
end YM.Integration.WilsonOlderFreshGraphArmada
end
