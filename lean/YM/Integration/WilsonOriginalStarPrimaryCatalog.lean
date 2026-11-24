import YM.Integration.WilsonOriginalStarIncomingRead
import YM.Integration.ActualRunCurvaturePackets

/-! The original printed star stencil at its genuine coordinates, including its unmasked marked scalar. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalStarPrimaryCatalog
open Function Finset Lattice Wilson RG Source Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Tint QuadraticLocal.Affinity
open PhysicalNext.Repeat.Legato Push.Local Push.AbsoluteSums AnalyticNext WilsonRetainedMarkedInletRegular
open ActualRunPhysicalPages ActualRunCurvaturePackets
open Next.Foundations Ac
open scoped BigOperators Classical Topology
variable {G : Gauge} (R : Run G) (N p k d : ℕ) (upper : k≤N) (ref : R.family.ref d≤k)
   {V T : Type} [DecidableEq V] {J : Census V} (o : V → Site (R.family.side k p)) (j : V)
   (v : R.family.label d) (t : T → ℂ)
local notation "P_" => R.family.path.rep N p k
local notation "F_" => R.family.labels.level d
local notation "C_" => R.family.localSection d

omit [DecidableEq V] in
private theorem root : o j∈(C_).footprint (o j) :=
  Finset.mem_image.mpr ⟨0,(R.makes.sections d).anchored,by simp⟩

def catalogue : Lamps T Bool G (P_).p o J where
  mode _ := J.fire j
  live _ := J.fire_hot j
  address _ := ⟨o j,(C_).footprint (o j),root R p k d o j⟩
  roots _ b hit := (show b=j from Finset.mem_singleton.mp hit) ▸ root R p k d o j
  nominal x i := if i=true then fun _=>t x*v 0 else (t x) • kernel R N p k d ((F_).core v) (o j)
  legal x i := by split; exact regular_const _; exact regular_smul _ (priced R N p k d upper ref _ _).1
  clear i := i=true
  pure _ i _ take := by simp only [if_pos take]

local notation "M_" => catalogue (J:=J) R N p k d upper ref o j v t
def primary (U : Config G (R.family.side k p)) : ℂ :=
  v 0 + masked (P_).p.threshold ((C_).footprint (o j))
    (kernel R N p k d ((F_).core v) (o j)) U

omit [DecidableEq V] in
theorem printed (U : Config G (R.family.side k p)) :
    primary R N p k d o j v U = v 0 +
      masked (P_).p.threshold ((C_).footprint (o j))
        (fun X=>∑ i:(F_).Index, ((((P_).p.threshold)⁻¹^ActualRunGradedKernels.rank R d i:ℝ):ℂ) *
            ((F_).core v i) * basisValue (ofRun R d) i (o j) X) U := by
  unfold primary
  rw [show kernel R N p k d ((F_).core v) (o j)=_ from funext (run_kernel R N p k d ((F_).core v) (o j))]

theorem filed [Fintype V] (x : T) (U : Config G (R.family.side k p)) :
    ((M_).log x U).part (J.fire j)=t x*primary R N p k d o j v U := by
  rw [Lamps.log,Poly.share Summable.of_finite,tsum_fintype,Fintype.sum_bool]
  unfold Lamps.frame Lamps.light Lamps.ground catalogue primary
  simp only [Bool.false_eq_true,if_pos,if_neg,not_false_eq_true,Poly.part_send]
  by_cases h : Healthy (P_).p.threshold ((C_).footprint (o j)) U
  · rw [masked_eq _ _ _ _ h,masked_eq _ _ _ _ h]
    simp only [Pi.smul_apply,smul_eq_mul]
    ring
  · rw [masked_ne _ _ _ _ h,masked_ne _ _ _ _ h]
    ring

def amount (i : Bool) : ℝ :=
    if i=true then ‖v 0‖ else
    moving (P_).p (coverNumber (P_).p.B ((C_).footprint (o j))) * price R k d ((F_).core v)

def rent (w : V → ℝ) (a : ℝ) : ℝ :=
  ∑ i : Bool,w j*amount R N p k d o j v i *
    Real.exp (a*coverNumber (P_).p.B ((C_).footprint (o j)))

theorem funded (w : V → ℝ) (hw : ∀ i, 0<w i) (a : ℝ) (ht : ∀x, ‖t x‖≤1) :
    (M_).Paid w (P_).p.B a (rent R N p k d o j v w a) := by
  let F := (C_).footprint (o j)
  let m := moving (P_).p (coverNumber (P_).p.B F)
  let c := price R k d ((F_).core v)
  obtain ⟨hreg,hcore⟩ := priced R N p k d upper ref ((F_).core v) (o j)
  have hpos : 0 ≤ m := by unfold m moving; positivity
  have cpos : 0≤c := hcore.1
  have nni (i:Bool) : 0≤amount R N p k d o j v i := by
    unfold amount
    split; exact norm_nonneg _; exact mul_nonneg hpos cpos
  refine ⟨_, nni,?_,?_⟩
  · intro i x u hu
    have hit : u∈F := hu
    change (P_).p.supBounds u F (if i=true then fun _=>t x*v 0 else t x • kernel R N p k d ((F_).core v) (o j))
      (amount R N p k d o j v i)
    unfold amount
    by_cases truth : i=true
    · simp only [if_pos truth]
      apply bound_weaken (bound_const _)
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (ht x)
    simp only [if_neg truth]
    have moved : (P_).p.supBounds u F (kernel R N p k d ((F_).core v) (o j)) (m*c) := by
      apply bound_weaken (bound_shift hcore hreg u)
      apply mul_le_mul_of_nonneg_right _ cpos
      rw [←pow_mul]
      unfold m moving
      have loc := Corona.extent F (P_).p.B (root R p k d o j) hit
      gcongr
    exact bound_weaken (bound_smul (t x) moved) (mul_le_of_le_one_left (mul_nonneg hpos cpos) (ht x))
  · intro u
    have nn i : 0≤w j*amount R N p k d o j v i*Real.exp (a*coverNumber (P_).p.B F) :=
      mul_nonneg (mul_nonneg (hw j).le (nni i)) (Real.exp_nonneg _)
    change SumBudget (fun i:Bool=>if u∈F then Poly.toll w (J.fire j)*amount R N p k d o j v i*
      Real.exp (a*coverNumber (P_).p.B F) else 0) _
    simp only [Poly.solo_toll]
    refine ⟨fun i=>ite_nonneg (nn i) le_rfl,Summable.of_finite,?_⟩
    rw [tsum_fintype]
    apply Finset.sum_le_sum
    intro i _
    split; exact le_rfl; exact nn i

end YM.Integration.WilsonOriginalStarPrimaryCatalog
