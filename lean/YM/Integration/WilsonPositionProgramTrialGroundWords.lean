import YM.Integration.WilsonPositionProgramTrialGroundProjection
import YM.Integration.WilsonThermometerRegisteredGroundInk

/-! Every occupied original curvature word keeps its own thermal pole and
its measured coefficient. Its Gaussian salary is fixed before both sides
and all positions, even on the diagonal. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialGroundWords
open Finset Lattice Wilson RG Source Labels PhysicalNext.Repeat.Legato
open Next.Rank.Normal PertExtension PertExtension.Orb
open WilsonThermometerDeclaredSeeds WilsonOriginalStarSceneWords
open WilsonThermometerRegisteredGroundWords WilsonMaxwellThermometerGroundInversion
open WilsonThermometerRegisteredGroundInk
open scoped Classical BigOperators

theorem bounded {A V:Type*} [DecidableEq A] (tag:A→V)(s:Finset A):
    ∃M:ℝ,0≤M ∧ ∀Q:Symmetric V,(∀x y,‖Q.cov x y‖≤2)→‖blend Q 0 (glyphs tag s)‖≤M:=by
  induction s using Finset.strongInduction with
  | H s ih =>
    rcases s.eq_empty_or_nonempty with nil|occupied
    · subst s
      exact ⟨1,zero_le_one,fun Q _=>by simp [glyphs,fresh]⟩
    obtain ⟨i,hi⟩:=occupied
    choose c cpos current using fun j:A=>ih ((s.erase i).erase j)
      ((erase_subset _ _).trans_ssubset (erase_ssubset hi))
    refine ⟨∑j∈s.erase i,2*c j,Finset.sum_nonneg (fun j _=>mul_nonneg (by norm_num) (cpos j)),?_⟩
    intro Q price
    rw [← insert_erase hi,spring _ _ _ _ (notMem_erase _ _)]
    simp only [Pi.zero_apply,zero_mul,zero_add,erase_insert (notMem_erase i s)]
    exact (norm_sum_le ..).trans (sum_le_sum fun j _=> by
      rw [norm_mul]
      exact mul_le_mul (price _ _) (current j Q price) (norm_nonneg _) (by norm_num))

variable {G:Gauge} (R:Run G) {V:Type} [Fintype V](d:V→ℕ)
    (b:(j:V)→Choice R d j)(place:V→Fin 3)
local notation "e" j:max => WilsonThermometerDeclaredSeeds.entry R d j (b j)

/-- The factor left outside is the exact original coefficient on this socket. -/
theorem original :
    ∃M:ℝ,0≤M ∧ ∀{n:Side}(ev:Even n.val)(sites:Fin 3 → Cover)(g τ:ℝ)
      (v:(j:V)→R.family.label (d j))(a:V→ℂ),
      ‖blend (earned ev sites) 0 (sheet R d place g τ v (fun j (_:Unit)=>a j) () b)‖
        ≤M*‖∏j:V,a j*scalar R d g τ v (e j)‖:=by
  choose c cp hc using fun h:Colors R d b=>bounded
    (WilsonThermometerRegisteredGroundWords.tag R d b place h) univ
  refine ⟨∑h:Colors R d b,‖(cash R d b h:ℂ)‖*c h,
    sum_nonneg fun h _=>mul_nonneg (norm_nonneg _) (cp h),?_⟩
  intro n ev sites g τ v a
  simp only [sheet,map_sum,map_smul,smul_eq_mul,Finset.sum_mul]
  apply (norm_sum_le ..).trans
  refine sum_le_sum fun h _=>?_
  rw [norm_mul,norm_mul]
  calc _ ≤ (‖∏j:V,a j*scalar R d g τ v (e j)‖*‖(cash R d b h:ℂ)‖)*c h :=
      mul_le_mul_of_nonneg_left
        (hc h (earned ev sites) (WilsonPositionProgramTrialGroundProjection.original ev sites)) (by positivity)
    _ = _ := by ring


end YM.Integration.WilsonPositionProgramTrialGroundWords
end
