import YM.Contact.Detectors
import YangMills.WilsonProof.NativeSupport.YM.Next.MAXWELL.Depth
import YM.Next.MAXWELL.System

/-! Entire Maxwell horizon detected by two fixed sites and one exterior mark. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesTwoSites
open Function Set Maxwell Maxwell.Free Maxwell.Wick
open scoped Classical BigOperators
variable {G : Gauge} (F : Labels.Frames G) (d : ℕ)

private theorem separate : (0 : E4) ≠ basis timeAxis := by
  intro he
  have h := congrArg norm he
  simp at h

def shell (v : (standard F).Ref d) : Exterior (standard F) :=
  ⟨1,pairPoints 0 (basis timeAxis),fun _ => ⟨d,v⟩,pair_ok separate⟩

private theorem scored (v : (Model F).Field d) (w : (standard F).Ref d) :
    (Model F).spectra d v (shell F d w) = bond G 0 (basis timeAxis)
      (address F d v) (address F d ((Model F).project d w)) := by
  rw [shell,← Table.through _ (table_sym F),display,bond_eval]
  congr 1
  funext j
  fin_cases j <;> rfl

/-- Every exterior row consists of precisely one extra field at time distance
one from the central insertion, and these rows jointly identify the entire
original Maxwell horizon. The proof uses genuine time-reflection positivity. -/
theorem fixed : ∃ D : Contacts.Foci (Model F) d, ∀ j : D.index,
    ∃ w : (standard F).Ref d, D.shell j = shell F d w := by
  let B := Module.finBasis ℂ ((Model F).Field d)
  let w (j) := Classical.choose ((Model F).onto d (B j))
  have hw (j) : (Model F).project d (w j) = B j := Classical.choose_spec ((Model F).onto d (B j))
  let query := LinearMap.pi (fun j => (LinearMap.proj (R:=ℂ) (shell F d (w j))).comp ((Model F).spectra d))
  have faithful : Injective query := by
    intro v z same
    have columns (j) : bond G 0 (basis timeAxis) (address F d (v-z)) (address F d (B j)) = 0 := by
      have result := congrFun same j
      change (Model F).spectra d v (shell F d (w j)) = (Model F).spectra d z (shell F d (w j)) at result
      rw [scored,scored,hw] at result
      rw [map_sub,map_sub,LinearMap.sub_apply,result,sub_self]
    have spans (q : (Model F).Field d) : bond G 0 (basis timeAxis) (address F d (v-z)) (address F d q) = 0 := by
      rw [← B.sum_repr q,map_sum,map_sum]
      apply Finset.sum_eq_zero
      intro j _
      rw [map_smul,map_smul,columns,smul_zero]
    have translated : bond G ((-1 : ℝ) • basis timeAxis) 0 = bond G 0 (basis timeAxis) := by
      simpa using (pair_flow (G:=G) ((-1 : ℝ) • basis timeAxis) 0 (basis timeAxis)).symm
    have zero := pair_nonzero timeAxis (address F d (v-z)) (r:=1) zero_lt_one (address_in F d (v-z)) (by
      intro q hq
      rw [translated]
      have he := spans ((fields F d).symm ⟨q,hq⟩)
      change bond G 0 (basis timeAxis) _ ((fields F d) ((fields F d).symm ⟨q,hq⟩)).val = 0 at he
      simpa using he)
    apply sub_eq_zero.mp
    apply address_inj F d
    rwa [map_zero]
  refine ⟨⟨_,inferInstance,fun j => shell F d (w j),fun _ => rfl,query.leftInverse,
    fun v => LinearMap.leftInverse_apply_of_inj (LinearMap.ker_eq_bot.mpr faithful) v⟩,?_⟩
  exact fun j => ⟨w j,rfl⟩

theorem original : ∃ D : Contacts.Foci (Model F) d, ∀ j : D.index,
    (D.shell j).n = 1 ∧ (D.shell j).point 0 = 0 := by
  obtain ⟨D,rows⟩ := fixed F d
  refine ⟨D,fun j => ?_⟩
  obtain ⟨w,hw⟩ := rows j
  rw [hw]
  exact ⟨rfl,rfl⟩

end YM.Integration.WilsonMatrixTicketLanesTwoSites
