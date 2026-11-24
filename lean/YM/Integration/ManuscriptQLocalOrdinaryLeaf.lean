import YM.Integration.QLocalInheritedRegularSlots
import YM.Integration.ManuscriptQLocalOrdinaryScale
import YM.Integration.ManuscriptQLocalOrdinaryExtraMark
import YM.MergeProof.Fruit

/-! A true independent marked reading of one original submitted ordinary row. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ManuscriptQLocalOrdinaryLeaf
open Function Set Lattice RG Tree Wilson Pressure MeasureTheory Marker
open PhysicalNext PhysicalNext.Repeat Progress.DirectedRecipe MergeProof
open Comparison.RG02 ConnectedActivityE6 Greenbelt Lotus
open scoped Topology BigOperators Classical

variable {G : Gauge} {f : Side} {V ι : Type} [DecidableEq V] {Γ : Census V}

def leaf (R : Rep G f) (z : RegularAddress f) (F : Config G f → ℝ) {u : ℝ}
    (regular : R.p.Regular z.support F) (bound : R.p.supBounds z.site z.support F u)
    (tag : ℕ) : Lotus.Leaf (QLocalInheritedRegularSlots.carrier R) := by
  let i := blankRow f (z,tag)
  have addr : (QLocalInheritedRegularSlots.carrier R).activities.reg i=z :=
    (QLocalInheritedRegularSlots.reserved R z tag).1
  refine ⟨.logKey i,masked R.p.threshold z.support F,?_,?_,
    (QLocalInheritedRegularSlots.reserved R z tag).2,u,?_,?_,
    masked_measurable _ _ _ regular.borel⟩
  · change UsesFinal _ ((QLocalInheritedRegularSlots.carrier R).activities.reg i).support _
    rw [addr]
    intro U V agree flags_eq
    have healthy : Healthy R.p.threshold z.support U ↔ Healthy R.p.threshold z.support V := by
      unfold Healthy
      change z.support ∩ flags R.p.threshold U = z.support ∩ flags R.p.threshold V at flags_eq
      simp only [Finset.disjoint_iff_inter_eq_empty, flags_eq]
    by_cases h : Healthy R.p.threshold z.support U
    · rw [masked_eq _ _ _ _ h,masked_eq _ _ _ _ (healthy.mp h),regular.sites U V agree]
    · rw [masked_ne _ _ _ _ h,masked_ne _ _ _ _ (mt healthy.mpr h)]
  · change ∀ U, _ ≠ 0 → Healthy R.p.threshold ((QLocalInheritedRegularSlots.carrier R).activities.reg i).support U
    rw [addr]
    intro U value
    exact of_not_not fun bad => value (masked_ne _ _ _ _ bad)
  · intro U
    by_cases h : Healthy R.p.threshold z.support U
    · rw [masked_eq _ _ _ _ h]
      exact bound.2 U h [] (by simp) (by simp)
    · rw [masked_ne _ _ _ _ h,norm_zero]
      exact bound.1
  · intro g U
    have healthy : Healthy R.p.threshold z.support (gauge g U) ↔ Healthy R.p.threshold z.support U := by
      unfold Healthy
      rw [gauge_flags]
    by_cases h : Healthy R.p.threshold z.support U
    · rw [masked_eq _ _ _ _ (healthy.mpr h),masked_eq _ _ _ _ h,regular.symmetry g U]
    · rw [masked_ne _ _ _ _ (mt healthy.mp h),masked_ne _ _ _ _ h]

variable (R : Rep G f) (shift : ℝ) (i : ℕ) {u : ℝ}
variable (reg : R.p.Regular (R.activities.reg i).support (R.activities.E i))
  (bill : R.p.supBounds (R.activities.reg i).site (R.activities.reg i).support (R.activities.E i) u)

def source (tag : ℕ) : Lotus.Leaf (QLocalInheritedRegularSlots.carrier (ManuscriptQLocalOrdinaryScale.carrier R shift)) :=
  leaf (ManuscriptQLocalOrdinaryScale.carrier R shift) (R.activities.reg i) (R.activities.E i) reg bill tag

theorem actual (tag : ℕ) (U : Config G f) :
    (source R shift i reg bill tag).ingredient U=R.activities.regularOccurrence R.p i U := rfl

theorem crest (tag : ℕ) : (source R shift i reg bill tag).crest=(R.activities.reg i).support :=
  congrArg RegularAddress.support (QLocalInheritedRegularSlots.reserved (ManuscriptQLocalOrdinaryScale.carrier R shift) (R.activities.reg i) tag).1

theorem value_price (tag : ℕ) : (source R shift i reg bill tag).weight=u := rfl

/-- Repeated physical supports have distinct reserve addresses and every
finite background menu, including the original compulsory keys, is allowed. -/
theorem fresh [Fintype ι] (m : ι→Menu.Hat Γ (QLocalInheritedRegularSlots.carrier (ManuscriptQLocalOrdinaryScale.carrier R shift))) :
    ∃ tag : ℕ,∀ j,(source R shift i reg bill tag).turn≠(m j).M.turn := by
  classical
  let k := fun t : ℕ=>Lotus.Wing.logKey (blankRow f ((R.activities.reg i),t))
  have inj : Injective k := by
    intro t t' h
    exact congrArg Prod.snd ((blankRow f).injective (Lotus.Wing.logKey.inj h))
  have finite : (k ⁻¹' Set.range (fun j=>(m j).M.turn)).Finite :=
    (Set.finite_range _).preimage inj.injOn
  obtain ⟨t,_,ht⟩ := (Set.infinite_univ : Set.Infinite (Set.univ : Set ℕ)).exists_notMem_finset
    finite.toFinset
  refine ⟨t,fun j hj=>ht ?_⟩
  exact finite.mem_toFinset.mpr ⟨j,hj.symm⟩

def mass : ℝ := R.p.mass (R.activities.reg i).support u

include bill in
theorem mass_nonnegative : 0 ≤ mass R i (u:=u) :=
  mul_nonneg (Real.exp_pos _).le bill.1

include shift reg bill in
theorem zero_mass (b : mass R i (u:=u)=0) (U : Config G f) :
    R.activities.regularOccurrence R.p i U=0 := by
  have hu : u=0 := (mul_eq_zero.mp b).resolve_left (Real.exp_pos _).ne'
  have h := (source R shift i reg bill 0).earn U
  rw [actual,value_price,hu,norm_le_zero_iff] at h
  exact h

variable [Fintype V]

def slot (Γ : Census V) := Order.Join.pair Γ.quiet ManuscriptQLocalOrdinaryExtraMark.full

theorem occupied : (slot Γ).val.Nonempty := by
  refine ⟨Sum.inr (0 : Fin 1),?_⟩
  simp [slot,Order.Join.pair,ManuscriptQLocalOrdinaryExtraMark.full]

def hat (tag : ℕ) : Menu.Hat (Order.Board Γ 1) (QLocalInheritedRegularSlots.carrier (ManuscriptQLocalOrdinaryScale.carrier R shift)) where
  M := source R shift i reg bill tag
  s := slot Γ
  shiny := occupied
  charge := -(mass R i (u:=u) : ℂ)⁻¹

theorem signed (tag : ℕ) (U : Config G f) :
    (mass R i (u:=u) : ℂ)*(hat R shift i reg bill (Γ:=Γ) tag).charge*
      ((hat R shift i reg bill (Γ:=Γ) tag).M.ingredient U : ℂ)=
    -(R.activities.regularOccurrence R.p i U : ℂ) := by
  change (mass R i (u:=u) : ℂ)*(-(mass R i (u:=u) : ℂ)⁻¹)*
      (R.activities.regularOccurrence R.p i U : ℂ)=_
  by_cases h : mass R i (u:=u)=0
  · rw [zero_mass R shift i reg bill h U]
    simp
  · have h' : (mass R i (u:=u) : ℂ)≠0 := by exact_mod_cast h
    field_simp

end YM.Integration.ManuscriptQLocalOrdinaryLeaf
