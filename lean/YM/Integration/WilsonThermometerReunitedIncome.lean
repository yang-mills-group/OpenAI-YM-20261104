import YM.Integration.WilsonThermometerFiniteModeIncome

/-! Re-enrol each solitary row and the separated mixed rows of one registered marked intake. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerReunitedIncome
open Finset Lattice Wilson RG Marker QuadraticLocal QuadraticLocal.Earn Push.AbsoluteSums
open WilsonPrecontactSeparatedLamps WilsonThermometerFiniteModeIncome
open scoped Classical BigOperators
variable {V ι T : Type} [DecidableEq V] [Fintype V]
    {G : Gauge} {n : Side} {p : BudgetPoint} {o : V → Site n} {R : Census V}

def group (s : R.Mode) : Option V :=
  if h : s.val.card = 1 then some (Finset.card_eq_one.mp h).choose else none

omit [Fintype V] in
private theorem occupied {s : R.Mode} (live : s ≠ R.quiet) : s.val.Nonempty := by
  apply Finset.nonempty_iff_ne_empty.mpr
  intro h
  exact live (Subtype.ext h)

omit [Fintype V] in
private theorem one {s : R.Mode} (live : s ≠ R.quiet) (v : V) :
    group s = some v ↔ WilsonOriginalOneColor.visible v s := by
  classical
  by_cases h : s.val.card = 1
  · let first := (Finset.card_eq_one.mp h).choose
    have same : s.val = {first} := (Finset.card_eq_one.mp h).choose_spec
    rw [group, dif_pos h, Option.some_inj, WilsonOriginalOneColor.visible]
    change first = v ↔ s.val ⊆ {v}
    constructor
    · rintro rfl
      exact same.le
    · intro contained
      have present : first ∈ s.val := same.symm ▸ Finset.mem_singleton_self first
      exact Finset.mem_singleton.mp (contained present)
  · rw [group, dif_neg h]
    constructor
    · simp
    · intro contained
      obtain ⟨i, hi⟩ := occupied live
      have iv : i = v := Finset.mem_singleton.mp (contained hi)
      have hv : v ∈ s.val := iv ▸ hi
      have same : s.val = {v} := le_antisymm contained (Finset.singleton_subset_iff.mpr hv)
      exact (h (by simp [same])).elim

omit [Fintype V] in
private theorem many {s : R.Mode} (live : s ≠ R.quiet) :
    group s = none ↔ 1 < s.val.card := by
  have pos := Finset.card_pos.mpr (occupied live)
  by_cases h : s.val.card = 1
  · simp [group,h]
  · simpa [group,h] using (show 1 < s.val.card by omega)

omit [DecidableEq V] in
private theorem total (f : V → ℝ) (b : ℝ) :
    (∑ k : Option V, k.elim b f) = b + ∑ v, f v := by
  classical
  rw [Fintype.sum_option]
  rfl

theorem regular (L : Lamps T ι G p o R) {w : V → ℝ} {B : ℕ} {a : ℝ}
    (fee : V → ℝ) (joint : ℝ)
    (single : ∀ v, (WilsonOriginalOneColor.lamps v L).Paid w B a (fee v))
    (cross : (portion L (mixed L)).Paid w B a joint) :
    L.Paid w B a (joint + ∑ v, fee v) := by
  rw [←total fee joint]
  apply WilsonThermometerFiniteModeIncome.regular L (fun i => group (L.mode i))
  intro label
  cases label with
  | none =>
    have seteq : {j | group (L.mode j) = none} = mixed L :=
      Set.ext fun i => many (L.live i)
    rw [seteq]
    exact cross
  | some v =>
    have seteq : {j | group (L.mode j) = some v} = WilsonOriginalOneColor.seats v L :=
      Set.ext fun i => one (L.live i) v
    rw [seteq]
    exact single v

omit [Fintype V] in
private theorem sameOffers {P : Passport n V} (X : ι → Row P R G T)
    {c d : ι → Prop} {w : V → ℝ} {σ f : ℝ} (same : ∀ i, c i ↔ d i)
    (under : Offers (fun i : Subtype d => X i.val) w σ f) :
    Offers (fun i : Subtype c => X i.val) w σ f := by
  have eqcd : c = d := funext (fun i => propext (same i))
  subst d
  exact under

theorem offers {P : Passport n V} (X : ι → Row P R G T) {w : V → ℝ} {σ : ℝ}
    (fee : V → ℝ) (joint : ℝ)
    (single : ∀ v, Offers (fun i : {j // WilsonOriginalOneColor.visible v (X j).mode} =>
      X i.val) w σ (fee v))
    (cross : Offers (fun i : {j // 1 < (X j).mode.val.card} => X i.val) w σ joint) :
    Offers X w σ (joint + ∑ v, fee v) := by
  rw [←total fee joint]
  apply WilsonThermometerFiniteModeIncome.offers X (fun i => group (X i).mode)
  intro label
  cases label with
  | none =>
    exact sameOffers X (fun i => many (X i).binder.live) cross
  | some v =>
    exact sameOffers X (fun i => one (X i).binder.live v) (single v)

omit [Fintype V] in
theorem credential {P : Passport n V} (X : ι → Row P R G T) {u w : V → ℝ} {σ a b : ℝ}
    {grades : V → ℕ} {order load shelf : ℕ} (old : Scene.Armada X u grades σ a order load shelf)
    (positive : ∀ i, 0 < w i) (funded : Offers X w σ b) :
    Scene.Armada X w grades σ b order load shelf :=
  {old with positive := positive, suggests := funded}

end YM.Integration.WilsonThermometerReunitedIncome

