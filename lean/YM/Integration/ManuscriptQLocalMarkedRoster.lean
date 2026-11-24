import YM.Integration.ManuscriptQLocalHealthyOffer
import YM.Integration.QLocalInheritedRegularSlots
import YM.Integration.LocalComparisonReadout

/-! The original FullBudget on every finite simultaneous selection of the
marked input. Only marker roots enter the tariff. The scopes of the source
and every unchanged forced address remain those of the submitted carrier. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ManuscriptQLocalMarkedRoster
open Function Finset MeasureTheory Lattice Wilson RG RG.Shoot Marker Overlay
open RG3.Held RG3.Forms RG3.Script.Picnic Push.AbsoluteSums LocalComparison Progress.DirectedRecipe
open PhysicalNext.Repeat Lotus MergeProof MergeProof.Menu
open ManuscriptQLocalMarkedLeaves ManuscriptQLocalMarkedOffers
open scoped Topology Classical BigOperators
variable {G : Gauge} {n : Side} {Y : Rep G n} {X V : Type} [Fintype V] [DecidableEq V]
  {Γ : Census V} {o : V → Site n} {T : Taste X o Y Γ} {w : V → ℝ} {κ a b : ℝ}
  (B : FullBudget Y.p T w κ a b)

omit [Fintype V] in
include B in
private theorem regular_pin (x : X) (i : ℕ) (v : V) (hv : v ∈ (T.menu.rays i).val) :
    o v∈T.menu.branch i := by
  have h:T.menu.origins v∈T.menu.branch i:=(B.active x).articles.pins i v hv
  simpa only [T.root] using h

private def address (x : X) (i : ℕ) : RegularAddress n :=
  let v := ((B.active x).articles.proper i).choose
  ⟨o v,T.menu.branch i,regular_pin B x i v ((B.active x).articles.proper i).choose_spec⟩

def ordinary (base x : X) (i : ℕ) : Slot (QLocalInheritedRegularSlots.carrier Y) :=
  let A := address B base i
  let k := blankRow n (A,i)
  let h := QLocalInheritedRegularSlots.reserved Y A i
  ManuscriptQLocalMarkedLeaves.regular (QLocalInheritedRegularSlots.budget Y T B)
    x i k (congrArg RegularAddress.support h.1) h.2

def hard (x : X) (ij : ℕ×ℕ) : Slot (QLocalInheritedRegularSlots.carrier Y) :=
  ManuscriptQLocalMarkedLeaves.forced (QLocalInheritedRegularSlots.budget Y T B) x ij.1 ij.2

omit [Fintype V] in
theorem ordinary_field (base x : X) (i : ℕ) (U : Config G n) :
    (ordinary B base x i).field U=masked Y.p.threshold (T.menu.branch i) (T.menu.regular x i) U := rfl

omit [Fintype V] in
theorem hard_field (x : X) (ij : ℕ×ℕ) (U : Config G n) :
    (hard B x ij).field U=T.menu.force x ij.1 ij.2 U := rfl

omit [Fintype V] in
theorem ordinary_support (base x : X) (i : ℕ) :
    (ordinary B base x i).turn.support (QLocalInheritedRegularSlots.carrier Y)=T.menu.branch i :=
  congrArg RegularAddress.support (QLocalInheritedRegularSlots.reserved Y (address B base i) i).1

omit [Fintype V] in
theorem distinct {base x : X} {i j : ℕ} (h : i≠j) :
    (ordinary B base x i).turn≠(ordinary B base x j).turn :=
  fun e=>QLocalInheritedRegularSlots.different h (Wing.logKey.inj e)

abbrev Occurrence (E : Finset ℕ) (K : Finset (ℕ×ℕ)) := (↥E) ⊕ (↥K)

def rows (base x : X) (E : Finset ℕ) (K : Finset (ℕ×ℕ)) :
    Occurrence E K → Slot (QLocalInheritedRegularSlots.carrier Y) :=
  Sum.elim (fun i=>ordinary B base x i.val) (fun ij=>hard B x ij.val)

def modes (E : Finset ℕ) (K : Finset (ℕ×ℕ)) : Occurrence E K → Γ.Mode :=
  Sum.elim (fun i=>T.menu.rays i.val) (fun ij=>T.menu.marks ij.val.1 ij.val.2)

/-- The live layout is chosen once, before all independently varying tests. -/
def live (K : Finset (ℕ×ℕ)) :=
  K.filter (fun ij => ∃ (x : X) (U : Config G n), T.menu.force x ij.1 ij.2 U≠0)

omit [Fintype V] in
theorem silent (K : Finset (ℕ×ℕ)) {ij : ℕ×ℕ} (h : ij∈K) (h₀ : ij∉live (T:=T) K)
    (x : X) (U : Config G n) : T.menu.force x ij.1 ij.2 U=0 :=
  Classical.byContradiction fun ne=>h₀ (Finset.mem_filter.mpr ⟨h,x,U,ne⟩)

private theorem totals (x : X) (E : Finset ℕ) (K : Finset (ℕ×ℕ)) :
    (∑ i∈E,Poly.toll w (T.menu.rays i)*Y.p.mass (T.menu.branch i) (B.white i)) +
      (∑ ij∈K,Poly.toll w (T.menu.marks ij.1 ij.2)*Y.p.mass (Y.activities.forced ij.1).support (B.black ij))
      ≤ Fintype.card V * a + Fintype.card V * (κ*b) := by
  choose A D hA hD hp using B.regularTotal
  have reg := rooted_sumBudget (fun i => mul_nonneg (Poly.worth B.radii _).le
    (mul_nonneg (Real.exp_pos _).le (B.white_nonnegative i))) (fun i=>(B.active x).articles.proper i) hA
  have gas := rooted_sumBudget (fun i : ℕ×ℕ => mul_nonneg (Poly.worth B.radii _).le
    (mul_nonneg (Real.exp_pos _).le (B.black_nonnegative i))) (fun i=>(B.active x).articles.occurs i.1 i.2) B.forcedTotal
  apply add_le_add
  · apply (budget_sum reg E).trans
    calc
      _ ≤ ∑ _v : V,a := by
        apply Finset.sum_le_sum
        intro v _
        have hd := (tsum_nonneg (hD v).1).trans (hD v).2.2
        have hu := mul_nonneg (B.radii v).le (B.unit_nonnegative v)
        linarith [hp v]
      _ = _ := by simp
  · simpa [BudgetPoint.mass] using budget_sum gas K

def promised (base x : X) (E : Finset ℕ) (K : Finset (ℕ×ℕ)) :
    Ticket (rows B base x E (live (T:=T) K)) (modes (T:=T) E (live (T:=T) K)) w :=
  ticket _ _ _ (fun i=>match i with
    | .inl i=>(B.active base).articles.proper i.val
    | .inr ij=>(B.active base).articles.occurs ij.val.1 ij.val.2)

/-- The same physical radius and rooted price hold before all finite
truncations and before every x. No ambient-volume charge is incurred. -/
theorem offer (base x : X) (E : Finset ℕ) (K : Finset (ℕ×ℕ)) :
    Menu.Offer o (promised B base x E K).terms w Y.p.B Y.p.supportExponent
      (2*(Fintype.card V*a+Fintype.card V*(κ*b))) := by
  apply (promised B base x E K).price o B.radii
  · intro idx z hz
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hz
    cases idx with
    | inl i =>
      change o v∈(ordinary B base x i.val).turn.support _
      rw [ordinary_support]
      exact regular_pin B base i.val v hv
    | inr ij =>
      obtain ⟨y,U,hy⟩ := (Finset.mem_filter.mp ij.property).2
      have hn : (T.leaf y).contents.entries ij.val.1 ij.val.2≠0 := fun eq=>hy (congrFun eq U)
      change o v∈(Y.activities.forced ij.val.1).support
      have h:T.menu.origins v∈(Y.activities.forced ij.val.1).support:=
        (B.active y).articles.retained ij.val.1 ij.val.2 hn v hv
      simpa only [T.root] using h
  · rw [Fintype.sum_sum_type]
    change (∑ i : E,Poly.toll w (T.menu.rays i.val)*Y.p.mass ((ordinary B base x i.val).turn.support _) (B.white i.val))+
      (∑ ij : live (T:=T) K,Poly.toll w (T.menu.marks ij.val.1 ij.val.2)*
        Y.p.mass (Y.activities.forced ij.val.1).support (B.black ij.val))≤_
    simp only [ordinary_support]
    rw [Finset.sum_coe_sort E (fun i=>Poly.toll w (T.menu.rays i)*Y.p.mass (T.menu.branch i) (B.white i)),
      Finset.sum_coe_sort (live (T:=T) K) (fun ij=>Poly.toll w (T.menu.marks ij.1 ij.2)*
        Y.p.mass (Y.activities.forced ij.1).support (B.black ij))]
    exact totals B base E (live (T:=T) K)

end YM.Integration.ManuscriptQLocalMarkedRoster
end
