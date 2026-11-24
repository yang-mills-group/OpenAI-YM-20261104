import YM.Integration.ActualWilsonPacketSplit
import YM.Integration.ActualWilsonInventorySlot

/-! Genuine signed Taylor rows at the original localized Wilson keeper slots. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualWilsonTaylorSlot
open Function Set Finset MeasureTheory Lattice RG Wilson Source Labels Extra.Histories
open ActualWilsonPacketSplit RG16.Guarding RG04B.Mark Planned.GuardedAtom ProjectorNext.Equivariance
open scoped BigOperators Classical
variable {G : Gauge} {n : Side} {W : Rep G n} {Y : ℕ → Support n}

abbrev Key (W : Rep G n) (Y : ℕ → Support n) :=
  {z : ℕ × Finset ℕ // z.2.Nonempty ∧ ∀ j ∈ z.2, ¬Disjoint (scopes W j) (Y z.1)}

def stock (z : Key W Y) : StockTag n :=
  ⟨(joined W (Y z.1.1) z.1.2,z.1.2.biUnion (inventory W)),by
    obtain ⟨i,hi⟩ := z.2.1
    obtain ⟨x,hx⟩ := (W.activities.forced i).inventory_ne
    exact ⟨x,Finset.mem_biUnion.2 ⟨i,hi,hx⟩⟩,by
    intro x hx
    obtain ⟨i,hi,hx⟩ := Finset.mem_biUnion.1 hx
    exact Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨i,hi,(W.activities.forced i).inventory_sup hx⟩)⟩

def address (K : Guard.Keeper W.p W.activities) : Key W Y ↪ ℕ where
  toFun z := K.code (stock z,Encodable.encode z.1)
  inj' _ _ h := Subtype.ext (Encodable.encode_injective (congrArg Prod.snd (K.code.injective h)))

theorem geometry (K : Guard.Keeper W.p W.activities) (z : Key W Y) :
    scopes W (address K z) = joined W (Y z.1.1) z.1.2 ∧
    inventory W (address K z) = z.1.2.biUnion (inventory W) :=
  ⟨K.support (stock z,Encodable.encode z.1),K.inventory (stock z,Encodable.encode z.1)⟩

def gate (z : Key W Y) (U : Config G n) : Prop :=
  (z.1.2 : Set ℕ).Pairwise (fun i j => Disjoint (scopes W i) (scopes W j)) ∧
    (stock z).1.1 ∩ flags W.p.threshold U = (stock z).1.2

def deposit (f : ℕ → Config G n → ℂ) (z : Key W Y) (U : Config G n) : ℂ :=
  if gate z U then f z.1.1 U * ∏ i ∈ z.1.2, (W.activities.K i U : ℂ) else 0

def rows (K : Guard.Keeper W.p W.activities) (f : ℕ → Config G n → ℂ) :=
  extend (address (Y := Y) K) (deposit f) 0

theorem on_slot (K : Guard.Keeper W.p W.activities) (f : ℕ → Config G n → ℂ) (z : Key W Y) :
    rows (Y := Y) K f (address K z) = deposit f z := (address (Y := Y) K).injective.extend_apply .. 

theorem off_slot (K : Guard.Keeper W.p W.activities) (f : ℕ → Config G n → ℂ) {i : ℕ}
    (hi : i ∉ range (address (Y := Y) K)) : rows (Y := Y) K f i = 0 := extend_apply' _ _ _ hi

theorem must_pass (K : Guard.Keeper W.p W.activities) (f : ℕ → Config G n → ℂ)
    (z : Key W Y) (U : Config G n) (h : deposit f z U ≠ 0) :
    (W.activities.forced (address K z)).eligible W.p.threshold U := by
  have hg : gate z U := by by_contra hn; simp [deposit,hn] at h
  have hp : scopes W (address K z) ∩ flags W.p.threshold U = inventory W (address K z) := by
    rw [(geometry K z).1,(geometry K z).2]
    exact hg.2
  exact ⟨hp,K.pass (stock z,Encodable.encode z.1) U hp⟩

theorem origin (f : ℕ → Config G n → ℂ) (o : Site n) (hf : ∀ j U, f j U≠0 → o∈Y j)
    (z : Key W Y) (h : deposit f z ≠ 0) : o ∈ joined W (Y z.1.1) z.1.2 := by
  by_contra hn
  apply h
  funext U
  have hz : f z.1.1 U = 0 := by
    by_contra hc
    exact hn (Finset.mem_union_left _ (hf _ U hc))
  simp [deposit,hz]

theorem gauge (f : ℕ → Config G n → ℂ) (hf : ∀ j, GaugeInvariant (f j))
    (hW : W.activities.ForcedFamily W.p) (z : Key W Y) : GaugeInvariant (deposit f z) := by
  intro t U
  simp only [deposit,gate,gauge_flags,hf z.1.1 t U,fun i => hW.sym i t U]
  split_ifs <;> rfl

theorem guard_measurable (Z S : Support n) (t : ℝ) :
    MeasurableSet {U : Config G n | S ∩ flags t U = Z} := by
  have he : {U : Config G n | S ∩ flags t U = Z} =
      ⋃ I : {I : Support n // S ∩ I=Z}, {U : Config G n | flags t U=I.1} := by
    ext U
    simp only [Set.mem_setOf_eq,Set.mem_iUnion]
    constructor
    · intro h
      exact ⟨⟨flags t U,h⟩,rfl⟩
    rintro ⟨I,hI⟩
    rw [hI]
    exact I.2
  rw [he]
  exact MeasurableSet.iUnion (fun I => flags_measurable_eq t I.1)

theorem borel (f : ℕ → Config G n → ℂ) (hf : ∀ j, Measurable (f j))
    (hW : W.activities.ForcedFamily W.p) (z : Key W Y) : Measurable (deposit f z) := by
  by_cases h : (z.1.2 : Set ℕ).Pairwise (fun i j => Disjoint (scopes W i) (scopes W j))
  · have hp : Measurable (fun U => ∏ i ∈ z.1.2, (W.activities.K i U : ℂ)) :=
      Finset.measurable_prod _ fun i _ => Complex.continuous_ofReal.measurable.comp (hW.meas i)
    change Measurable (fun U => if gate z U then _ else _)
    have hg : MeasurableSet {U | gate z U} := by
      simpa only [gate,h,true_and] using (guard_measurable (G := G) (stock z).1.2 (stock z).1.1 W.p.threshold)
    exact ((hf z.1.1).mul hp).ite hg measurable_const
  change Measurable (fun U => if gate z U then _ else _)
  simp only [gate,h,false_and,if_false]
  exact measurable_const

theorem restrict_flags {S T : Support n} (h : S ⊆ T) {a b : Support n} (he : T ∩ a=T ∩ b) :
    S ∩ a = S ∩ b := by
  ext x
  constructor
  · intro hx
    have hz : x ∈ T ∩ a := mem_inter.2 ⟨h (mem_inter.1 hx).1,(mem_inter.1 hx).2⟩
    rw [he] at hz
    exact mem_inter.2 ⟨(mem_inter.1 hx).1,(mem_inter.1 hz).2⟩
  intro hx
  have hz : x ∈ T ∩ b := mem_inter.2 ⟨h (mem_inter.1 hx).1,(mem_inter.1 hx).2⟩
  rw [←he] at hz
  exact mem_inter.2 ⟨(mem_inter.1 hx).1,(mem_inter.1 hz).2⟩

theorem reads (f : ℕ → Config G n → ℂ) (hf : ∀ j, UsesFinal W.p.threshold (Y j) (f j))
    (hW : W.activities.ForcedFamily W.p) (z : Key W Y) :
    UsesFinal W.p.threshold (joined W (Y z.1.1) z.1.2) (deposit f z) := by
  intro U V ha he
  have hs : Y z.1.1 ⊆ joined W (Y z.1.1) z.1.2 := Finset.subset_union_left
  have hr j (hj : j ∈ z.1.2) : scopes W j ⊆ joined W (Y z.1.1) z.1.2 := fun _ hx =>
    mem_union_right _ (mem_biUnion.2 ⟨j,hj,hx⟩)
  have hU := hf z.1.1 U V (agrees_mono ha hs) (restrict_flags hs he)
  have hprod : (∏ i ∈ z.1.2, (W.activities.K i U : ℂ)) = ∏ i ∈ z.1.2, (W.activities.K i V : ℂ) :=
    Finset.prod_congr rfl fun i hi => congrArg Complex.ofReal
      (hW.reads i U V (agrees_mono ha (hr i hi)) (restrict_flags (hr i hi) he))
  have hflag : (stock z).1.1 ∩ flags W.p.threshold U=(stock z).1.1 ∩ flags W.p.threshold V := he
  simp only [deposit,gate,hflag,hU,hprod]
  split_ifs <;> rfl

def book {d : ℕ} (E : Frame G d) (o : Site n) (K : Guard.Keeper W.p W.activities)
    (f : ℕ → Config G n → ℂ) : Coefficient E n :=
  { primary o (0 : E.Coeff) with forced := rows (Y := Y) K f }

theorem format {d : ℕ} (E : Frame G d) (o : Site n) (A : Hol G) (K : Guard.Keeper W.p W.activities)
    (f : ℕ → Config G n → ℂ) (hg : ∀ j, GaugeInvariant (f j)) (hm : ∀ j, Measurable (f j))
    (hl : ∀ j, UsesFinal W.p.threshold (Y j) (f j)) (ho : ∀ j U, f j U≠0 → o∈Y j)
    (hW : W.activities.ForcedFamily W.p) : (book (Y := Y) E o K f).Format o A W := by
  have hb : (primary o (0 : E.Coeff)).Format o A W := primary_format _
  refine ⟨hb.smooth,hb.origin,hb.identity_null,hb.projects,?_,?_,?_,?_,?_⟩
  · intro i U hn
    by_cases hi : i∈range (address (Y := Y) K)
    · obtain ⟨z,rfl⟩ := hi
      exact must_pass K f z U (by simpa only [book,on_slot] using hn)
    exact False.elim (hn (congrFun (off_slot K f hi) U))
  · intro i hn
    by_cases hi : i∈range (address (Y := Y) K)
    · obtain ⟨z,rfl⟩ := hi
      change o ∈ scopes W (address K z)
      rw [(geometry K z).1]
      exact origin f o ho z (by simpa only [book,on_slot] using hn)
    exact False.elim (hn (off_slot K f hi))
  · intro i
    change GaugeInvariant (rows (Y := Y) K f i)
    by_cases hi : i∈range (address (Y := Y) K)
    · obtain ⟨z,rfl⟩ := hi
      rw [on_slot]
      exact gauge f hg hW z
    rw [off_slot K f hi]
    exact fun _ _ => rfl
  · intro i
    change UsesFinal _ _ (rows (Y := Y) K f i)
    by_cases hi : i∈range (address (Y := Y) K)
    · obtain ⟨z,rfl⟩ := hi
      change UsesFinal _ (scopes W (address K z)) _
      rw [(geometry K z).1,on_slot]
      exact reads f hl hW z
    rw [off_slot K f hi]
    exact fun _ _ _ _ => rfl
  · intro i
    change Measurable (rows (Y := Y) K f i)
    by_cases hi : i∈range (address (Y := Y) K)
    · obtain ⟨z,rfl⟩ := hi
      rw [on_slot]
      exact borel f hm hW z
    rw [off_slot K f hi]
    exact measurable_const

end YM.Integration.ActualWilsonTaylorSlot
