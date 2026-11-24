import YM.Integration.ManuscriptQLocalForcedClusters

/-! The three original exceptional purchases form a joint allowance for distinct
integrated components. A component meeting several conditions occurs once in
the selected set. A globally exceptional connected term can itself be tagged. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ManuscriptQLocalExceptionalCounts
open Filter Function Finset Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson
open ConnectedActivityE6 Blaze Blaze.March Captain Push Push.AbsoluteSums
open PhysicalNext PhysicalNext.Repeat Height LocalLTE MergeProof Marker Extra.Multi
open scoped Classical BigOperators
variable {G:Gauge} {c f L:Side} {S:StepData c f} {T:Tube G S} {R:Rep G f}
  {P:Teller G} {Q:ConnectedActivityE6.Target G P} {W x μ a:ℝ} {o:Target.Order G W}
  (H:Cash W x μ L Q o a T R) {ι:Type} (M:ι→Lotus.Leaf R)

def Invoice (ℓ:ℕ) (z:H.fragrances) (q:ℕ) : Prop :=
  ∃ p s v:ℕ, q≤p+s+v ∧ ℓ*p≤Height.degreeN H ℓ z ∧ s≤Height.overlap H z ∧
    (v:ℝ)*Pressure.Stores.till x≤Height.depth H z

def localDegree (ℓ:ℕ) (z:H.fragrances) (b:Option (Fin z.1)) : ℕ :=
  Height.pinsN ℓ S (z.2 b).val+(z.2 b).val.card

def high (ℓ:ℕ) (z:Fan.Stars H M) : Finset (Option (Fin z.1.1)) :=
  Finset.univ.filter fun b=> ¬ManuscriptQLocalForcedClusters.seeded H M z b ∧ ℓ≤localDegree H ℓ z.1 b

def deep (ℓ:ℕ) (z:Fan.Stars H M) : Finset (Option (Fin z.1.1)) :=
  Finset.univ.filter fun b=> ¬ManuscriptQLocalForcedClusters.seeded H M z b ∧
    ¬ℓ≤localDegree H ℓ z.1 b ∧ Pressure.Stores.till x≤H.shapeW (z.1.2 b).val

def seeds (z:Fan.Stars H M) : Finset (Option (Fin z.1.1)) :=
  Finset.univ.filter (ManuscriptQLocalForcedClusters.seeded H M z)

def members (ℓ:ℕ) (z:Fan.Stars H M) := high H M ℓ z ∪ seeds H M z ∪ deep H M ℓ z

lemma disjoint_high (ℓ:ℕ) (z:Fan.Stars H M) : Disjoint (high H M ℓ z) (seeds H M z) :=
  Finset.disjoint_left.mpr fun _ hh hs=>(Finset.mem_filter.mp hh).2.1 (Finset.mem_filter.mp hs).2

lemma disjoint_deep (ℓ:ℕ) (z:Fan.Stars H M) : Disjoint (high H M ℓ z ∪ seeds H M z) (deep H M ℓ z) := by
  apply Finset.disjoint_left.mpr
  intro b hab hd
  rcases Finset.mem_union.mp hab with hh|hs
  · exact (Finset.mem_filter.mp hd).2.2.1 (Finset.mem_filter.mp hh).2.2
  · exact (Finset.mem_filter.mp hd).2.1 (Finset.mem_filter.mp hs).2

lemma local_total (ℓ:ℕ) (z:H.fragrances) : ∑b,localDegree H ℓ z b=Height.degreeN H ℓ z := by
  simp only [localDegree,Finset.sum_add_distrib,Height.degreeN,Height.acmeN,Height.breadth]

lemma tall_charge (ℓ:ℕ) (z:Fan.Stars H M) : ℓ*(high H M ℓ z).card≤Height.degreeN H ℓ z.1 := by
  let D:=high H M ℓ z
  calc ℓ*D.card=∑b∈D,ℓ:=by simp [Nat.mul_comm]
       _≤∑b∈D,localDegree H ℓ z.1 b:=Finset.sum_le_sum fun _ hb=>(Finset.mem_filter.mp hb).2.2
       _≤∑b,localDegree H ℓ z.1 b:=Finset.sum_le_sum_of_subset_of_nonneg
         (Finset.subset_univ _) fun _ _ _=>Nat.zero_le _
       _=Height.degreeN H ℓ z.1:=local_total H ℓ z.1

lemma deep_charge (ℓ:ℕ) (z:Fan.Stars H M) :
    ((deep H M ℓ z).card:ℝ)*Pressure.Stores.till x≤Height.depth H z.1 := by
  let D:=deep H M ℓ z
  calc (D.card:ℝ)*Pressure.Stores.till x=∑b∈D,(Pressure.Stores.till x:ℝ):=by simp
       _≤∑b∈D,H.shapeW (z.1.2 b).val:=Finset.sum_le_sum fun _ hb=>(Finset.mem_filter.mp hb).2.2.2
       _≤Height.depth H z.1:=Finset.sum_le_sum_of_subset_of_nonneg
         (Finset.subset_univ _) fun _ _ _=>H.positive_volume _

lemma restricted (ℓ:ℕ) (z:Fan.Stars H M) (χ:Push.SectorMeasure.Chi)
    (live:ManuscriptQLocalForcedClusters.alive H χ M z) :
    Invoice H ℓ z.1 (members H M ℓ z).card := by
  refine ⟨(high H M ℓ z).card,(seeds H M z).card,(deep H M ℓ z).card,?_,tall_charge H M ℓ z,
    ManuscriptQLocalForcedClusters.seeds_le_overlap H χ M z live,deep_charge H M ℓ z⟩
  rw [members,Finset.card_union_of_disjoint (disjoint_deep H M ℓ z),
    Finset.card_union_of_disjoint (disjoint_high H M ℓ z)]

lemma nonnegative_depth (z:H.fragrances) : 0≤Height.depth H z := sum_nonneg fun _ _=>H.positive_volume _

lemma seeds_only (ℓ:ℕ) (z:H.fragrances) {q:ℕ} (hq:q≤Height.overlap H z) : Invoice H ℓ z q :=
  ⟨0,q,0,by simp,by simp,hq,by simpa using (nonnegative_depth H z)⟩

lemma closed (ℓ:ℕ) (z:H.fragrances) (hz:Height.tiredN H ℓ z) : Invoice H ℓ z 1 := by
  rcases hz with num|seed|meter
  · exact ⟨1,0,0,by simp,by simpa using num,Nat.zero_le _,by simpa using (nonnegative_depth H z)⟩
  · exact seeds_only H ℓ z seed
  · exact ⟨0,0,1,by simp,by simp,Nat.zero_le _,by simpa using meter⟩

lemma member_iff (ℓ:ℕ) (z:Fan.Stars H M) (b:Option (Fin z.1.1)) :
    b∈members H M ℓ z ↔ ManuscriptQLocalForcedClusters.seeded H M z b ∨
      ℓ≤localDegree H ℓ z.1 b ∨ Pressure.Stores.till x≤H.shapeW (z.1.2 b).val := by
  by_cases hs:ManuscriptQLocalForcedClusters.seeded H M z b
  · simp [members,high,seeds,deep,hs]
  · by_cases hd:ℓ≤localDegree H ℓ z.1 b
    · simp [members,high,seeds,deep,hs,hd]
    · simp [members,high,seeds,deep,hs,hd,lt_of_not_ge hd]

lemma local_interior (ℓ:ℕ) (z:Fan.Stars H M) (χ:Push.SectorMeasure.Chi)
    (live:ManuscriptQLocalForcedClusters.alive H χ M z) {b:Option (Fin z.1.1)}
    (localLow:b∉members H M ℓ z) : Height.Elder ℓ (z.1.2 b) := by
  obtain ⟨U,ok⟩ := live
  have spark:=(Captain.silenced M (z.1.2 b) (z.2 b) (U b) (ok b)).1
  have missed:=mt (member_iff H M ℓ z b).mpr localLow
  have noSeed:=fun h=>missed (Or.inl h)
  have short:= lt_of_not_ge fun h=>missed (Or.inr (Or.inl h))
  have close:=lt_of_not_ge fun h=>missed (Or.inr (Or.inr h))
  refine ⟨spark,Finset.not_nonempty_iff_eq_empty.mp noSeed,
    Finset.not_nonempty_iff_eq_empty.mp (fun h=>noSeed (ManuscriptQLocalForcedClusters.owner_seed H χ M z ⟨U,ok⟩ h)),
    Finset.card_pos.mpr spark.1,(Nat.le_add_left _ _).trans short.le,?_⟩
  exact close.le.trans (by exact_mod_cast Nat.div_le_self ..)

/-- Every genuine live species in the componentwise complement is one of the
actual smooth input vertices used by the low Wick expansion. -/
lemma ordinary_species (ℓ:ℕ) (z:Fan.Stars H M) (χ:Push.SectorMeasure.Chi)
    (live:ManuscriptQLocalForcedClusters.alive H χ M z) {b:Option (Fin z.1.1)}
    (localLow:b∉members H M ℓ z) : ∀w∈(z.1.2 b).val,w∈Set.range (Fan.elastic (S:=S)) := by
  have hi := local_interior H M ℓ z χ live localLow
  have short:localDegree H ℓ z.1 b<ℓ:=lt_of_not_ge fun h=>localLow ((member_iff H M ℓ z b).mpr (Or.inr (Or.inl h)))
  let p:=z.1.2 b
  intro w hf
  rcases w with w|w
  · have hL:=Finset.mem_toLeft.mpr hf;rw [hi.unforced] at hL;exact (Finset.notMem_empty _ hL).elim
  have he' : Silica.hornN ℓ w<ℓ := lt_of_le_of_lt
    ((show Silica.hornN ℓ w≤Height.pinsN ℓ S p.val from Finset.single_le_sum (f:=Sum.elim _ _) (fun _ _=>Nat.zero_le _) hf).trans (Nat.le_add_right _ _)) short
  rcases w with w|w|w
  · have hv: w∈ Matter.own (z.1.2 b).val:= Finset.mem_toLeft.mpr (Finset.mem_toRight.mpr hf); rw [hi.noK] at hv; exact (Finset.notMem_empty _ hv).elim
  · rcases w with w|w|w
    · rcases w with w|w|w|w|w|w
      · exact ⟨.inl w,rfl⟩
      · exact ⟨.inr (.inl w),rfl⟩
      · exact ⟨.inr (.inr (.inl w)),rfl⟩
      · exact ⟨.inr (.inr (.inr (.inl w))),rfl⟩
      all_goals exfalso; change ℓ+2<ℓ at he'; omega
    · exact ⟨.inr (.inr (.inr (.inr w))),rfl⟩
    exfalso; change ℓ+2<ℓ at he'; omega
  exfalso; change ℓ+2<ℓ at he'; omega

end YM.Integration.ManuscriptQLocalExceptionalCounts
