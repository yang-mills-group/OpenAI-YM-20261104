import YM.QuadraticLocal.Earn.Rendering
/-! # Marker clusters to enroll in a publication

One FULL finite disjoint combination. Keep old indices (not just union of modes &
positions). Critical for operator price and absolute convergence after projection.
Includes any staggering of multiple markers on same site. Restrictions of Census additional
to square-zero on repeats are kept. Global inputs do not appear in these clusters.
Elementary computations receive REAL markers: use separate passports to each aperture with
separate paints, loan toll still charged at the full complex mark. -/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Earn
open Function Filter Finset Lattice RG Wilson Marker Ac
open Push Push.AbsoluteSums Paths Animals
open QuadraticLocal.Sunrise
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {V α ι : Type}[DecidableEq V]{G:Gauge}{n c:Side}
variable {P:Passport n V} {R:Census V} {g a e σ r b :ℝ} {k u' i' : ℕ}
variable (X:ι→Row P R G α)
set_option quotPrecheck false
local notation "σ"=> (fun i:ι=> (X i).mode)
-- syntactic note no binder after
local notation "σ'"=> (fun i:ι=> (X i).mode.val)

abbrev Club:= { s:Finset ι // s.Nonempty ∧ (s:Set ι).Pairwise (fun i j=> Disjoint (σ' i) (σ' j)) ∧ (∃ m:R.Mode,m.val=s.biUnion σ') ∧ ∀ i∈s,¬(X i).clear }
variable (C:Club X)
namespace Club
-- rely on actual `Finset.biUnion` using [DecidableEq V]. Open scope Classical locally on ι. capture notation to avoid projection issues.

abbrev members := C.val
abbrev words (C:Club X): Finset V:= C.val.biUnion (fun i=> (X i).mode.val)
def alliance : R.Mode:= C.prop.2.2.1.choose
local notation "V₁"=> (C.prop.2.2)
theorem fulfills : (alliance X C).val=words X C:= (V₁.1.choose_spec)
lemma earn i (h:i∈C.val) : (X i).mode.val⊆ (alliance X C).val:= fulfills X C ▸ Finset.subset_biUnion_of_mem (fun i=> (X i).mode.val) h
lemma apart : Set.Pairwise C.val (fun i j=> Disjoint (σ' i) (σ' j)):= C.prop.2.1
lemma all_masked : ∀ i∈C.val,¬(X i).clear:= C.prop.2.2.2
abbrev Keys := Fin (Finset.card C.val)
def ticket : Club.Keys X C ≃ ↥C.val := ((Finset.equivFin C.val).symm)
abbrev stamp (i:Club.Keys X C) : ι:= ((Club.ticket X C) i).val
set_option quotPrecheck false
local notation "K"=> (Club.Keys X C)
abbrev lowest : Club.Keys X C:= ⟨0,Finset.card_pos.mpr C.prop.1⟩
local notation "e₀"=> Club.lowest X C
local notation "i₀"=> Club.stamp X C
abbrev troops (i:Club.Keys X C) : Row P R G α:= X (i₀ i)
local notation "T"=> Club.troops X C
local notation "η"=> alliance X C
lemma troop_inj : Injective (Club.stamp X C):= fun i j h=> (Club.ticket X C).injective (Subtype.ext h)
lemma attends (i:Club.Keys X C) : Club.stamp X C i∈ C.val:= ((Club.ticket X C) i).prop
lemma attends_rev (i:ι)(hi:i∈C.val):∃ j:Club.Keys X C, Club.stamp X C j=i:=by
   obtain ⟨j,r⟩:= (Club.ticket X C).surjective (⟨i,hi⟩:↥C.val); exact ⟨j,congr_arg Subtype.val r⟩
lemma cites : (η).val=Finset.univ.biUnion (fun i:Club.Keys X C => (T i).mode.val):= by
   rw [fulfills]; ext1 j; simp_rw [Finset.mem_biUnion]; -- may need words
   constructor
   · intro hj; obtain ⟨i,hi,hx⟩:= hj
     obtain ⟨i,rfl⟩:= attends_rev X C i hi; exact ⟨i,mem_univ _,hx⟩
   rintro ⟨j,h,hx⟩; exact ⟨_,Club.attends X C j,hx⟩
lemma unique_rank (v:V)(hv:v∈ (η).val) : ∃! i:Club.Keys X C,v∈ (T i).mode.val := by
    rw [Club.cites X C] at hv; obtain ⟨i,_,h⟩:= Finset.mem_biUnion.mp hv; refine ⟨i,h,?_⟩; intro j h'; apply (Club.troop_inj X C); by_contra hn; exact Finset.disjoint_left.mp ((Club.apart X C) (Club.attends X C j) (Club.attends X C i) hn) h' h
abbrev joint (C:Club X)(v:V):Club.Keys X C:= if h:v∈(Club.alliance X C).val then Classical.choose ((Club.unique_rank X C v h).exists) else Club.lowest X C
theorem join_rank {v:V}(hv:v∈ (η).val) : v∈ (T (Club.joint X C v)).mode.val := by unfold Club.joint; rw [dif_pos hv]; exact Classical.choose_spec (unique_rank X C _ hv).exists
-- Cost statements helper. Not per BOOL here.
lemma union_price (w:V→ℝ) : Poly.toll w η = ∏ i∈C.val,Poly.toll w (X i).mode:=by unfold Poly.toll; rw [fulfills,Club.words]; exact Finset.prod_biUnion (C.prop.2.1)
lemma toll (w:V→ℕ): (∑ i∈ (Club.alliance X C).val,w i)=∑ i∈C.val,∑ t∈ (X i).mode.val,w t:=by rw [fulfills,Club.words]; exact Finset.sum_biUnion (C.prop.2.1)
lemma summed (W:ι→ℕ) : (∑ i:Club.Keys X C, W (stamp X C i))=∑ i∈C.val,W i:= by rw [← Finset.sum_attach C.val W]; exact Equiv.sum_comp (ticket X C) (fun i=> W i.val)
lemma sumℝ (W:ι→ℝ) : (∑ i:Club.Keys X C,W (stamp X C i))=∑ i∈C.val,W i:= by rw [← Finset.sum_attach C.val W]; exact Equiv.sum_comp (ticket X C) (fun i=> W i.val)
lemma product {F:Type*}[CommMonoid F](W:ι→F) : (∏ i:Club.Keys X C,W (stamp X C i))=∏ i∈C.val,W i:= by rw [← Finset.prod_attach C.val W]; exact Equiv.prod_comp (ticket X C) (fun i=> W i.val)
lemma cardLe : C.val.card≤ (η).val.card:=by
    let v:=fun i:ι=>(X i).binder.front; have hv i:v i∈ (X i).mode.val:= (X i).binder.east; have hp: Set.MapsTo v C.val (η).val:= fun i hi=> Club.earn X C _ hi (hv i); have hh:Set.InjOn v C.val:= by
       intro i hi j hj hz; by_contra h'; exact Finset.disjoint_left.mp (Club.apart X C hi hj h') (hv i) ((hz ▸ hv j): _ )
    exact Finset.card_le_card_of_injOn v hp hh
lemma sum_value (w:V→ℕ)(k:ℕ)(hk: ∀ i:ι, (X i).Credentials k w) : (∑ i:Club.Keys X C,(T i).lamp.toll) = ∑ j∈ (η).val,w j := by rw [Club.toll]; exact (Club.summed X C (fun q=>(X q).lamp.toll)).trans (Finset.sum_congr rfl fun i hi=>(hk i).2)
lemma quota (w:V→ℕ)(k:ℕ)(hk: ∀ i:ι, (X i).Credentials k w) : C.val.card ≤ ∑ j∈ (η).val,w j:= by
 rw [Club.toll]; calc
 C.val.card = ∑ _i∈ C.val,(1:ℕ) := by simp
 _ ≤ _:= Finset.sum_le_sum fun i _=> ((hk i).2 ▸ (X i).lamp.higher)

-- Height spreads for engagement/disengagement. Use center ≥ etc.
variable (q:Ratio c n)
abbrev mask (i:ι): Site c:= q.parent (X i).center
abbrev site (q:Ratio c n)(i:Club.Keys X C): Site c:= mask X q (i₀ i)
abbrev roof := site X C q (Club.lowest X C)
local notation "L"=> q.count.val
def reach :ℕ:= C.val.sup (fun i=> separation (roof X C q) (mask X q i))
abbrev length := ∑ i∈ C.val,(X i).length
local notation "Ω" i:max=> (X i)
lemma brings (i:ι)(h:i∈C.val):separation (roof X C q) (mask X q i)≤ Club.reach X C q:= le_sup (f:=fun i=> separation _ _) h -- check
lemma extent_le (hb:∀ i∈C.val,separation (roof X C q) (mask X q i)≤ k): reach X C q≤ k:= Finset.sup_le hb
lemma en_route (i:ι)(h:i∈ C.val): (X i).length ≤ Club.length X C:= Finset.single_le_sum (f:=fun i=> (X i).length) (fun i _=> Nat.zero_le _) h

end Club
end YM.QuadraticLocal.Earn
