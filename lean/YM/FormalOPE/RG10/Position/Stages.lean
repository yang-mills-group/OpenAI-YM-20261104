import YM.PertExtension.MaxwellReading

/-! # Coherent engineering-graded public dictionary

Used **only at the pre-frame and WilsonX stages**, not as a basis of an interacting Hilbert
space. Uses the actual compatible family of off-shell stencil-label frames and the accepted free
on-shell Gram result. Every basis element chosen at its *own* engineering weight is used up the
chain with exactly the same stencil representative, with higher labels proved only to supply
higher weights (positivity hypothesis not needed beyond the accepted free theory). Real bases
through each filtration. This is coordination with RG06: all free Maxwell quotient labels,
with exact write-back/cross to own-horizon support. Including all top diagrams from these stencils
does NOT supply proof of the identification of the entire limit quotient with the free one. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalOPE.RG10.Position
open Function Maxwell Labels Extraction Filter Finset Extra.FD MvPolynomial PertExtension
open scoped Topology BigOperators ContDiff Classical
variable {G : Gauge} (F : Frames G)
local notation "W" d => Table.Field (freeTable F) d
local notation "R" d=> recorded F d
variable (d : ℕ) {h k : ℕ}

theorem rising_on (hu:h ≤ k) : shellSector G h ≤ shellSector G k := by
  rintro v ⟨p,rfl⟩; exact ⟨raiseLabel G hu p,rfl⟩

def higher (hu:h ≤ k) : (W h) →ₗ[ℂ] W k :=
    ((exactField F k).symm.toLinearMap).comp ((Submodule.inclusion (rising_on (G:=G) hu)).comp (exactField F h).toLinearMap)

lemma writes_higher (hu:h ≤ k) (x : W h) : writes F k (higher F hu x)=writes F h x := by
  unfold writes higher; simp
lemma form (p : Label G d) : writes F d (sourceAt F d p)=observable G d p := by
  unfold sourceAt; rw [LinearMap.comp_apply, writes_project];
  change observable G d ((F.level d).coords.symm ((F.level d).coords p))= _; rw [LinearEquiv.symm_apply_apply]

abbrev weight := Horizon.weight d F
abbrev Index := PositionPrescription.Index F d
lemma recorded_at (i : Index F d) : IsWeightedHomogeneous costKey (writes F d ((R d).b i)) (weight F d i) := by
  rw [(R d).corners i |>.choose_spec];
  have hh:=at_alcove F d ((R d).corners i).choose
  intro p hp
  exact congr_arg Prod.fst ((weight_collapse p).symm.trans (hh hp))

abbrev Spur := {i : Index F d // weight F d i=d}
abbrev Deck := Σ a : Fin (d+1), Spur F a.val
abbrev Token := Σ d:ℕ, Spur F d

namespace Deck
def token (z : Deck F d) : Token F := ⟨z.1.val,z.2⟩
abbrev price (z : Deck F d) := z.1.val
def climb (hu:h ≤ k) (z : Deck F h) : Deck F k := ⟨⟨z.1.val,Nat.lt_of_lt_of_le z.1.isLt (by omega)⟩,z.2⟩
lemma token_climb (hu:h ≤ k) (z : Deck F h) : token F k (climb F hu z)=token F h z:=rfl
lemma price_climb (hu:h ≤ k) (z : Deck F h) : price F k (climb F hu z)=price F h z:=rfl
lemma token_inj : Injective (token F d):=by
  rintro ⟨⟨i,hi⟩,v⟩ ⟨⟨j,hj⟩,w⟩ he
  obtain ⟨ha,hb⟩ := Sigma.mk.inj he; simp only at ha; subst j; congr; exact eq_of_heq hb
lemma climb_inj (hu:h ≤ k) : Injective (climb F hu):=fun _ _ he=> token_inj F h (congr_arg (token F k) he)
lemma price_bound (z : Deck F d) : price F d z ≤ d:= Nat.le_of_lt_succ z.1.isLt
lemma of_price (hu:h ≤ k) {j:Deck F k} (hz:price F k j ≤ h) : ∃ v,climb F hu v=j := ⟨⟨⟨price F k j,Nat.lt_succ_of_le hz⟩,j.2⟩,by cases j; rfl⟩
end Deck

def covers (i : Deck F d) : W d:= higher F (Deck.price_bound F d i) ((R i.1.val).b i.2.val)

lemma written (i : Deck F d): writes F d (covers F d i)=writes F (Deck.price F d i) ((R i.1.val).b i.2.val):=writes_higher ..
lemma leaf_cost (i : Deck F d) : AtWeight F (covers F d i) (Deck.price F d i):=by
  show IsWeightedHomogeneous ..; rw [written]
  simpa [i.2.property,Deck.price] using recorded_at F _ i.2.val

lemma at_own_weight (p : W d) (hp : IsWeightedHomogeneous costKey (writes F d p) d) :
    ∑ i:Spur F d, (R d).b.repr p i.val • (R d).b i.val=p := by
  let u : Finset (Index F d) := univ.filter (fun i=> weight F d i=d)
  rw [← sum_subtype u (fun _=> by simp [u]) (fun i=> (R d).b.repr p i • (R d).b i)];
  apply writes_inj F d; unfold u
  rw [_root_.map_sum, Finset.sum_filter]
  have hh := congr_arg ((weightedHomogeneousComponent costKey d) ∘ (writes F d)) ((R d).b.sum_repr p)
  simp only [comp_apply,_root_.map_sum,hp.weightedHomogeneousComponent_same, map_smul] at hh
  rw [← hh]; apply sum_congr rfl; intro i hi
  rw [map_smul]; by_cases h:weight F d i=d
  · rw [(show IsWeightedHomogeneous _ _ d from by have hh:=recorded_at F d i; rw [h] at hh; exact hh).weightedHomogeneousComponent_same,if_pos h]
  rw [(recorded_at F d i).weightedHomogeneousComponent_ne _ (Ne.symm h),smul_zero, if_neg h]

lemma span_covers : ⊤ ≤ Submodule.span ℂ (Set.range (covers F d)) := by
  let b := (R d).b;
  intro z _; rw [← b.sum_repr z]; apply Submodule.sum_mem
  intro j hj; apply Submodule.smul_mem; -- decompose in basis of weight j
  let x:= weight F d j
  let hx : x ≤ d:= (F.level d).bound (Horizon.reference d F j)
  let y : W x := sourceAt F x ((F.level x).basis (Horizon.sourceAxis d F j))
  have he : writes F d (b j)=writes F x y:=by rw [form]; exact MaxwellReading.pureMatch ..
  have hp : IsWeightedHomogeneous costKey (writes F x y) x:= he ▸ recorded_at F d j
  have H : b j=higher F hx y:=writes_inj F d (he.trans (writes_higher _ hx _).symm)
  rw [H,← at_own_weight F x y hp, _root_.map_sum];
  apply Submodule.sum_mem; intro i hi; rw [map_smul]; apply Submodule.smul_mem;
  exact Submodule.subset_span ⟨⟨⟨x,Nat.lt_succ_of_le hx⟩,i⟩,rfl⟩

lemma independence : LinearIndependent ℂ (covers F d) := by
  apply Fintype.linearIndependent_iff.mpr
  intro g he i; rcases i with ⟨a,v⟩
  let h:=a.val; apply Fintype.linearIndependent_iff.mp ((R h).b.linearIndependent.comp (Subtype.val:Spur F h → Index F h) Subtype.val_injective) (fun v=>g ⟨a,v⟩) _ v
  apply writes_inj F h; simp only [_root_.map_sum,map_zero,map_smul]
  have hh := congr_arg ((weightedHomogeneousComponent costKey h) ∘ (writes F d)) he
  rw [Fintype.sum_sigma] at hh; simp only [comp_apply,_root_.map_sum,map_smul,map_zero] at hh
  rw [Finset.sum_eq_single a] at hh;
  · rw [← hh]; apply sum_congr rfl; intro v' _;
    have hr : IsWeightedHomogeneous costKey (writes F d (covers F d ⟨a,v'⟩)) h:=leaf_cost F d ⟨a,v'⟩
    rw [hr.weightedHomogeneousComponent_same,written]; rfl
  · intro b _ hb; apply sum_eq_zero; intro w _;
    have hr : IsWeightedHomogeneous costKey (writes F d (covers F d ⟨b,w⟩)) b.val:=leaf_cost F d ⟨b,w⟩;
    rw [hr.weightedHomogeneousComponent_ne _ (Ne.symm (Fin.val_injective.ne hb)), smul_zero]
  simp

def deck := Module.Basis.mk (independence F d) (span_covers F d)
@[simp] lemma deckAt (i:Deck F d) : deck F d i=covers F d i := by simp [deck]
lemma cabin (hu:h ≤ k) (i:Deck F h) : higher F hu (deck F h i)=deck F k (Deck.climb F hu i) := by
  apply writes_inj F k; rw [writes_higher,deckAt,deckAt,written,written]; rfl
lemma deck_real (i:Deck F d) : (freeTable F).conj (table_spin F) d (deck F d i)= deck F d i := by
  apply writes_inj F d; rw [deckAt,writes_bar,written,← writes_bar (h:= table_spin F),(R i.1.val).real_i]

end YM.FormalOPE.RG10.Position
