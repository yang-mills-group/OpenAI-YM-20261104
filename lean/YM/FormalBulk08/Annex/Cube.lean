import YM.FormalBulk08.Annex.Face
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Annex
open Function Filter Lattice Dawn Set
open scoped BigOperators Topology ENNReal Classical ContDiff
variable {D k:ℕ}
abbrev Siteface := Axis × Bool
abbrev tent (i:Siteface):= nearM i.1 i.2
def lobby : Set E4:= {x|∀ i:Axis,|x i|≤8}
def cloud (T : Finset Siteface): Set E4:= lobby ∩ ⋂ u∈ T,tent u
def beam : Set E4:= cloud Finset.univ
lemma cloud_has {y:E4}{T:Finset Siteface} : y∈cloud T ↔ y∈lobby ∧ ∀ i∈T,y∈tent i:=by unfold cloud; rw [mem_inter_iff]; simp
lemma cube_test {x:E4} : x∈beam ↔ ∀ i, |x i| ≤ 1/2:= by
   rw [beam,cloud_has];constructor
   · intro ⟨_,p⟩ i; have hz : ε false*x i≤ε false*border false:=p (i,false) (Finset.mem_univ _); have hX: ε true*x i≤ ε true*border true:= p (i,true) (Finset.mem_univ _); rw [abs_le]
     simp [ε,border] at hz hX; constructor<;>linarith
   intro h; refine ⟨fun i=>(h i).trans (by norm_num),?_⟩; rintro ⟨i,b⟩ _; obtain ⟨he,hp⟩:=abs_le.mp (h i); change ε b*x i≤ ε b*border b; cases b<;> simp [ε,border]<;>linarith
lemma cloud_enlarge {x:E4}{u:Finset Siteface} (h:x∈beam):x∈cloud u := cloud_has.mpr ⟨h.1,fun _ _=> (cloud_has.mp h).2 _ (Finset.mem_univ _)⟩
lemma jog {T:Finset Siteface} (i:Siteface)(x:E4)(h:x∈cloud T)(p:x∈farM i.1 i.2) (j:Fin (D+1)): jostle i.1 i.2 (taps D j) x∈ cloud (insert i T):= by
    obtain ⟨a,b⟩:=i; let y:=jostle a b (taps D j) x; change x∈farM a b at p
    have ht : |y a|≤1/2:= by
       unfold y; rw [jostle_one,abs_le]; obtain ⟨hs,hx⟩:= gentle j; obtain ⟨hH,hK⟩:=abs_le.mp (h.1 a); change ε b*border b≤ ε b*x a at p; cases b <;> simp only [ε,border,↓reduceIte,Bool.false_eq_true] at p ⊢ <;> constructor<;>nlinarith
    refine cloud_has.mpr ⟨fun u=>?_,fun z hz=>?_⟩
    · by_cases hx:u=a; rw [hx]; exact ht.trans (by norm_num)
      change |y u|≤8; rw [show y u=x u from jostle_else a b _ _ hx]; exact h.1 u
    obtain ⟨z,v⟩:=z; by_cases hp:z=a
    · subst z; change ε v*y a≤ ε v*border v; obtain ⟨h,h'⟩:= abs_le.mp ht;cases v <;> simp [ε,border] <;>linarith
    have h': (z,v) ∈ T:= Finset.mem_of_mem_insert_of_ne hz (by simp [hp]); change ε v*y z ≤_; rw [show y z=x z from jostle_else a b _ _ hp]; exact (cloud_has.mp h).2 _ h'
-- application
lemma round_money (i:Siteface)(T:Finset Siteface){f:Garden D}(A:ℝ)(he:∀ x∈cloud (insert i T),∀ u:Brush D, |Dawn.halo f u x| ≤ A)(x:E4)(hx:x∈ cloud T)(u:Brush D)(h:x∈farM i.1 i.2) :
    |Dawn.halo (rounds i.1 i.2 f) u x| ≤ (∑ j,|treks D j|)* A := by
   rw [map_basis,Finset.sum_mul]; refine (Finset.abs_sum_le_sum_abs ..).trans ?_; apply Finset.sum_le_sum; intro j _
   rw [abs_mul,folded,abs_mul,abs_pow]; refine mul_le_mul_of_nonneg_left (le_trans ?_ (he _ (jog i x hx h j) u)) (abs_nonneg _); obtain ⟨hp,hH⟩:= gentle j; exact mul_le_of_le_one_left (abs_nonneg _) (pow_le_one₀ (abs_nonneg _) (abs_le.mpr ⟨by linarith,by linarith⟩))
structure Memos (f g:Garden D)(T:Finset Siteface)(C:ℝ): Prop where
    pays : ∀ x∈ cloud T,∀ u:Brush D,|Dawn.halo g u x| ≤ C
    meets: ∀ x∈beam,∀ u:Brush D,Dawn.halo g u x=Dawn.halo f u x
lemma memo_move (i:Siteface)(T:Finset Siteface)(f g:Garden D)(A:ℝ)(hA:0≤A)(h:Memos f g (insert i T) A): Memos f (notchM i.1 i.2 g) T ((1+∑ i,|treks D i|)*A):= by
    constructor
    · intro x hx u; by_cases hh:x∈tent i
      · rw [quiet i.1 i.2 _ _ _ hh]; apply (h.pays x (cloud_has.mpr ?_) u).trans (le_mul_of_one_le_left hA (by exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _=>abs_nonneg _)))
        exact ⟨hx.1, fun v hv=> by rcases Finset.mem_insert.mp hv with hv|hv; subst v;exact hh;exact (cloud_has.mp hx).2 _ hv⟩
      have he:x∈farM i.1 i.2:= by change ¬ ε _* x _≤_ at hh; exact (lt_of_not_ge hh).le
      rw [further _ _ g u x he]; exact (round_money i T _ h.pays x hx u he).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) hA)
    intro x hx u; rw [quiet i.1 i.2 g u x ((cloud_has.mp hx).2 i (Finset.mem_univ _)), h.meets x hx u]
lemma memo_down (A:ℝ)(h:0≤A)(T:Finset Siteface)(f g:Garden D)(hp:Memos f g T A) : ∃ k,Memos f k ∅ ((1+∑ i, |treks D i|)^T.card *A):= by
    induction T using Finset.induction_on generalizing A g with
    | empty=> exact ⟨g,by simpa using hp⟩
    | insert i T he ih=>
       rw [Finset.card_insert_of_notMem he,pow_succ,mul_assoc];exact ih _ (by positivity) _ (memo_move _ _ _ _ _ h hp)
lemma cube_eq (D:ℕ): ∃ B:ℝ,0≤ B ∧∀ (f:Garden D) A,0≤A →(∀ x∈beam,∀ u:Brush D, |Dawn.halo f u x|≤A) → ∃ g,Memos f g ∅ (B*A):= by
    let B:ℝ:=(1+∑ i, |treks D i|)^(Finset.univ:Finset Siteface).card; exact ⟨B,by unfold B; positivity,fun f A h hp=> memo_down A h Finset.univ f f ⟨hp,fun _ _ _=>rfl⟩⟩
end YM.FormalBulk08.Annex
