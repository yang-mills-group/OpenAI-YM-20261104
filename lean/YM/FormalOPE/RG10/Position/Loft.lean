import YM.FormalOPE.RG10.Position.Stages

/-!
# Choose once, take the real-equivariant *graded* off-shell lift

All tokens at their own weight. Larger pure field letters use identical polynomial lifts;
not saying the corresponding bare stencil reconstructed from the columns of a new longer section
equals the original ones. `Lift`: choose in coordination with RG06/11, including any additional
orthogonal-normalization conditions on the chosen bases. `Loft.ready` proves these **particular**
horizon/unit/real/grade/H requirements admit a simultaneous solution. None of this permits using
raw pivot axes not H-covariant as if they were. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Position
open Function Maxwell Labels Extraction Filter Finset Extra.FD MvPolynomial PertExtension
open scoped Topology BigOperators ContDiff Classical
variable {G : Gauge} (F : Frames G)
local notation "W" d => Table.Field (freeTable F) d
local notation "R" d => recorded F d
local notation "ιH" => Signed.inclusionO
local notation "φ" d=> writes F d
variable (d:ℕ){h k : ℕ}
namespace Deck
def slots (i : Deck F d) := ((F.level i.1.val).grades (Horizon.reference i.1.val F i.2.val)).2
def grades (i : Deck F d) := (price F d i, slots F d i)
def start : Deck F d := ⟨0,0,le_antisymm ((F.level 0).bound (Horizon.reference 0 F 0)) (Nat.zero_le _)⟩
lemma grades_increments (hi:h≤k) (i:Deck F h) : grades F k (climb F hi i)= grades F h i:=rfl
end Deck

open Deck
lemma ground : deck F d (start F d)=(freeTable F).unit d := by
 apply writes_inj F d
 rw [deckAt,written,writes_unit]; convert! congr_arg (writes F 0) (R 0).unit_ |>.trans (writes_unit ..)
lemma real_move (s : Ortho) (x : W d) :
    (freeTable F).conj (table_spin F) d (ride F s d x) = ride F s d ((freeTable F).conj (table_spin F) d x):=by
  have hs : Surjective (sourceAt F d) := by
    intro x; obtain ⟨v,rfl⟩ := (freeTable F).onto d x
    obtain ⟨v,rfl⟩ := (F.level d).coords.surjective v; exact ⟨v,rfl⟩
  obtain ⟨v,rfl⟩ := hs x; apply writes_inj F d
  rw [writes_bar,ride_at,ride_at,writes_bar,form,← observe_rot,← observe_bar,real_turn,←observe_bar,observe_rot]
lemma tensor_unit (s : Ortho) : tensor s (Labels.unit G d)=Labels.unit G d := Subtype.ext (map_one (rotated s))
lemma ride_high (hu:h≤k) (s: Ortho) (x : W h) : ride F s k (higher F hu x)= higher F hu (ride F s h x) := by
  apply writes_inj F k; rw [writes_higher,ride_at,writes_higher,ride_at]
lemma moves (x : W d) (s t : Ortho) : ride F s d (ride F t d x)=ride F (s*t) d x := by
  apply writes_inj F d; rw [ride_at,ride_at,ride_at,pull_mul]
lemma no_move (x : W d) : ride F 1 d x=x:=by apply writes_inj F d; rw [ride_at,pull_one]
lemma move_unit (s:Ortho) : ride F s d ((freeTable F).unit d)=(freeTable F).unit d := by
  apply writes_inj F d; rw [ride_at,writes_unit]; exact map_one _

private theorem pure_turns (s : Ortho) (p : Label G d) (m) (hp : p∈ Grade m) : tensor s p∈Grade m:=by
  have ht:= gradePart_mem m (tensor s p); rw [gradePart_turn,gradePart_self p m hp] at ht; exact ht
lemma purity (p : Label G d) (m) (hp : p∈ Grade m) :
    IsWeightedHomogeneous compileW (observable G d p) m :=
  gradeMove bidegree compileW reduceEq (gradientReduce (fun i => (i+2,1))) _ _ ((pure_grade _ _).1 hp)
def precedent (i:Deck F d) : Label G d := raiseLabel G (price_bound F d i) ((F.level i.1.val).basis (Horizon.reference i.1.val F i.2.val))
lemma advance (i:Deck F d) : precedent F d i ∈ Grade (Deck.grades F d i):= by
  rcases i with ⟨j,v,hv⟩; let x:= Horizon.reference j.val F v
  let g:= (F.level j.val).grades x
  change (F.level j.val).basis x ∈ Grade (j.val,g.2)
  rw [show (j.val,g.2)=g from Prod.ext hv.symm rfl]; exact (F.level j.val).pure _

lemma precedent_real (i:Deck F d) : realBar (precedent F d i)= precedent F d i:= by
  apply Subtype.ext; exact congr_arg (fun v:Label G i.1.val=>v.val) ((F.level i.1.val).realForm (Horizon.reference i.1.val F i.2.val))
lemma kept (i:Deck F d) : observable G d (precedent F d i)= writes F d (deck F d i) := by
 rw [deckAt,written];
 calc
  _ = writes F i.1.val (Extra.FD.pack F (Horizon.reference i.1.val F i.2.val)):= (form ..).symm
  _ = _:= congr_arg (writes F i.1.val) ((R i.1.val).corners i.2.val |>.choose_spec).symm
lemma grade_written (i:Deck F d) : IsWeightedHomogeneous compileW (writes F d (deck F d i)) (Deck.grades F d i) :=
  kept F d i ▸ purity d _ _ (advance F d i)
lemma grades_ground : Deck.grades F d (start F d) = (0,0) := by
  have he:= grade_written F d (start F d); rw [ground,writes_unit] at he
  exact (he (d:=0) (by simp)).symm.trans (map_zero _)
lemma prime_ground : precedent F d (start F d) = Labels.unit G d := by
  have ht:= advance F d (start F d); rw [grades_ground] at ht
  obtain ⟨r,hr⟩:=Labels.scalar_grade 0 ht; have ht:= kept F d (start F d); rw [hr,ground,writes_unit,map_smul,show observable G d (Labels.unit G d)=1 from map_one reduceEq] at ht
  have hr':= congr_arg (MvPolynomial.coeff 0) ht
  rw [coeff_smul, coeff_one,if_pos rfl,smul_eq_mul,mul_one] at hr'; simp_rw [hr, hr',one_smul]

lemma grade_zero {p : W d} {m} (i : Deck F d) (hi : m ≠ Deck.grades F d i) (hp : IsWeightedHomogeneous compileW (writes F d p) m) : (deck F d).repr p i=0 := by
  let b:= deck F d; let c (j):= if m=Deck.grades F d j then b.repr p j else 0
  have h j := weightedHomogeneousComponent_of_mem (m:=m) (grade_written F d j)
  have he : ∑ j, c j • b j=p:=by
    apply writes_inj F d; rw [_root_.map_sum]; simp_rw [map_smul]
    have hv:= congr_arg ((weightedHomogeneousComponent compileW m) ∘ (writes F d)) (b.sum_repr p)
    simp only [comp_apply,_root_.map_sum,map_smul,hp.weightedHomogeneousComponent_same] at hv
    rw [← hv]; apply sum_congr rfl; intro j _; unfold b c; rw [h]; split <;> simp [b]
  have hj: b.repr p i=c i:=by
    rw [← he]; simp only [_root_.map_sum,Finsupp.finsetSum_apply,map_smul,Finsupp.smul_apply,Module.Basis.repr_self,Finsupp.single_apply,smul_eq_mul,mul_ite,mul_one,mul_zero]; simp
  exact hj.trans (if_neg hi)

structure Loft (F : Frames G) where
  lift : ∀ d, ((freeTable F).Field d) →ₗ[ℂ] Label G d

namespace Loft
structure Level (P : Loft F) : Prop where
  warmth d x : observable G d (P.lift d x) = writes F d x
  grade d m x (hp : IsWeightedHomogeneous compileW (writes F d x) m) : P.lift d x ∈ Grade m
  oriented d (j : Signed) x : tensor j.ortho (P.lift d x) = P.lift d (ride F j.ortho d x)
  form d x : realBar (P.lift d x)= P.lift d ((freeTable F).conj (table_spin F) d x)
  unit d : P.lift d ((freeTable F).unit d)=Labels.unit G d
  shelf (h k : ℕ) (hk:h ≤ k) x : P.lift k (higher F hk x) = raiseLabel G hk (P.lift h x)

def preliminary : Loft F where
  lift d:= (deck F d).constr ℂ (precedent F d)
variable {F}
lemma pole (i : Deck F d) : (preliminary F).lift d (deck F d i)=precedent F d i := Module.Basis.constr_basis ..
lemma homogeneity {x : W d} (m) (hp : IsWeightedHomogeneous compileW (writes F d x) m) :
    (preliminary F).lift d x∈ Grade m := by
  rw [← (deck F d).sum_repr x]
  rw [_root_.map_sum]; apply Submodule.sum_mem; intro i _; by_cases h:m=Deck.grades F d i
  · rw [map_smul,pole]; exact Submodule.smul_mem _ _ (h.symm ▸ advance F d i)
  rw [grade_zero _ d i h hp,zero_smul, map_zero]; exact Submodule.zero_mem _
lemma warmth {x : W d} : observable G d ((preliminary F).lift d x) = writes F d x :=
  let he : (observable G d).comp _ = writes F d := (deck F d).ext (fun i=> by change observable G d ((preliminary F).lift d (deck F d i)) = _; rw [pole,kept]);
  DFunLike.congr_fun he x

lemma radiance {x : W d} : realBar ((preliminary F).lift d x)= (preliminary F).lift d ((freeTable F).conj (table_spin F) d x) := by
  rw [← (deck F d).sum_repr x]; simp_rw [_root_.map_sum,map_smul, map_smulₛₗ, deck_real, pole,precedent_real]; rfl
lemma upper (hu:h ≤ k) (x : W h) : (preliminary F).lift k (higher F hu x) = raiseLabel G hu ((preliminary F).lift h x) := by
  rw [← (deck F h).sum_repr x]
  simp_rw [_root_.map_sum,map_smul,cabin,pole]
  rfl
lemma faithful (x:Label G h) : higher F (show h ≤ h from le_rfl) (sourceAt F h x) = sourceAt F h x:= by
  apply writes_inj F h; rw [writes_higher]

open Signed
def shift (F : Frames G) (d) (s : Signed) : ((freeTable F).Field d) →ₗ[ℂ] Label G d:= (tensor (ιH s)⁻¹).comp (((preliminary F).lift d).comp (ride F (ιH s) d))
lemma turn_bar (x:W d) (s:Signed) : realBar (shift F d s x)=shift F d s ((freeTable F).conj (table_spin F) d x) := by
  unfold shift; simp_rw [LinearMap.comp_apply,real_turn,radiance,real_move]
lemma respected (s:Ortho) {x : W d} (m) (hp : IsWeightedHomogeneous compileW (writes F d x) m) : IsWeightedHomogeneous compileW (writes F d (ride F s d x)) m:=by
  rw [ride_at,← warmth,← observe_rot]
  exact purity d _ _ (pure_turns d s _ _ (homogeneity _ m hp))
lemma rotated (x:W d) (s t : Signed) : shift F d s (ride F t.ortho d x)= tensor t.ortho (shift F d (s*t) x) := by
  unfold shift; simp_rw [LinearMap.comp_apply]
  change tensor (ιH s)⁻¹ ((preliminary F).lift d (ride F (ιH s) d (ride F (ιH t) d x))) = tensor (ιH t) _
  rw [moves,map_mul,mul_inv_rev,← tensor_mul,← mul_assoc,mul_inv_cancel,one_mul]

variable (F)
local notation "c" => (Fintype.card Signed : ℂ)⁻¹
def standard : Loft F where
  lift d:= c • ∑ s:Signed, shift F d s
lemma ready : Level F (standard F) := by
  have h : (Fintype.card Signed : ℂ) ≠ 0:=Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  constructor
  · intro d x
    have he(s:Signed) : observable G d (shift F d s x)=writes F d x := by
      unfold shift; rw [LinearMap.comp_apply,observe_rot,LinearMap.comp_apply,warmth,ride_at,← pull_mul,inv_mul_cancel,pull_one]
    simp [standard,he,_root_.map_sum,← Nat.cast_smul_eq_nsmul ℂ,h,smul_smul]
  · intro d m x hp; unfold standard; simp only [LinearMap.smul_apply,LinearMap.sum_apply]; apply Submodule.smul_mem; apply Submodule.sum_mem
    intro s _; exact pure_turns d _ _ m (homogeneity d m (respected d _ m hp))
  · intro d t x; unfold standard; simp only [LinearMap.smul_apply,LinearMap.sum_apply,_root_.map_sum,map_smul]
    simp_rw [rotated d x _ t]
    exact congr_arg (fun v : Label G d=> c • v) ((Equiv.sum_comp (Equiv.mulRight t) (fun s=> tensor t.ortho (shift F d s x))).symm)
  · intro d x; simp_rw [standard,LinearMap.smul_apply,LinearMap.sum_apply,map_smulₛₗ,_root_.map_sum,turn_bar]; simp
  · intro d
    have he (s:Signed) : shift F d s ((freeTable F).unit d)=Labels.unit G d:=by unfold shift; rw [LinearMap.comp_apply,LinearMap.comp_apply,move_unit,← ground,pole,prime_ground,tensor_unit]
    simp [standard,he,← Nat.cast_smul_eq_nsmul ℂ,h,smul_smul]
  intro d e hd x
  have he (s:Signed) : shift F e s (higher F hd x)=raiseLabel G hd (shift F d s x) := by unfold shift; simp_rw [LinearMap.comp_apply,ride_high,upper]; rfl
  simp only [standard,LinearMap.smul_apply,LinearMap.sum_apply,map_smul, _root_.map_sum,he]
end Loft
end YM.FormalOPE.RG10.Position
