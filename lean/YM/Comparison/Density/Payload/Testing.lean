import YM.Comparison.Density.Markers.Purchases
/-!
# Slotted markers

Tests can be held during transformations, with the test cost (unit
supremum for each independent argument in a product coefficient) INSIDE
all weighted estimates. Slottedness prohibits nonlinear or out-of-slot
test dependence. Distinct markers for all positions/slots, using Census
as usual (also the old/orbit disjoint rules). The testing space needn't
be finite dimensional. `Region` supplies an address restriction relation,
as strong as the estimates demand (in a fixed-lift application only use
actual test cells, not identifications of translated test functions or
periodizing omitted endpoints). This is a real-output representation
norm, not a bound for a stronger analytical norm involving particular
path or derivative-measure presentations.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Comparison.Density.Testing
open Marker Lattice Set Function MeasureTheory Filter
open scoped BigOperators Topology
variable {V : Type} [DecidableEq V] {R : Census V} {n : Side}
variable {X : V→Type} [∀ v, NormedAddCommGroup (X v)] [∀ v, NormedSpace ℂ (X v)]
variable {E : Type*} [AddCommGroup E] [Module ℂ E]

abbrev Cross (X : V→Type) := ∀ v, X v

def UnitPage (x : Cross X) := ∀ i, ‖x i‖ ≤ 1

omit [DecidableEq V] in
lemma normalize [Fintype V] (x : Cross X) : ∃ p : ℂ, ∃ y : Cross X, UnitPage y ∧ x=p • y := by
  let q : ℝ := ‖x‖+1
  have ht : 0<q := add_pos_of_nonneg_of_pos (norm_nonneg x) zero_lt_one
  have hq : ‖(q:ℂ)‖=q := by rw [Complex.norm_real,Real.norm_of_nonneg ht.le]
  refine ⟨q,(q:ℂ)⁻¹ • x,?_,?_⟩
  · intro i; simp only [Pi.smul_apply,norm_smul,norm_inv,hq]
    rw [← div_eq_inv_mul, div_le_one ht]
    exact (norm_le_pi_norm x i).trans (le_add_of_nonneg_right zero_le_one)
  rw [smul_smul,mul_inv_cancel₀ (norm_pos_iff.mp (by rwa [hq])),one_smul]

structure Slotted (s : Finset V) (f : Cross X → E) : Prop where
  fixed x y : (∀ i∈s, x i=y i) → f x=f y
  changes i : i∈s → ∀ x, IsLinearMap ℂ (fun u : X i => f (update x i u))

structure Region (X : V→Type) (n : Side) where
  knows : ∀ i, Support n → X i → X i → Prop
  reflexive i S a : knows i S a a
  -- `knows i S` says the two test arguments agree AT EVERY ADDRESS
  -- allowed by using support S and that marker. Larger supports may
  -- authorize more addresses; no wrapping/hull inference here.
  tighter i : ∀ (S T : Support n), S⊆T → ∀ a b, knows i T a b → knows i S a b

def Reads (r : Region X n) (S : Support n) (s : Finset V) (f : Cross X → E) :=
  ∀ x y, (∀ i∈s,r.knows i S (x i) (y i)) → f x=f y

variable {s t u : Finset V} {S : Support n}
namespace Slotted
variable {f : Cross X → E}
lemma allScale (h : Slotted s f) (x : Cross X) (a : V→ℂ) : f (fun i=>a i • x i) = (∏ i∈s, a i) • f x := by
  classical
  let scaled (t : Finset V) := fun i=> if i∈t then a i • x i else x i
  have hx (t : Finset V) (ht : t⊆s) : f (scaled t) = (∏ i∈t,a i) • f x := by
    induction t using Finset.induction with
    | empty=> simp [scaled]
    | insert i t hi ih=>
      have he : i∈s := ht (Finset.mem_insert_self ..)
      have hs : scaled (insert i t)=update (scaled t) i (a i • x i):= by
        funext j; by_cases hq:j=i
        · subst j; simp [scaled]
        simp [scaled,hq]
      have hy : update (scaled t) i (x i)=scaled t:= by
        conv_lhs => arg 3; rw [show x i=scaled t i by simp [scaled, hi]]
        exact update_eq_self ..
      rw [Finset.prod_insert hi,hs]; rw [(h.changes i he (scaled t)).map_smul (a i) (x i),hy,ih ((Finset.subset_insert ..).trans ht),smul_smul]
  rw [h.fixed _ (scaled s) (by intro i hi; simp [scaled,hi]),hx s le_rfl]

lemma stretch (h : Slotted s f) (p : ℂ) (x : Cross X) : f (p • x) = p^s.card • f x := by
  simpa only [Finset.prod_const] using! h.allScale x (fun _ => p)

lemma vacant : Slotted s (fun _ : Cross X=> (0:E)):= ⟨fun _ _ _=>rfl,fun _ _ _=>⟨fun _ _=>by simp,fun _ _=>by simp⟩⟩
lemma base (c : E) : Slotted ∅ (fun _ : Cross X=> c):= ⟨fun _ _ _=>rfl,fun _ h=> False.elim (Finset.notMem_empty _ h)⟩
lemma plus {g : Cross X → E} (hf : Slotted s f) (hg : Slotted s g) : Slotted s (f+g):= by
  refine ⟨fun x y h=> ?_,fun i hi x=>?_⟩
  · simp only [Pi.add_apply,hf.fixed x y h,hg.fixed x y h]
  obtain h:= hf.changes i hi x; obtain H := hg.changes i hi x
  exact ⟨fun a b=> by
    rw [Pi.add_apply, h.map_add a b,H.map_add a b]; simp only [Pi.add_apply]; abel,
    fun z a=>by rw [Pi.add_apply, h.map_smul z a, H.map_smul z a,Pi.add_apply,smul_add]⟩
lemma scale (h : Slotted s f) (a : ℂ) : Slotted s (a • f):= by
  refine ⟨fun x y he=> by simp only [Pi.smul_apply,h.fixed x y he],fun i hi x=>?_⟩
  obtain H:= h.changes i hi x
  exact ⟨fun x y=>by rw [Pi.smul_apply,H.map_add x y,Pi.smul_apply,Pi.smul_apply,smul_add],
    fun z x=>by rw [Pi.smul_apply,H.map_smul z x,Pi.smul_apply,smul_comm a z]⟩
lemma more_args {f g : Cross X→ℂ} (h : Slotted s f) (H : Slotted t g) (hp : Disjoint s t) : Slotted (s∪t) (f*g) := by
  have he {f g : Cross X→ℂ} {s t : Finset V} (h : Slotted s f) (H : Slotted t g)
      {i : V} (hi : i∈s) (hu : i∉t) (x : Cross X) : IsLinearMap ℂ (fun a=> (f*g) (update x i a)) := by
    have hx := h.changes i hi x
    have hk a : g (update x i a)=g x:= H.fixed _ _ fun j hj=> update_of_ne (by rintro rfl; contradiction) ..
    refine ⟨fun y z=>?_,fun y z=>?_⟩
    · rw [Pi.mul_apply,hx.map_add y z]; simp only [Pi.mul_apply, hk,add_mul]
    rw [Pi.mul_apply,hx.map_smul y z]; simp only [Pi.mul_apply,hk,smul_mul_assoc]
  refine ⟨fun x y hk=>?_,fun i hi x=>?_⟩
  · rw [Pi.mul_apply,h.fixed x y (fun i hi=> hk i (Finset.mem_union_left t hi)),H.fixed x y (fun i hi=> hk i (Finset.mem_union_right s hi)),Pi.mul_apply]
  rcases Finset.mem_union.mp hi with hk|hk
  · exact he h H hk (Finset.disjoint_left.mp hp hk) x
  rw [mul_comm]; exact he H h hk (Finset.disjoint_right.mp hp hk) x

lemma sums {ι : Type*} (F : ι→ Cross X → E) (I : Finset ι) (h : ∀ i ∈ I, Slotted s (F i)) : Slotted s (fun x => ∑ i∈I,F i x):= by
  classical
  induction I using Finset.induction with
  | empty=> simpa only [Finset.sum_empty] using! (vacant (X:=X) (E:=E) (s:=s))
  | insert i I hi ih => simp_rw [Finset.sum_insert hi]; exact (h i (Finset.mem_insert_self ..)).plus (ih fun i hi'=> h i (Finset.mem_insert_of_mem hi'))
lemma series {ι : Type*} (F : ι→ Cross X→ℂ) (h : ∀ i, Slotted s (F i)) (hx : ∀ x : Cross X,Summable fun i=>F i x) :
    Slotted s (fun x=> ∑' i,F i x) := by
  refine ⟨fun x y H=> tsum_congr (fun i=>(h i).fixed x y H),fun i hi x=> ⟨fun u w=> ?_,fun z w=>?_⟩⟩
  · simp_rw [(h _).changes i hi x|>.map_add u w]; exact Summable.tsum_add (hx _) (hx _)
  simp_rw [(h _).changes i hi x|>.map_smul z w]; exact Summable.tsum_const_smul z (hx _)
end Slotted

/-- Whole test-polynomial. Indicator branches can depend on links but
not on changing tests mid-selection. -/
structure Catalogue (r : Region X n) (S : Support n) (f : Cross X → Poly R) : Prop where
  pieces i : Slotted i.val (fun x => (f x).part i)
  track i : Reads r S i.val (fun x=> (f x).part i)

namespace Catalogue
open Finset Markers
variable {r : Region X n} {f g : Cross X → Poly R}
lemma roomier {T : Support n} (h : Catalogue r S f) (he : S⊆T) : Catalogue r T f :=
    ⟨h.pieces,fun i x y H=> h.track i x y (fun j hj=> r.tighter j S T he _ _ (H j hj))⟩
lemma empty : Catalogue r S (fun _ : Cross X => (0:Poly R)) := ⟨fun _=>Slotted.vacant,fun _ _ _ _=>rfl⟩
lemma pegged (a : ℂ) : Catalogue r S (fun _ : Cross X=> Poly.bead R a):= by
  refine ⟨fun i=>?_,fun _ _ _ _=> rfl⟩; simp only [Poly.bead,RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,Poly.part_send]
  by_cases he:i=R.quiet
  · subst i; simp only [if_true]; exact Slotted.base _
  simp only [if_neg he]; exact Slotted.vacant
lemma unit : Catalogue r S (fun _ : Cross X=> (1:Poly R)):= by simpa only [map_one] using (pegged (R:=R) 1 (r:=r) (S:=S))
lemma plus (h : Catalogue r S f) (H : Catalogue r S g) : Catalogue r S (f+g):= by
  refine ⟨fun i=> (h.pieces i).plus (H.pieces i),fun i x y he=>?_⟩
  simp only [Pi.add_apply, Poly.part_plus]; rw [show (f x).part i=(f y).part i from h.track i x y he,show (g x).part i=(g y).part i from H.track i x y he]
lemma times (h : Catalogue r S f) (H : Catalogue r S g) : Catalogue r S (f*g) := by
  refine ⟨fun i=>?_,fun i x y he=>?_⟩ <;> simp only [Pi.mul_apply, Poly.part_mul]
  · refine Slotted.sums _ _ fun j _=> Slotted.sums _ _ fun k _=> ?_
    by_cases hj : Poly.merges j k i
    · simp only [if_pos hj]; rw [← hj.2]; exact (h.pieces j).more_args (H.pieces k) hj.1
    simp only [if_neg hj]; exact Slotted.vacant
  refine Finset.sum_congr rfl fun j _=> Finset.sum_congr rfl fun k _=> ?_
  split
  next hK=>
    have hz : j.val ∪ k.val = i.val:= hK.2
    rw [show (f x).part j= (f y).part j from h.track j x y (fun v hv=> he v (hz ▸ mem_union_left k.val hv)), show (g x).part k= (g y).part k from H.track k x y (fun v hv=> he v (hz ▸ mem_union_right j.val hv))]
  rfl
lemma prod {ι : Type*} (I : Finset ι) (F : ι → Cross X → Poly R) (h : ∀ i∈I,Catalogue r S (F i)) : Catalogue r S (fun x=> ∏ i∈I,F i x):= by
  classical
  induction I using Finset.induction with
  | empty=> simp only [Finset.prod_empty]; exact Catalogue.unit
  | insert i I hi ih=> simp_rw [Finset.prod_insert hi]; exact (h i (Finset.mem_insert_self ..)).times (ih fun i hi'=> h i (mem_insert_of_mem hi'))
lemma power (h : Catalogue r S f) (m : ℕ) : Catalogue r S (fun x=> f x ^ m) := by
  induction m with
  | zero=> simp only [pow_zero]; exact Catalogue.unit
  | succ m ih=> simp_rw [pow_succ]; exact ih.times h
lemma sum {ι : Type*} (I : Finset ι) (F : ι → Cross X → Poly R) (h : ∀ i∈I,Catalogue r S (F i)) : Catalogue r S (fun x=> ∑ i∈I,F i x):= by
  classical
  induction I using Finset.induction with
  | empty=> simp only [Finset.sum_empty]; exact Catalogue.empty
  | insert i I hi ih=> simp_rw [Finset.sum_insert hi]; exact (h i (Finset.mem_insert_self ..)).plus (ih fun i hi'=> h i (mem_insert_of_mem hi'))
lemma smul (h : Catalogue r S f) (a : ℂ) : Catalogue r S (fun x=> a • f x) := by
  simp_rw [← Poly.product_bead]; exact (pegged a).times h
lemma sub (h : Catalogue r S f) (H : Catalogue r S g) : Catalogue r S (f-g) := by
  rw [sub_eq_add_neg]; have he : -g=fun x=> (-1:ℂ) • g x:= by simp; rfl
  rw [he]; exact h.plus (H.smul _)
lemma soaring [Fintype V] (h : Catalogue r S f) : Catalogue r S (Poly.pass ∘ f):= by
  unfold Poly.pass Function.comp; exact Catalogue.sum _ _ fun i _=> (h.power i).smul _
lemma friend [Fintype V] (a : ℝ) (h : Catalogue r S f) : Catalogue r S (fun x=> Markers.companion a (f x)):=
    Catalogue.sub ((pegged _).times h.soaring) unit
end Catalogue
end YM.Comparison.Density.Testing
