import YM.XSpace.WideLeg
/-! # Real-ray isolation of transmitted color pair -/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Stab
open Function Set Filter MeasureTheory Next.Rank Normal Maxwell Maxwell.Free ProbeLine MvPolynomial
open scoped Topology BigOperators InnerProductSpace ContDiff Classical Polynomial
variable {G : Gauge}

-- finite tables of polynomial variations
inductive Flows {V : Type*} : (ℝ→poly V)→poly V→Prop
| one (p:poly V): Flows (fun _=>p) p
| add {f g p q}:Flows f p→ Flows g q→Flows (f+g) (p+q)
| times {f g p a}:Flows f p→Proves g a→Flows (fun t=>g t • f t) (a • p)
| along {f g p}:Flows f p→f=ᶠ[atTop]g→Flows g p
namespace Flows
variable {V:Type*}{p q:poly V} {f g:ℝ→poly V}
lemma mark {g:ℝ→ℂ}{a:ℂ}(h:Proves g a): Flows (V:=V) (fun t=>MvPolynomial.C (g t)) (MvPolynomial.C a):= by simpa only [← C_mul',mul_one] using (Flows.one (1:poly V)).times h
lemma fixed {V:Type*}(p:poly V):Flows (fun _=>p) p:= one p
lemma right (h:Flows f p)(q:poly V): Flows (fun t=> q*f t) (q*p):= by
  induction h with
  | one p=> exact Flows.one _
  | @add f g p v _ _ ih ih' => simpa only [Pi.add_def,mul_add] using ih.add ih'
  | @times f g p a _ hu ih => simpa only [mul_smul_comm] using! ih.times hu
  | along hp h ih => exact ih.along (h.mono fun i hx=> congr_arg _ hx)
lemma mul (h:Flows f p)(H:Flows g q): Flows (f*g) (p*q):= by
  induction h with
  | one p=> exact H.right _
  | @add f g p v _ _ h H=> simpa only [add_mul] using h.add H
  | @times a b f t hb he ih => simp only [Pi.mul_def, smul_mul_assoc t]; convert! ih.times he using 1; exact _root_.funext fun r=>smul_mul_assoc ..
  | along hp h ih=> exact ih.along (h.mono fun i hi=>congr_arg (·*g i) hi)
lemma checks {x:poly V}(L:poly V→ₗ[ℂ] ℂ)(h:Flows f x): Proves (fun i=>L (f i)) (L x) := by
  induction h with
  | one p=>exact Proves.unit _
  | @add f g x y ha hp h h'=> simp only [Pi.add_apply,map_add]; exact h.add h'
  | times ha he ih=> simp only [_root_.map_smul,smul_eq_mul]; exact he.mul ih
  | along _ he ih=> exact ih.alter (he.mono fun i hi=> congr_arg _ hi)
lemma sum {α:Type*} {A : Type*} (s: Finset α) (f:α→ℝ→poly A)(g:α→poly A)(h :∀ i∈s,Flows (f i) (g i)) : Flows (fun t=>∑ i∈s,f i t) (∑ i∈s,g i):= by
  induction s using Finset.induction_on with
  | empty=> simp; exact Flows.one _
  | @insert j s hj ih=> simp_rw [Finset.sum_insert hj]; exact (h j (Finset.mem_insert_self ..)).add (ih fun i hi=>h i (Finset.mem_insert_of_mem hi))
end Flows

variable {S:Set E4}{m u v:E4}
local notation "x" => (m+v)
local notation "y" => (m-v)
variable (c:G.ColorIndex)(p: Flavor 0) (i:G.ColorIndex)

def weight (m u v : E4) (r:ℝ):ℂ:= ((rsq (drifts m u (m+v) r)^3:ℝ):ℂ)
def diff (m u v:E4)(p:Flavor 0)(i:G.ColorIndex)(t:ℝ) : Derivation ℂ (Web G) (Web G):= weight m u v t • scrape (m+t • u) p i
lemma diff_at (f:Web G)(t:ℝ): diff m u v p i t f= weight m u v t • scrape (m+t • u) p i f := rfl
lemma read_p (H:Congruent S m v u): Proves (weight m u v) 0:= by
  have ht:= (square_match m u x).pow 3; unfold weight; simp_rw [Complex.ofReal_pow]; simpa only [H.null_one, zero_pow (show 3≠0 by omega), Pi.pow_def] using ht

lemma dust (H:Congruent S m v u) (b:WebKey G) (hb:b.1∈S): Flows (fun t=> diff m u v p i t (X b)) 0 := by
  let a:=flavor (G:=G) 0 i p
  obtain ⟨c',h⟩:= Soup.along (true_pole a (coordinateLeg b.2)) H.raw (H.regular b.1 hb)
  have hp: ∀ t, factors b.1 (coordinateLeg b.2)=MvPolynomial.X b:= fun (t:ℝ)=> by unfold factors; rw [symbol_coordinate,post_X]
  have he:= Flows.mark (V:=WebKey G) ((read_p H).mul h); rw [zero_mul,map_zero] at he
  refine he.along ?_; filter_upwards [wandering m u _ H.raw] with r hr
  rw [← hp r,diff_at]; unfold scrape; rw [remainder_eqn, if_neg ((sub_ne_zero.mp hr):m+r • u≠b.1)]
  rw [Pi.mul_apply,map_mul,C_mul']; rfl

-- transmission for fixed polynomial columns
structure Receiving (m u v:E4)(p:Flavor 0)(i:G.ColorIndex)(a a' a'' : Web G):Prop where
  first: Flows (fun r=> diff m u v p i r a) a'
  twice: Flows (fun r=> diff m u v p i r (diff m u v p i r a)) a''
namespace Receiving
variable {p i}{a b a' b' a'' b'':Web G} (h:Receiving m u v p i a a' a'')
include h in
lemma add (hb:Receiving m u v p i b b' b''): Receiving m u v p i (a+b) (a'+b') (a''+b'') := by
  constructor
  · simp only [map_add]; exact h.first.add hb.first
  simp only [map_add]; exact h.twice.add hb.twice
lemma scalar (c : ℂ): Receiving m u v p i (MvPolynomial.C c:Web G) 0 0:= by constructor <;> (simp [diff_at,scrape]; exact Flows.one _) -- inspect
include h in
lemma mul (hb:Receiving m u v p i b b' b''): Receiving m u v p i (a*b) (a*b'+a'*b) ((a*b''+a'*b')+(a'*b'+a''*b)):= by
  have he (f g:Web G)(r:ℝ) : diff m u v p i r (f*g)=f*diff m u v p i r g+diff m u v p i r f*g:= by simp only [Derivation.leibniz,smul_eq_mul,mul_comm g]
  constructor
  · simp_rw [he]; exact ((Flows.one a).mul hb.first).add (h.first.mul (Flows.one b))
  simp_rw [he,_root_.map_add,he]; exact (((Flows.one a).mul hb.twice).add (h.first.mul hb.first)).add ((h.first.mul hb.first).add (h.twice.mul (Flows.one b)))
lemma sum {α:Type*} (s: Finset α) (f F D:α→Web G)(h:∀ j∈s,Receiving m u v p i (f j) (F j) (D j)): Receiving m u v p i (∑ j∈s,f j) (∑ j∈s,F j) (∑ j∈s,D j):= by
  constructor
  · simp only [map_sum]; exact Flows.sum _ _ _ fun j hj=> (h j hj).first
  simp only [map_sum]; exact Flows.sum _ _ _ fun j hj=> (h j hj).twice
lemma mark1 (m u v:E4) (p:Flavor 0) (i:G.ColorIndex) {f: Web G} {r:ℂ} (g:ℝ→ℂ) (h: Proves g r) (b : (fun t=> diff m u v p i t f)=ᶠ[atTop] (fun t=> MvPolynomial.C (g t))): Receiving m u v p i f (MvPolynomial.C r) 0:= by
  refine ⟨(Flows.mark h).along b.symm,(Flows.one _).along (b.mono fun t ht=>?_)⟩
  change diff m u v p i t f=MvPolynomial.C _ at ht; dsimp only; rw [ht]; simp  -- inspect
end Receiving
lemma grounds (b:Web G) (H:Congruent S m v u) (hb: ∀ i∈b.vars,i.1∈S) : Receiving m u v p i b 0 0:= by
  let f := Subtype.val (p:=fun i=> i∈b.vars)
  obtain ⟨a,ha⟩:= exists_rename_eq_of_vars_subset_range b f Subtype.val_injective (fun l hl=> ⟨⟨l,hl⟩,rfl⟩)
  suffices ∀ a, Receiving m u v p i (rename f a) 0 0 from ha ▸ this a
  intro a
  induction a using MvPolynomial.induction_on with
  | C c=> rw [rename_C]; exact Receiving.scalar _
  | add a b h hh => rw [map_add]; simpa using h.add hh
  | mul_X a j hh=>
    rw [map_mul,rename_X]
    have he:Receiving m u v p i (X (f j)) 0 0:= by
      refine ⟨dust p i H (f j) (hb _ j.property),?_⟩
      simp_rw [diff_at,scrape,slit_X,(slit _).map_smul,slit_C,smul_zero]; exact Flows.one 0
    simpa using hh.mul he
lemma from_x (j:G.ColorIndex)(q:Flavor 0)(H:Congruent S m v u): Receiving m u v p i (singleF x q j) (if j=i then C (bilinear (⟨H.raw,H.null_one⟩:Sky m u x) c p q) else 0) 0:= by
  let W:= (⟨H.raw,H.null_one⟩:Sky m u x)
  by_cases h:j=i
  · subst j; rw [if_pos rfl]; apply Receiving.mark1 _ _ _ _ _ _ (test_residue W c p q) -- inspect
    filter_upwards [wandering m u x H.raw] with r hr; rw [diff_at, singleF, through_eqn (sub_ne_zero.mp hr) _ q c, if_pos rfl, ← C_mul',← _root_.map_mul]; congr 1; exact (Complex.ofReal_mul ..).symm
  rw [if_neg h]; nth_rw 1 [← show C (σ:=WebKey G) (0:ℂ)=0 from map_zero _]; apply Receiving.mark1 _ _ _ _ _ _ (Proves.unit _)
  filter_upwards [wandering m u x H.raw] with r hr; rw [diff_at,singleF, through_eqn (sub_ne_zero.mp hr) _ q c, if_neg h,map_zero, smul_zero]
lemma from_y (j:G.ColorIndex)(q:Flavor 0)(H:Congruent S m v u): Receiving m u v p i (singleF y q j) (if j=i then C (bilinear (⟨H.raw,H.null_two⟩:Sky m u y) c p q) else 0) 0:= by
  let W:= (⟨H.raw,H.null_two⟩:Sky m u y)
  by_cases h:j=i
  · subst j; rw [if_pos rfl]; apply Receiving.mark1 _ _ _ _ _ _ (test_residue W c p q)
    filter_upwards [wandering m u y H.raw] with r hr; rw [diff_at,singleF, through_eqn (sub_ne_zero.mp hr) _ q c, if_pos rfl, ← C_mul', ← map_mul, weight,H.twins]; congr 1; exact (Complex.ofReal_mul ..).symm
  rw [if_neg h]; nth_rw 1 [← show C (σ:=WebKey G) (0:ℂ)=0 from map_zero _]; apply Receiving.mark1 _ _ _ _ _ _ (Proves.unit _)
  filter_upwards [wandering m u y H.raw] with r hr; rw [diff_at,singleF, through_eqn (sub_ne_zero.mp hr) _ q c, if_neg h,map_zero, smul_zero]
end YM.XSpace.Stab
