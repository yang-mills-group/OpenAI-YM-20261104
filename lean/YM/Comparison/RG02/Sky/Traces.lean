import YM.Comparison.RG02.Cumulants.Wick
import YM.Overlay.Terminal
/-!
# Charged connected drawings, before even positions

 use Wick recursion operator; produces list (count every choice), no simplifying weights by
 symmetry. All legs numbered; in more generic Tilt-comparison can have mean-loops, here specialize
 to full conditional *centered* flat Q, external/bilinears reabsorbed in **vertex generator**. No
 need for pair classification from manuscript. On finite arity only.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Sky.Traces
open Finset Lattice Function Marker Multi Cumulants Cumulants.Wick
open Extra.Trajectories (connected)
open Next.Rank
open scoped BigOperators Topology Classical

variable {I A J : Type*} [DecidableEq I] [DecidableEq A] [Fintype A] (π:I→A)
abbrev Path (I : Type*) := List (I × I)

-- The same active-root leg deterministic choice as Wick.trees (note Uses FULL Vertex census).
local notation "Ω"=> Stock.final A
def circle (p:Finset I) (S:Finset A) (N : ℕ): List (Path I) :=
  if h:(legs π p S).Nonempty then match N with
  | 0=> []
  | r+1=>
     let i:= Classical.choose h
     (legs π (p.erase i) (Ω).val).toList.flatMap fun j=> (circle ((p.erase i).erase j) (insert (π j) S) r).map ((i,j)::·)
  else if S=(Ω).val then [[]] else []
termination_by N

variable (Q : I→I→ℂ)
def price (w : Path I):= (w.map fun i=> Q i.1 i.2).prod
omit [DecidableEq I] in
lemma price_add (w : Path I) (i j : I) : price Q ((i,j)::w)= Q i j * price Q w:= by simp [price]

private lemma many {A B R: Type*}[AddCommMonoid R](L:List A)(f:A→List B)(g:B→R): ((L.flatMap f).map g).sum=(L.map fun a=> ((f a).map g).sum).sum:= by
   induction L with
   | nil=> simp
   | cons a l ih=> simp [ih]
variable (c : Normal.Symmetric J) (q:I→J)
local notation "pr"=> price (fun i j => c.cov (q i) (q j))
def Cooperates (c : Normal.Symmetric J)(q:I→J) (p:Finset I)(S:Finset A)(N:ℕ)(T:List (Path I)) := ((T.map pr).sum:ℂ)=trees π q c 0 Ω S p N -- mirror trace semantics
lemma count (p:Finset I)(S:Finset A)(N:ℕ) : ((circle π p S N).map pr).sum = trees π q c 0 Ω S p N:= by
   induction N generalizing p S with
   | zero=>
      rw [circle,trees]; split_ifs <;> simp [price]
   | succ n ih=>
      rw [circle,trees]; split_ifs with h H
      · let i:= Classical.choose h
        change (( (legs π (p.erase i) (Ω).val).toList.flatMap (fun j=> (circle π ((p.erase i).erase j) (insert (π j) S) n).map ((i,j)::·))).map pr).sum=0 * trees π q c 0 Ω S (p.erase i) n + ∑ j∈legs π (p.erase i) (Ω).val, c.cov (q i) (q j) * trees π q c 0 Ω (insert (π j) S) ((p.erase i).erase j) n
        rw [zero_mul,zero_add,many, Finset.sum_map_toList]; refine sum_congr rfl fun j _=> ?_
        change (((circle π ((p.erase i).erase j) _ n).map ((i,j)::·)).map pr).sum=_
        rw [List.map_map, show pr ∘ ((i,j)::·) = fun a=> c.cov (q i) (q j)* pr a from funext fun _=> price_add .., List.sum_map_mul_left, ih]
      all_goals simp [price]

lemma carried (p:Finset I)(a:A)(N:ℕ)(h:p.card≤N): (connected (moments (Stock.census A) (Normal.blend c 0) (word π q p))).part Ω = ((circle π p {a} N).map pr).sum:= by
   rw [count, connected_tree π q c 0 Ω a (mem_univ _) p N h]

def Travels (w:Path I)(s:Finset A):Prop := ∀ j∈w, π j.1∈ s → π j.2 ∈ s
lemma floods (S s:Finset A)(H:S⊆s)(p:Finset I)(N:ℕ)(w:Path I)(h:w ∈ circle π p S N)(ht:Travels π w s): ∀ v:A,v∈s:= by
   induction N generalizing p S w with
   | zero=>
      rw [circle] at h; split_ifs at h with hb hS; all_goals first| (exact fun v=>H (hS.symm ▸ (mem_univ v : v∈(Ω).val))) | simp at h
   | succ n ih=>
      rw [circle] at h; split_ifs at h with hb hS
      · simp only [List.mem_flatMap,List.mem_map] at h
        obtain ⟨j,hj,w',h,rfl⟩:=h
        apply ih _ _ _ w' h
        · exact fun i hi=> ht _ (List.mem_cons_of_mem _ hi)
        exact insert_subset (ht (_,j) (List.mem_cons_self) (H (mem_filter.mp (Classical.choose_spec hb)).2)) H
      · exact fun v=>H (hS.symm ▸ (mem_univ v : v∈(Ω).val))
      simp at h

lemma path_prices {I : Type*} (Q:I × I→ℂ)(w:Path I): (w.map Q).prod=∏ i,Q (w.get i):= by
   have h : w.map Q=List.ofFn (Q ∘ w.get):= by rw [← List.map_ofFn]; simp
   rw [h,List.prod_ofFn]; rfl
omit [DecidableEq I] in
lemma charge_prices (Q:I→I→ℂ)(w:Path I) : price Q w=∏ i,Q (w.get i).1 (w.get i).2:= path_prices ..
lemma listed {I A:Type*} [AddCommMonoid A] (f:I→A)(w:List I) : (w.map f).sum=∑ i,f (w.get i):= by
   have h:w.map f=List.ofFn (f ∘ w.get):=by rw [← List.map_ofFn]; simp
   rw [h,List.sum_ofFn]; rfl
lemma count_charges (p:Finset I)(v:A)(N:ℕ)(he:p.card≤N) :
     (connected (moments (Stock.census A) (Normal.blend c 0) (word π q p))).part Ω=
       ∑ i, pr ((circle π p {v} N).get i) := by rw [carried π c q p v N he, listed]
end YM.Comparison.RG02.Sky.Traces
