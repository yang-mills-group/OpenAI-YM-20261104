import YM.SchemeConversionRG11.FirstW.Ship.Home
import YM.MultiNext.SIGNED_SOURCE_CONTINUATION.Newtown
/-! Filtered native cover polynomials used for weighted Taylor tests. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.FirstW
open Function Lattice Pert Topology Filter Align
open scoped BigOperators Classical
open MultiNext.SignedSource
open Newt (jump)
variable {V E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {p : Cover→E} {d l : ℕ}
def Loft (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (d : ℕ) : Submodule ℝ (Cover→E) where
  carrier := setOf fun p=> ∀ D : List Axis,D.length=d+1→combine D p=0
  smul_mem' r A h:= fun i hi=> by rw [combine_smul,h i hi,smul_zero]
  add_mem' h t:= fun i hi=>by rw [combine_add,h i hi,t i hi,add_zero]
  zero_mem' :=fun i _ =>combine_zero _
lemma combine_top (h : p∈Loft E d) (D : List Axis) (hv:D.length>d) : combine D p=0 := by
  induction D with
  | nil => simp at hv
  | cons i t ih=>
    rw [List.length_cons] at hv
    rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp hv) with h'|hh
    · exact h _ (by rw [List.length_cons]; linarith only [h'])
    rw [combine,ih hh]; funext x; simp [up]
lemma loft_mono (h:d≤l) : Loft E d ≤ Loft E l:=fun _ ha i hi=> combine_top ha _ (by rw [hi]; omega)
omit [NormedSpace ℝ E] in
lemma switch_order (l:List Axis) (p:Cover→E): Newt.iterate p l=combine l p := by
  induction l generalizing p with
  | nil=>rfl
  | cons i l ih=> exact (ih (up i p)).trans (combine_up ..)
lemma loft_tail {k} (h : p∈Loft E k) : Newt.tail (k+1) p=0 := by
  funext x
  have hv := Newt.localized (p:=p) (k+1) (M:=0) le_rfl ((Laurent.size x:ℕ):ℝ) (fun D hD w _=>by rw [switch_order _ _,h D hD]; simp) x le_rfl
  exact norm_le_zero_iff.mp (by simpa using hv)
lemma take_up (k : ℕ) (p : Cover→E) (i : Axis) : up i (Newt.take (k+1) p)=Newt.take k (up i p) := by
  have H:=Newt.currency k p i; funext x; change Newt.take _ _ (x+step i)- _ = _; have he:=congrFun H x
  change (p (x+step i)-_)-(p x-_)=(p (x+step i)-p x)-Newt.take k (up i p) x at he; grind -- abel
lemma loft_adapt (k : ℕ) (p : Cover→E): Newt.take (k+1) p∈Loft E k := by
  induction k generalizing p with
  | zero=>
    intro D hD; rcases List.length_eq_one_iff.mp hD with ⟨i,rfl⟩; funext x; simp [Newt.take,Newt.piece,combine,up]
  | succ k ih=>
    rintro (_|⟨a,b⟩) hv; · simp at hv
    rw [combine,←combine_up,take_up]; exact (ih (up a p)) b (by rw [List.length_cons] at hv; omega)
open Laurent (size)
def fiat (k : ℕ) : Cover → ℝ := fun x=>(1+(size x:ℝ))^k
lemma yard_size (x : Cover) : yard x≤ size x := by
  obtain ⟨j,hj⟩:=yard_picked x; rw [hj]; exact Finset.single_le_sum (s:=Finset.univ) (f:=fun i:Axis=>(x i).natAbs) (fun _ _=>Nat.zero_le _) (Finset.mem_univ j)
lemma size_yard (x : Cover): size x ≤ 4*yard x := (Finset.sum_le_sum (fun i (_:i∈(Finset.univ (α:=Axis)))=> yard_upper x i)).trans (le_of_eq (by simp [Axis]))
-- individual layers depend only on their grade's forward row (constant lattice offsets), coefficients even available off-shell
lemma piece_eq (i : ℕ) (p q : Cover→E) (h : ∀ l : List Axis,l.length=i → combine l p 0=combine l q 0) : Newt.piece i p=Newt.piece i q := by
  induction i generalizing p q with
  | zero=> funext x; exact h [] rfl
  | succ i ih=>
    funext x; rw [Newt.piece,Newt.piece]; apply congrArg _; apply Finset.sum_congr rfl; intro a _
    have he : Newt.piece i (up a p)=Newt.piece i (up a q) := by
      apply ih; intro l hl; rw [combine_up,combine_up]; exact h (a::l) (by rw [List.length_cons,hl])
    exact congrArg (fun g:E4→E=> x a • g (x-basis a)) he
lemma loft_test {k : ℕ} {p q : Loft E k} (h : ∀ l:List Axis,l.length≤k → combine l p.val 0=combine l q.val 0) : p=q := by
  apply Subtype.ext; funext x
  have he t (ht:t≤k) := piece_eq t p.val q.val (fun l hl=> h l (hl ▸ ht))
  have hv (p:Loft E k): p.val x= ∑ i ∈ Finset.range (k+1), Newt.piece i p.val (Pattern.xyz x) := sub_eq_zero.mp (congrFun (loft_tail p.property) x)
  rw [hv p,hv q]; exact Finset.sum_congr rfl fun i hi=> congrFun (he i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))) _
abbrev Trad (k : ℕ) := Σ i: Fin (k+1), Fin i.val→ Axis
def triumph (k : ℕ) (t : Trad k) : Loft E k →ₗ[ℝ] E where
  toFun p:= combine (List.ofFn t.2) p.val 0
  map_add' p q:= congrFun (combine_add (List.ofFn t.2) p.val q.val) _
  map_smul' a p:= congrFun (combine_smul a (List.ofFn t.2) p.val) _
lemma lists (D : List Axis) (h:D.length≤d) : ∃ t:Trad d,List.ofFn t.2=D := ⟨⟨⟨D.length, h.trans_lt (by omega)⟩,D.get⟩,List.ofFn_get D⟩
instance [FiniteDimensional ℝ E] (k : ℕ) : FiniteDimensional ℝ (Loft E k) := FiniteDimensional.of_injective (LinearMap.pi (triumph k)) (fun p q h=> loft_test (fun D hD=>by obtain ⟨t,rfl⟩ := (show ∃ t:Trad k,D=List.ofFn t.2 from by obtain ⟨t,e⟩:= lists D hD; exact ⟨t,e.symm⟩); exact congrFun h t))
end YM.RG11.FirstW
