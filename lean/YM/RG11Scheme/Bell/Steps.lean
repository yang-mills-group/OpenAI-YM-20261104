import YM.RG11Scheme.Stencil.Loom

/-! Finite Newton jets. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG11Scheme.Bell
open Function Set Filter Lattice Mesh Stencil Stencil.Point Stencil.Shot
open scoped BigOperators Classical Topology
variable {E F Y:Type} {p q:ℕ} {D A B:List Axis}

def taxi (x:Cover):ℕ := ∑ i:Axis,(x i).natAbs
lemma taxi_bound x : taxi x≤4*elev x := by unfold taxi; grw [show ∀ i:Axis, (x i).natAbs≤elev x from fun i=>cardinal_big i x]; simp [Axis]
private lemma taxis {x y:Cover}{i:Axis}(h:(y i).natAbs+1=(x i).natAbs) (ht:∀ j,j≠i→x j=y j): taxi y+1=taxi x ∧ elev y≤elev x := by
   constructor
   · unfold taxi; rw [← Finset.sum_erase_add _ _ (a:=i) (Finset.mem_univ i), ← Finset.sum_erase_add (s:=Finset.univ) (f:=fun k:Axis=>(x k).natAbs) (Finset.mem_univ i), add_assoc,h]; congr 1; exact Finset.sum_congr rfl (fun j hj=>congrArg Int.natAbs ((ht j (Finset.ne_of_mem_erase hj)).symm))
   refine Finset.sup_le (fun j _=>?_)
   by_cases hj:j=i; · rw [hj]; have he := cardinal_big i x; omega
   rw [← ht _ hj]; exact cardinal_big j x
lemma descends (x:Cover)(h:x≠0): ∃ i y,(x=y+step i ∨ y=x+step i) ∧ taxi y+1=taxi x ∧ elev y≤elev x := by
   obtain ⟨i,hi⟩:= Function.ne_iff.mp h
   change x i ≠ 0 at hi
   rcases lt_or_gt_of_ne hi with w|w
   · refine ⟨i,x+step i,Or.inr rfl,taxis (i:=i) ?_ ?_⟩
     · simp only [Pi.add_apply, step_apply,if_true]; omega
     exact fun j hj=> by simp [hj]
   refine ⟨i,x-step i, Or.inl (sub_add_cancel ..).symm,taxis (i:=i) ?_ ?_⟩
   · simp only [Pi.sub_apply,step_apply, if_true];omega
   exact fun j hj=> by simp [hj]
lemma taxi_rule {P:Cover→Prop} (h:P 0) (hp:∀ (x y:Cover)(i:Axis),P y → elev y≤elev x → taxi x=taxi y+1 → (x=y+step i∨ y=x+step i) →P x) (x:Cover): P x := by
    generalize he: taxi x=u
    induction u using Nat.strong_induction_on generalizing x with
    | h u IH=> by_cases ht:x=0; · rwa [ht]
               obtain ⟨i,y,H,h',hh⟩:=descends x ht; exact hp x y i (IH _ (by omega : taxi y<u) _ rfl) hh h'.symm H
section alg
variable [AddCommGroup E]
lemma shuffle (D S:List Axis)(f:Cover→ E) (h:D.Perm S) : go D f=go S f := by
   induction h with
   | nil=>rfl
   | cons c h ih=>funext x;rw [onwards,onwards,ih]
   | swap a b l=>funext x; simp only [onwards];rw [add_right_comm x];abel
   | trans _ _ ih IH=>exact ih.trans IH
lemma climbed (x:E)(D:List Axis)(hx: 0<D.length) : go D (fun _:Cover=>x)=0 := by
   induction D using List.reverseRecOn with
   | nil=>simp at hx
   | append_singleton D d _ =>
       funext y; rw [go_concat, show go [d] _= 0 from funext (fun (y:Cover)=> by show x-x=(0:E); rw [sub_self])]; exact dark ..
lemma shared {f:Cover→ E}(h:∀ i:Axis,go [i] f=0) : ∀ x, f x=f 0 := taxi_rule (P:=fun x=>f x=f 0) rfl (fun x y i e _ _ H=> by
    rw [←e]; rcases H with H|H
    · exact H ▸ (sub_eq_zero.mp (congrFun (h i) y))
    subst y; exact (sub_eq_zero.mp (congrFun (h i) x)).symm)
end alg

variable [AddCommGroup E][Module ℝ E]
-- space of literal polys
def ladder (D:List Axis) : (Cover→ E) →ₗ[ℝ] (Cover→ E) where
   toFun := go D
   map_add' X Y := funext (plus_go X Y D)
   map_smul' c X := by
       funext x
       have he:= go_map ((c • LinearMap.id : E→ₗ[ℝ]E).toAddMonoidHom) X D x
       simp only [show ∀ y:E,(c • LinearMap.id : E→ₗ[ℝ]E).toAddMonoidHom y = c • y from fun y=> rfl] at he
       exact he

variable (E) in
def hill (d: ℕ) : Submodule ℝ (Cover → E) where
   carrier := {f|∀ D:List Axis,d<D.length→ go D f=0}
   zero_mem' D _:= funext fun p=>dark ..
   add_mem' hq hh D hd := by rw [show go D= ladder (E:=E) D from rfl]; rw [map_add]; exact Eq.trans (congrArg₂ (·+·) (hq D hd) (hh D hd)) (zero_add 0)
   smul_mem' a f hf D hd := by change ladder D (a • f)=_; rw [map_smul,show ladder D f=0 from hf D hd, smul_zero]
lemma hills (h:p≤q) : hill E p ≤ hill E q:= fun _ hh D hd=> hh D (by omega)
variable {f:Cover→ E}
lemma hill_const_iff : f∈hill E 0 ↔ ∀ x,f x=f 0 := ⟨fun h=> shared (fun i=>h [i] (by simp)),fun h D hd=> by
   rw [show f=(fun _=>f 0) from funext h];exact climbed _ _ hd⟩
lemma hill_single (h:∀ i:Axis,go [i] f∈hill E p) : f ∈ hill E (p+1) := by
   intro D hd; cases D using List.reverseRecOn with
   | nil=> simp at hd
   | append_singleton a b _=> rw [show go (a++[b]) f=go a (go [b] f) from funext fun x=> go_concat ..]; exact h b a (by simpa using hd)
lemma sliced_at (A:List Axis) (h:f∈hill E p): go A f∈hill E (p-A.length) := fun D hd=> by rw [← show go (D++A) f=go D (go A f) from funext fun x=> go_concat ..]; apply h; rw [List.length_append]; omega
lemma sliced (h:f∈hill E (p+1))(i:Axis): go [i] f∈hill E p := by simpa only [List.length_singleton,Nat.add_sub_cancel] using sliced_at [i] h
lemma lower_iff (h : f∈hill E (p+1)): f∈hill E p ↔ ∀ D:List Axis,D.length=p+1 → go D f 0=0 := by
    refine ⟨fun ht D he=> by rw [ht D (by omega)];rfl,?_⟩
    intro H D hd; by_cases e:D.length=p+1
    · have ht : go D f∈hill E 0:= by simpa [e] using sliced_at D h
      exact funext (fun x=> (hill_const_iff.mp ht x).trans (H D e))
    exact h D (by omega)
lemma hill_readout {f:Cover→ E} (h:f∈hill E p): f=0 ↔ ∀ D:List Axis,D.length≤p→ go D f 0=0 := by
    constructor
    · rintro rfl; exact fun D _=>dark ..
    intro H; induction p with
    | zero => exact funext fun x=> (hill_const_iff.mp h x).trans (H [] (by simp))
    | succ q IH=> exact IH ((lower_iff h).2 (fun D h=>H D h.le)) (fun D hd=>H D (hd.trans (Nat.le_succ q)))
lemma rise_cut (x:Cover) (h:f∈hill E p) : (fun y=>f (y+x))∈hill E p := fun D hd=>funext fun y=> (shifted D _ _ y).trans (congrFun (h D hd) _)
lemma hill_round (n:ℕ)(x:E) : (fun _:Cover=>x)∈hill E n:= hills (Nat.zero_le n) (hill_const_iff.mpr fun _=>rfl)
end YM.RG11Scheme.Bell
