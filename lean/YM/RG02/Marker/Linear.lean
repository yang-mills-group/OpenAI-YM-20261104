import YM.RG02.Marker.Partition

/-!
Multilinearity accounting by column (including finite sums of line
or vertex presentations). Valid even with new exclusions; irrelevant
variables outside this mode can still be held unchanged. There is no
information here about changes of coordinate basis for *error estimates*.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG02.Marks
open Filter Marker Multi Extra.Trajectories Finset
open scoped BigOperators Classical
variable {ι K : Type} [DecidableEq ι] [Fintype ι] {R : Census ι}

theorem piece {x : Poly R} (hx : x.part R.quiet=1)(S : Finset K)(y : K → Poly R)
    (hy : ∀ i∈S,(y i).part R.quiet=1)(i : ι)(s : R.Mode)(hi : i ∈ s.val)
    (ha : ∀ v : R.Mode, v.val⊆s.val → i∈v.val → x.part v=∑ k∈S,(y k).part v)
    (hb : ∀ v : R.Mode,v.val⊆s.val → i∉v.val → ∀ k∈S,(y k).part v=x.part v) :
    (connected x).part s=∑ k∈S,(connected (y k)).part s := by
   let z : Multi.Hot R := ⟨s,⟨i,hi⟩⟩
   have he (p : (parts R).Mode) (hp : p∈ shards R s) :
       (∏ v∈p.val,x.part v.val) = ∑ k∈S,∏ v∈p.val,(y k).part v.val := by
      let H (k:K)(s:Multi.Hot R) := (y k).part s.val
      let h (s: Multi.Hot R) := x.part s.val
      have hu : p.val.biUnion Multi.Hot.sites = s.val := congr_arg Subtype.val ((chooses ..).mp hp)
      obtain ⟨a,ha',hh⟩ := mem_biUnion.mp (hu.symm ▸ hi : i ∈ _)
      have hT (v) (hv:v∈p.val) : v.val.val⊆s.val := fun _ ht => hu ▸ mem_biUnion.mpr ⟨v,hv,ht⟩
      change ∏ v ∈ p.val,h v= _
      calc
         _ = (∑ k ∈ S, H k a) * ∏ v∈p.val.erase a,h v := by rw [← show h a =∑ k∈S,H k a from ha a.val (hT a ha') hh, Finset.mul_prod_erase _ h ha']
         _ = _ := by
           rw [sum_mul]; apply sum_congr rfl; intro k hk
           have hz : ∏ v∈p.val.erase a,h v=∏ v∈p.val.erase a,H k v:= by
              symm; apply prod_congr rfl; intro v hv
              obtain ⟨hne,h'⟩ := mem_erase.mp hv
              exact hb v.val (hT v h') (fun HL => disjoint_left.mp (parts_wise p h' ha' hne) HL hh) k hk
           rw [hz, Finset.mul_prod_erase _ (H k) ha']
   rw [show s=z.val from rfl,cumulant_partition hx]
   trans ∑ k∈S, ∑ p∈shards R z.val,
        (-1:ℂ)^(p.val.card-1) * ((p.val.card-1).factorial : ℂ)* ∏ b∈p.val,(y k).part b.val
   · rw [sum_comm (s:=S)]; refine sum_congr rfl fun p hp => ?_; rw [he p hp,mul_sum]
   exact (sum_congr rfl fun k hk => cumulant_partition (hy k hk) z).symm

omit [Fintype ι] in
/-- Multilinear decompositions iterate over the **active** subalphabet
of a specific cumulant. General lemma on such columns, with spectators fixed.
`K` may differ across columns. Sum here is over choosing pieces for each
coordinate (no multiplicative ambiguity/copy convention). -/
theorem picked {D M : ι → Type} [∀ i,Fintype (M i)]
    (s : Finset ι)(v : (i : ι) → D i)(u : ∀ i,M i→ D i)
    (f : ((i : ι)→ D i)→ ℂ)
    (hp : ∀ i∈s,∀ x, f (Function.update x i (v i))=∑ j:M i, f (Function.update x i (u i j))) :
    f v = ∑ z : ∀ i : ↥s, M i, f fun i => if H : i∈s then u i (z ⟨i,H⟩) else v i := by
  -- auxiliary replacing values on any given subset
  have h : ∀ (t : Finset ι), t⊆s→ ∀ x, (∀ i∈t, x i=v i) →
      f x = ∑ z : ∀ i : ↥t,M i, f fun i => if H : i∈t then u i (z ⟨i,H⟩) else x i := by
    intro t; induction t using Finset.induction with
    | empty => intro _ x _; simp
    | insert i t hi ih =>
      intro HT x hx
      have hi' : i ∈ insert i t := Finset.mem_insert_self i t
      let A := fun j : M i => Function.update x i (u i j)
      let g j (z : ∀ a : ↥t,M a) (b:ι) := if H : b∈t then u b (z ⟨b,H⟩) else A j b
      let Q := ∀ z : ↥(insert i t),M (↑z)
      let E : Q ≃ M i × (∀ a : ↥t,M a) := {
        toFun := fun r => (r ⟨i,hi'⟩, fun a => r ⟨a, Finset.mem_insert_of_mem a.property⟩)
        invFun := fun ⟨b,k⟩ a => if h : a.val=i then h.symm ▸ b else k ⟨a, (mem_insert.mp a.property).resolve_left h⟩
        left_inv := by
          intro r; ext ⟨a,h⟩; dsimp only
          by_cases ha:a=i
          · subst a; rw [dif_pos rfl]
          rw [dif_neg ha]
        right_inv := by
          rintro ⟨j,q⟩; apply Prod.ext
          · change (if h:i=i then _ else _)=j; rw [dif_pos rfl]
          ext ⟨a,H⟩; dsimp only; rw [dif_neg (ne_of_mem_of_not_mem H hi)] }
      calc
        _ = ∑ j:M i, f (A j) := by
          conv_lhs => arg 1; rw [show x=Function.update x i (v i) by rw [← hx i hi', Function.update_eq_self]]
          exact hp i (HT hi') _
        _ = ∑ z : Q, f (g (E z).1 (E z).2) := by
          rw [Equiv.sum_comp E (fun q => f (g q.1 q.2)), Fintype.sum_prod_type]; apply sum_congr rfl
          intro a _; apply ih (Subset.trans (subset_insert i t) HT) (A a)
          intro j hj; unfold A; rw [Function.update_of_ne (ne_of_mem_of_not_mem hj hi)]; exact hx j (mem_insert_of_mem hj)
        _ = _ := by
          apply sum_congr rfl; intro j _; congr 1
          funext q; by_cases hh : q ∈ t
          · simp only [mem_insert_of_mem (b:=i) hh,↓reduceDIte, g,hh,E,Equiv.coe_fn_mk]
          by_cases hh' : q=i
          · subst q; simp [g,A,hi,E]
          simp only [g,mem_insert,hh',hh,A,↓reduceDIte,or_self]
          rw [Function.update_of_ne hh']
  exact h _ Finset.Subset.rfl _ (fun i _ => rfl)
end YM.RG02.Marks
