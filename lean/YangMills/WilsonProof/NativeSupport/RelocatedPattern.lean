import YangMills.WilsonProof.NativeSupport.TorusCopies

/-! A collision between projected physical slot locations costs at most
one coarse displacement per slot. This is independent of their separation. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.InletSusceptibility.Packet
open Function Finset Lattice RG Wilson RGComparison.Core16
open scoped Classical BigOperators
variable {n c : Side}

def scale {n : Side} : {c : Side} → Descent n c → ℕ
  | _, .nil => 1
  | _, .push S _ d => S.ratio.count.val * scale d

theorem side_scale (d : Descent n c) : c.val*scale d = n.val := by
  induction d with
  | nil => simp [scale]
  | push S T d ih =>
    rw [scale,←Nat.mul_assoc,←S.ratio.exact_size,ih]

private theorem one_lift (r : Ratio c n) (y : Site c) :
    pdist (r.embed y) ≤ r.count.val*pdist y := by
  refine Finset.sup_le fun i _=>?_
  rw [r.lift_embed]
  simpa [Int.natAbs_mul] using Nat.mul_le_mul_left r.count.val (component_le y i)

theorem lift_distance (d : Descent n c) (y : Site c) :
    pdist (liftSite d y) ≤ scale d*pdist y := by
  induction d with
  | nil => simp [liftSite,scale]
  | push S T d ih =>
    exact (ih (S.ratio.embed y)).trans ((Nat.mul_le_mul_left _ (one_lift S.ratio y)).trans_eq
      (by simp only [scale]; ac_rfl))

private theorem distinct_choices {V : Type*} [Fintype V] (o : V→Site n)
    (D : Finset (Site n)) (hD : Fintype.card V ≤ D.card) :
    ∃ f : V→Site n, (∀ i,f i∈D) ∧ Injective (fun i=>f i+o i) := by
  have pick (S : Finset V) : ∃ f : V→Site n, (∀ i∈S,f i∈D) ∧
      Set.InjOn (fun i=>f i+o i) S := by
    induction S using Finset.induction_on with
    | empty => exact ⟨fun _=>0,by simp,by simp⟩
    | @insert i S hi ih =>
      obtain ⟨f,good,inj⟩:=ih
      let taken := S.image fun j=>f j+o j
      have small : taken.card<D.card := card_image_le.trans_lt
        ((card_lt_card (ssubset_insert hi)).trans_le ((card_le_univ _).trans hD))
      have fresh : ∃ b∈D,b+o i∉taken := by
        by_contra! all
        have sub : (D.image (fun b=>b+o i))⊆taken := by
          intro y hy
          obtain ⟨b,hb,rfl⟩:=mem_image.mp hy
          exact all b hb
        have card := card_le_card sub
        rw [card_image_of_injective _ (fun _ _ e=>add_right_cancel e)] at card
        omega
      obtain ⟨b,hb,free⟩:=fresh
      refine ⟨update f i b,?_,?_⟩
      · intro j hj
        rcases mem_insert.mp hj with rfl|h
        · simpa using hb
        have hj : j≠i := fun e=>hi (e ▸ h)
        rw [update_of_ne hj]; exact good j h
      intro x hx y hy e
      by_cases ex : x=i
      · subst x
        by_contra ey
        have ys := (mem_insert.mp hy).resolve_left (Ne.symm ey)
        apply free
        have equal : b+o i=f y+o y := by simpa [update_of_ne (Ne.symm ey)] using e
        exact equal ▸ mem_image_of_mem _ ys
      by_cases ey : y=i
      · subst y
        have xs := (mem_insert.mp hx).resolve_left ex
        have equal : f x+o x=b+o i := by simpa [update_of_ne ex] using e
        exact False.elim (free (equal ▸ mem_image_of_mem _ xs))
      exact inj ((mem_insert.mp hx).resolve_left ex) ((mem_insert.mp hy).resolve_left ey)
        (by simpa [update_of_ne ex,update_of_ne ey] using e)
  obtain ⟨f,good,inj⟩:=pick univ
  exact ⟨f,fun i=>good i (mem_univ i),fun i j h=>inj (mem_univ i) (mem_univ j) h⟩

theorem nearby_distinct {V : Type*} [Fintype V] (o : V→Site n) (large : Fintype.card V ≤ n.val) :
    ∃ q : V→Site n, (∀ i,pdist (q i) ≤ Fintype.card V) ∧ Injective (fun i=>q i+o i) := by
  let moves (j : Fin (Fintype.card V)) := j.val • (Lattice.step 0 : Site n)
  have inject : Injective moves := by
    intro i j e
    apply Fin.ext
    have eq := congrFun e 0
    change (i.val • (Lattice.step 0 : Site n)) 0=(j.val • (Lattice.step 0 : Site n)) 0 at eq
    simp only [Pi.smul_apply,step_apply,nsmul_eq_mul] at eq
    have values := congrArg ZMod.val eq
    simpa [ZMod.val_natCast,Nat.mod_eq_of_lt (i.isLt.trans_le large),
      Nat.mod_eq_of_lt (j.isLt.trans_le large)] using values
  have walk (j : ℕ) : pdist (j • (Lattice.step 0 : Site n)) ≤ j := by
    induction j with
    | zero => simp [pdist,Lattice.lift]
    | succ j ih => rw [succ_nsmul]; exact (pdist_triangle ..).trans (Nat.add_le_add ih (pdist_step _))
  let D := univ.image moves
  have count : (Fintype.card V) ≤ D.card := by simp [D,card_image_of_injective _ inject]
  obtain ⟨q,inside,distinct⟩:=distinct_choices o D count
  refine ⟨q,fun i=>?_,distinct⟩
  obtain ⟨j,_,eq⟩:=mem_image.mp (inside i)
  exact eq ▸ (walk j.val).trans j.isLt.le

theorem distinct_fine {V : Type*} [Fintype V] (d : Descent n c) (o : V→Site n)
    (large : Fintype.card V ≤ c.val) :
    ∃ x : V→Site n, Injective (home d ∘ x) ∧
      ∀ i,separation (x i) (o i) ≤ scale d*Fintype.card V := by
  obtain ⟨q,cost,distinct⟩:=nearby_distinct (home d ∘ o) large
  refine ⟨fun i=>liftSite d (q i)+o i,?_,fun i=>?_⟩
  · intro i j e
    apply distinct
    simpa only [comp_apply,ancestor_move] using e
  change pdist (liftSite d (q i)+o i-o i) ≤ _
  rw [add_sub_cancel_right]
  exact (lift_distance d _).trans (Nat.mul_le_mul_left _ (cost i))

end YM.Integration.InletSusceptibility.Packet
