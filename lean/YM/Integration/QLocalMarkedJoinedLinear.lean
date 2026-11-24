import YM.Integration.QLocalCompulsoryJoinedTape

/-! One physical marker sector is square zero. It can therefore be
inserted into every admissible packet by replacing exactly one joined
compulsory row, even when other rows have pre-existing nonquiet marks. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QLocalMarkedJoinedLinear
open Function Finset Lattice RG Wilson Marker Overlay Extra.Trajectories Extra.Histories Planned.GuardedAtom
open QLocalMarkedJoinedCofactor QLocalMarkedJoinedSeries ActualWilsonTaylorSlot
open scoped Classical BigOperators

theorem linear {ι α:Type*} [DecidableEq ι] [CommSemiring α] (b:Finset ι) (v k:ι→α)
    (zero:∀i j,k i*k j=0) :
    (∏i∈b,(v i+k i))=(∏i∈b,v i)+∑i∈b,k i*∏j∈b.erase i,v j := by
  induction b using Finset.induction with
  | empty=>simp
  | insert t b fresh ih=>
    have last:(∑i∈b,k i*∏j∈(insert t b).erase i,v j)=v t*(∑i∈b,k i*∏j∈b.erase i,v j):=by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.erase_insert_of_ne (ne_of_mem_of_not_mem hi fresh).symm,
        Finset.prod_insert (fun h=>fresh (Finset.mem_of_mem_erase h))]
      ring
    have vanish:k t*(∑i∈b,k i*∏j∈b.erase i,v j)=0:=by
      rw [Finset.mul_sum]
      exact Finset.sum_eq_zero (fun i _=>by rw [←mul_assoc,zero,zero_mul])
    rw [Finset.prod_insert fresh,Finset.prod_insert fresh,Finset.sum_insert fresh,Finset.erase_insert fresh,
      ih,last,add_mul,mul_add,mul_add,vanish]
    ring

variable {G:Gauge} {n:Side} {W:Rep G n} {Y:ℕ→Support n} {V:Type} [DecidableEq V] [Fintype V]
    {Γ:Census V}

theorem square {V:Type} [DecidableEq V] [Fintype V] {Γ:Census V} (s:Γ.Mode) (hs:s≠Γ.quiet) (a b:ℂ) : Poly.send s a*Poly.send s b=0 := by
  by_contra hn
  obtain ⟨t,h⟩:=merges_of_tagged_mul hn
  obtain ⟨v,hv⟩:=Finset.nonempty_iff_ne_empty.mpr (fun e=>hs (Subtype.ext e))
  exact Finset.disjoint_left.mp h.1 hv hv

def addition (K:Guard.Keeper W.p W.activities) (a:Bands Γ W) (s:Γ.Mode)
    (f:ℕ→ Config G n→ℂ) (i:ℕ) (U:Config G n) : Poly Γ :=
  placed (Y:=Y) K (fun l=>a.each l U) (fun r=>Poly.send s (f r U)) U i

theorem silence {G:Gauge} {n:Side} {W:Rep G n} {Y:ℕ→Support n} {V:Type} [DecidableEq V] [Fintype V] {Γ:Census V} (K:Guard.Keeper W.p W.activities) (a:Bands Γ W) (s:Γ.Mode) (hs:s≠Γ.quiet)
    (f:ℕ→ Config G n→ℂ) (i:ℕ) (U:Config G n) : (addition (Y:=Y) K a s f i U).part Γ.quiet=0 := by
  by_cases present:i∈Set.range (address (Y:=Y) K)
  · obtain ⟨z,rfl⟩:=present
    rw [addition,QLocalMarkedJoinedCofactor.on_slot,QLocalMarkedJoinedCofactor.deposit]
    split <;> simp [hs.symm]
  · rw [addition,escaped _ _ _ _ _ present]; rfl

theorem square_rows (K:Guard.Keeper W.p W.activities) (a:Bands Γ W) (s:Γ.Mode) (hs:s≠Γ.quiet)
    (f:ℕ→ Config G n→ℂ) (i j:ℕ) (U:Config G n) :
    addition (Y:=Y) K a s f i U*addition (Y:=Y) K a s f j U=0 := by
  by_cases first:i∈Set.range (address (Y:=Y) K)
  · by_cases second:j∈Set.range (address (Y:=Y) K)
    · obtain ⟨z,rfl⟩:=first; obtain ⟨t,rfl⟩:=second
      unfold addition
      rw [QLocalMarkedJoinedCofactor.on_slot,QLocalMarkedJoinedCofactor.on_slot]
      by_cases hz:gate z U <;> by_cases ht:gate t U <;>
        simp only [QLocalMarkedJoinedCofactor.deposit,hz,ht,if_true,if_false,mul_zero,zero_mul]
      rw [mul_mul_mul_comm,square s hs,zero_mul]
    · change _*placed (Y:=Y) K _ _ U j=0
      rw [escaped _ _ _ _ _ second,mul_zero]
  · change placed (Y:=Y) K _ _ U i*_=0
    rw [escaped _ _ _ _ _ first,zero_mul]

theorem packet {G:Gauge} {n:Side} {W:Rep G n} {V:Type} [DecidableEq V] [Fintype V] {Γ:Census V} {a b:Bands Γ W} (k:ℕ→ Config G n→Poly Γ) (U:Config G n) (I:Finset ℕ)
    (each:∀i,b.each i U=a.each i U+k i U) (nil:∀i j,k i U*k j U=0) :
    b.packet I U=a.packet I U + ∑i∈I,k i U*coat W (fun j=>a.each j U) i I U := by
  by_cases ad:W.activities.admissible W.p U I
  · unfold Bands.packet
    simp only [if_pos ad,each]
    rw [linear I _ _ nil]
    congr 1
    exact Finset.sum_congr rfl (fun i hi=>by simp [QLocalMarkedJoinedCofactor.coat,hi,ad])
  · simp [Bands.packet,QLocalMarkedJoinedCofactor.coat,ad]

end YM.Integration.QLocalMarkedJoinedLinear
