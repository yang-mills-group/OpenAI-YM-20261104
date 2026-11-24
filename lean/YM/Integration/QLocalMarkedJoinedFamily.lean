import YM.Integration.QLocalMarkedJoinedCatalogue

/-! Keep invoices on whole test families while the authentic compulsory
bank is enlarged finitely. Each stage uses the same updated tape for its
cluster, admissible rows, and quantitative accounts. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QLocalMarkedJoinedFamily
open Function Finset Lattice RG Wilson Marker Overlay Extra.Histories Planned.GuardedAtom
open RG3.Script.Picnic QLocalCompulsoryJoinedTape QLocalMarkedJoinedLinear QLocalMarkedJoinedCatalogue
open WilsonLimitConstruction.FundedMarkedFieldSplit Extra.Trajectories
open scoped BigOperators Classical
variable {G:Gauge} {n:Side} {W:Rep G n} {X V:Type} [DecidableEq V] [Fintype V] {Γ:Census V}
    {o:V→Site n} {Y:ℕ→Support n}

theorem finite (K:Guard.Keeper W.p W.activities) (T:Taste X o W Γ) {d:X→ Config G n→Poly Γ}
    (F:Source (W:=W) Y d) (S:Finset Γ.Mode) (warm:∀s∈S,s≠Γ.quiet)
    (Good:(X→Bands Γ W)→ℕ→Prop) (start:Good T.menu.terms 0) (funds:∀x,Financed (T.menu.terms x))
    (step:∀(A:X→Bands Γ W) (j:ℕ),j<Fintype.card Γ.Mode→
      Good A j→(∀x,Financed (A x))→∀s:Γ.Mode,s≠Γ.quiet→
      Good (fun x=>bands (A x) (addition (Y:=Y) K (A x) s (F.field s x))) (j+1)) :
    ∃H:Compulsory X Γ G n,Good (replace T H).menu.terms S.card ∧ ∀x,
      Financed ((replace T H).menu.terms x) ∧ ∀U,((replace T H).menu.terms x).cluster U=
        Poly.pass (∑s∈S,Poly.send s ((d x U).part s))*(T.menu.terms x).cluster U := by
  induction S using Finset.induction with
  | empty=>exact ⟨unit T,start,fun x=>⟨funds x,fun U=>by simp [unit,replace]⟩⟩
  | insert s S new ih=>
    have active:s≠Γ.quiet:=warm s (Finset.mem_insert_self ..)
    have rem:∀j∈S,j≠Γ.quiet:=fun j h=>warm j (Finset.mem_insert_of_mem h)
    obtain ⟨H,income,paid⟩:=ih rem
    let old:=replace T H
    let fresh x:=addition (Y:=Y) K (old.menu.terms x) s (F.field s x)
    have size:S.card<Fintype.card Γ.Mode:=by
      have h:=Finset.card_le_univ (insert s S)
      rw [Finset.card_insert_of_notMem new] at h
      omega
    refine ⟨tape old fresh,?_,?_⟩
    · rw [Finset.card_insert_of_notMem new]
      exact step old.menu.terms S.card size income (fun x=>(paid x).1) s active
    intro x
    let a:=old.menu.terms x
    let b:=bands a (fresh x)
    have cert (U:Config G n):Summable (fun l=>b.packet l U) ∧
        b.cluster U=Poly.pass (Poly.send s ((d x U).part s))*a.cluster U:=by
      have h:=QLocalMarkedJoinedRelease.issued K a s active (F.field s x) U
        (fun r=>F.dirty s x r U) (F.purchase s x U).summable
        (fun i=>(paid x).1.1 i U) ((paid x).1.2 U)
      simpa only [(F.purchase s x U).tsum_eq] using h
    refine ⟨⟨fun i U=>QLocalCompulsoryJoinedTape.tagged a (fresh x) i U
       ((paid x).1.1 i U),fun U=>(cert U).1⟩,?_⟩
    intro U
    change b.cluster U=_
    rw [(cert U).2,(paid x).2 U,Finset.sum_insert new,
      pass_add (by simp [active.symm]) (by simp [Poly.part_sum,show Γ.quiet∉S from fun h=>(rem _ h) rfl]),mul_assoc]

theorem issued (K:Guard.Keeper W.p W.activities) (T:Taste X o W Γ) {d:X→ Config G n→Poly Γ}
    (F:Source (W:=W) Y d) (silent:∀x U,(d x U).part Γ.quiet=0)
    (Good:(X→Bands Γ W)→ℕ→Prop) (start:Good T.menu.terms 0) (funds:∀x,Financed (T.menu.terms x))
    (step:∀(A:X→Bands Γ W) (j:ℕ),j<Fintype.card Γ.Mode→
      Good A j→(∀x,Financed (A x))→∀s:Γ.Mode,s≠Γ.quiet→
      Good (fun x=>bands (A x) (addition (Y:=Y) K (A x) s (F.field s x))) (j+1)) :
    ∃H:Compulsory X Γ G n,Good (replace T H).menu.terms (Finset.univ.erase Γ.quiet).card ∧ ∀x,
      Financed ((replace T H).menu.terms x) ∧ ∀U,
      ((replace T H).leaf x).contents.cluster U=Poly.pass (d x U)*(T.leaf x).contents.cluster U ∧
      ((replace T H).leaf x).density U=Poly.pass (d x U)*(T.leaf x).density U := by
  let S:=Finset.univ.erase Γ.quiet
  obtain ⟨A,hA,pa⟩:=finite K T F S (fun s hs=>(Finset.mem_erase.mp hs).1) Good start funds step
  refine ⟨A,hA,fun x=>⟨(pa x).1,fun U=>?_⟩⟩
  have restore:(∑s∈S,Poly.send s ((d x U).part s))=d x U:=by
    have all:=Poly.studs (d x U)
    rw [←Finset.add_sum_erase _ _ (Finset.mem_univ Γ.quiet)] at all
    simpa [S,silent] using all
  have full:=((pa x).2 U).trans (congrArg (fun v=>Poly.pass v*(T.leaf x).contents.cluster U) restore)
  exact ⟨full,cluster_density T A x U _ full⟩

end YM.Integration.QLocalMarkedJoinedFamily
