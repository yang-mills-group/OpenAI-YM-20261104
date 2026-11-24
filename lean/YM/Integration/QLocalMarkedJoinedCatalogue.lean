import YM.Integration.QLocalMarkedJoinedRelease

/-! All finite mixed sectors on one actual compulsory register. The
registration precedes independent tests and field configurations. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QLocalMarkedJoinedCatalogue
open Function Finset Lattice RG Wilson Marker Overlay Extra.Trajectories Extra.Histories Planned.GuardedAtom
open RG3.Script.Picnic LocalComparison WilsonLimitConstruction.FundedMarkedFieldSplit
open QLocalMarkedJoinedLinear QLocalCompulsoryJoinedTape
open scoped Classical BigOperators
variable {G:Gauge} {n:Side} {W:Rep G n} {Y:ℕ→Support n} {V X:Type} [DecidableEq V] [Fintype V]
    {Γ:Census V} {o:V→Site n}

structure Source (Y:ℕ→Support n) (d:X→ Config G n→Poly Γ) where
  field : Γ.Mode→X→ℕ→ Config G n→ℂ
  dirty s x r U : field s x r U≠0→¬Healthy W.p.threshold (Y r) U
  purchase s x U : HasSum (fun r=>field s x r U) ((d x U).part s)

def unit (T:Taste X o W Γ) : Compulsory X Γ G n:=⟨T.menu.marks,T.menu.force⟩

def Financed (a:Bands Γ W) : Prop:=
  (∀i U,Summable (fun j=>a.tagged i j U)) ∧ ∀U,Summable (fun b=>a.packet b U)

theorem finite (K:Guard.Keeper W.p W.activities) (T:Taste X o W Γ) {d:X→ Config G n→Poly Γ}
    (F:Source (W:=W) Y d) (S:Finset Γ.Mode) (warm:∀s∈S,s≠Γ.quiet)
    (P:Bands Γ W→Prop) (funds:∀x,P (T.menu.terms x) ∧ Financed (T.menu.terms x))
    (step:∀(a:Bands Γ W) (s:Γ.Mode),s≠Γ.quiet→ ∀x,
      P a→P (bands a (addition (Y:=Y) K a s (F.field s x)))) :
    ∃H:Compulsory X Γ G n,∀x,
      P (((replace T H).menu).terms x) ∧ Financed (((replace T H).menu).terms x) ∧
      ∀U,((replace T H).menu.terms x).cluster U=
        Poly.pass (∑s∈S,Poly.send s ((d x U).part s))*(T.menu.terms x).cluster U := by
  induction S using Finset.induction with
  | empty=> exact ⟨unit T,fun x=>⟨(funds x).1,(funds x).2,fun U=>by simp [unit,replace]⟩⟩
  | insert s S new ih=>
    have active:s≠Γ.quiet:=warm s (Finset.mem_insert_self ..)
    have rem:∀j∈S,j≠Γ.quiet:=fun j h=>warm j (Finset.mem_insert_of_mem h)
    obtain ⟨A,paid⟩:=ih rem
    let old:=replace T A
    let fresh x:=addition (Y:=Y) K (old.menu.terms x) s (F.field s x)
    refine ⟨tape old fresh,?_⟩
    intro x
    let a:=old.menu.terms x
    let b:=bands a (fresh x)
    have prior:=paid x
    have cert (U:Config G n):Summable (fun l=>b.packet l U) ∧
        b.cluster U=Poly.pass (Poly.send s ((d x U).part s))*a.cluster U:=by
      have h:=QLocalMarkedJoinedRelease.issued K a s active (F.field s x) U
        (fun r=>F.dirty s x r U) (F.purchase s x U).summable
        (fun i=>prior.2.1.1 i U) (prior.2.1.2 U)
      simpa only [(F.purchase s x U).tsum_eq] using h
    refine ⟨step a s active x prior.1,⟨fun i U=>QLocalCompulsoryJoinedTape.tagged a (fresh x) i U
       (prior.2.1.1 i U),fun U=>(cert U).1⟩,?_⟩
    intro U
    change b.cluster U=_
    rw [(cert U).2,prior.2.2 U,Finset.sum_insert new,
      pass_add (by simp [active.symm]) (by simp [Poly.part_sum,show Γ.quiet∉S from fun h=>(rem _ h) rfl]),
      mul_assoc]

theorem issued (K:Guard.Keeper W.p W.activities) (T:Taste X o W Γ) {d:X→ Config G n→Poly Γ}
    (F:Source (W:=W) Y d) (silent:∀x U,(d x U).part Γ.quiet=0) (P:Bands Γ W→Prop)
    (funds:∀x,P (T.menu.terms x) ∧ Financed (T.menu.terms x))
    (step:∀(a:Bands Γ W) (s:Γ.Mode),s≠Γ.quiet→ ∀x,
      P a→P (bands a (addition (Y:=Y) K a s (F.field s x)))) :
    ∃H:Compulsory X Γ G n,∀x,
      P ((replace T H).menu.terms x) ∧ Financed ((replace T H).menu.terms x) ∧
      ∀U,((replace T H).leaf x).contents.cluster U=Poly.pass (d x U)*(T.leaf x).contents.cluster U ∧
        ((replace T H).leaf x).density U=Poly.pass (d x U)*(T.leaf x).density U := by
  let S:Finset Γ.Mode:=Finset.univ.erase Γ.quiet
  have warm:∀s∈S,s≠Γ.quiet:=fun _ h=>(Finset.mem_erase.mp h).1
  obtain ⟨H,pa⟩:=finite K T F S warm P funds step
  refine ⟨H,fun x=>⟨(pa x).1,(pa x).2.1,fun U=>?_⟩⟩
  have restore:(∑s∈S,Poly.send s ((d x U).part s))=d x U:=by
    have sum:=Poly.studs (d x U)
    rw [←Finset.add_sum_erase _ _ (Finset.mem_univ Γ.quiet)] at sum
    simpa [S,silent] using sum
  have complete:=((pa x).2.2 U).trans (congrArg (fun v=>Poly.pass v*(T.leaf x).contents.cluster U) restore)
  exact ⟨complete,cluster_density T H x U _ complete⟩

end YM.Integration.QLocalMarkedJoinedCatalogue
