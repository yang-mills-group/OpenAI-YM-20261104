import YM.Integration.QLocalMarkedJoinedFamily
import YM.Integration.QLocalThermalJoinedSource
import YM.Integration.LocalComparisonSignedLinearity
import YM.RG3.Held.Typed

/-! The original signed, square-free product at a joined compulsory
address is multilinear in its declared external sources. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QLocalMarkedJoinedLetters

open Function Finset Lattice Wilson RG Marker Overlay RG3.Held RG3.Script.Picnic
open LocalComparison Planned.GuardedAtom ActualWilsonTaylorSlot ActualWilsonJoinedCofactor QLocalMarkedJoinedCofactor
open QLocalCompulsoryInventoryBank (roster mode)
open QLocalCompulsoryJoinedTape QLocalMarkedJoinedLinear QLocalMarkedJoinedCatalogue
open WilsonLimitConstruction.FundedMarkedFieldSplit
open scoped Classical BigOperators

variable {G:Gauge} {V:Type} [Fintype V] [DecidableEq V] {Γ:Census V} {n:Side} {Q:Rep G n}
    {D:V→ ComparisonDensity.Address.Orbit} {o:V→Site n} {Y:ℕ→Support n}

private theorem sent {V:Type} [Fintype V] [DecidableEq V] {Γ:Census V} {D:V→ ComparisonDensity.Address.Orbit} (s : Γ.Mode) (f : TestSpace D→ℂ) (h : Letter ℂ (fun v=>ComparisonDensity.Address.Orbit.Mood (D v)) s.val f) :
    Published (K:=ℂ) (fun v=>ComparisonDensity.Address.Orbit.Mood (D v)) (fun x=>Poly.send s (f x)) := by
  intro k
  by_cases same : k=s
  · subst k
    have value : (fun x=>(Poly.send s (f x)).part s)=f := by funext x;simp
    exact (congrArg (Letter ℂ (fun v=>ComparisonDensity.Address.Orbit.Mood (D v)) s.val) value).mpr h
  · have zero : (fun x=>(Poly.send s (f x)).part k)=0 := by
      funext x
      simp [Poly.part_send,same]
    exact (congrArg (Letter ℂ (fun v=>ComparisonDensity.Address.Orbit.Mood (D v)) k.val) zero).mpr Letter.still

theorem addition_published (K:Guard.Keeper Q.p Q.activities) (T:Taste (TestSpace D) o Q Γ)
    (h:Multilinear D T) (fin:∀x,Financed (T.menu.terms x)) (s:Γ.Mode)
    (f:TestSpace D→ℕ→ Config G n→ℂ) (typed:∀r U,Letter ℂ (fun v=>ComparisonDensity.Address.Orbit.Mood (D v)) s.val (fun x=>f x r U)) (i:ℕ) (U:Config G n) :
    Published (K:=ℂ) (fun v=>ComparisonDensity.Address.Orbit.Mood (D v)) (fun x=>addition (Y:=Y) K (T.menu.terms x) s (f x) i U) := by
  have hard (l : ℕ) : Published (K:=ℂ) (fun v=>ComparisonDensity.Address.Orbit.Mood (D v)) (fun x=>(T.menu.terms x).each l U) := by
    have fixed : Published (K:=ℂ) (fun v=>ComparisonDensity.Address.Orbit.Mood (D v)) (fun _ : TestSpace D=>Poly.send Γ.quiet (Q.activities.K l U : ℂ)) :=
      Published.const _ (fun k hk=>by simp [Poly.part_send,hk])
    have tags (j : ℕ) : Published (K:=ℂ) (fun v=>ComparisonDensity.Address.Orbit.Mood (D v)) (fun x=>(T.menu.terms x).tagged l j U) :=
      sent _ _ (h.forced l j U)
    exact fixed.sum (Published.assembly (fun j x=>(T.menu.terms x).tagged l j U) tags (fun x=>(fin x).1 l U))
  by_cases hit:i∈Set.range (address (Y:=Y) K)
  · obtain ⟨z,rfl⟩:=hit
    by_cases hg:gate z U
    · have one:=sent s (fun x=>f x z.1.1 U) (typed z.1.1 U)
      have many:=Published.prod (K:=ℂ) z.1.2 (fun l x=>(T.menu.terms x).each l U)
        (fun l _=>hard l)
      have eq : (fun x=>addition (Y:=Y) K (T.menu.terms x) s (f x) (address K z) U)=
          ((fun x=>Poly.send s (f x z.1.1 U)) * (fun x=>∏l∈z.1.2,(T.menu.terms x).each l U)) := by
        funext x
        simp [addition,QLocalMarkedJoinedCofactor.on_slot,QLocalMarkedJoinedCofactor.deposit,hg]
      exact (congrArg (Published (K:=ℂ) (fun v=>ComparisonDensity.Address.Orbit.Mood (D v))) eq).mpr (one.product many)
    · have eq : (fun x=>addition (Y:=Y) K (T.menu.terms x) s (f x) (address K z) U)=0 := by
        funext x
        simp [addition,QLocalMarkedJoinedCofactor.on_slot,QLocalMarkedJoinedCofactor.deposit,hg]
      exact (congrArg (Published (K:=ℂ) (fun v=>ComparisonDensity.Address.Orbit.Mood (D v))) eq).mpr Published.zero
  · have eq : (fun x=>addition (Y:=Y) K (T.menu.terms x) s (f x) i U)=0 := by
      funext x
      exact QLocalMarkedJoinedCofactor.escaped _ _ _ _ _ hit
    exact (congrArg (Published (K:=ℂ) (fun v=>ComparisonDensity.Address.Orbit.Mood (D v))) eq).mpr Published.zero

theorem typed (T:Taste (TestSpace D) o Q Γ) (h:Multilinear D T) (d:TestSpace D→ℕ→ Config G n→Poly Γ)
    (hd:∀i U,Published (K:=ℂ) (fun v=>ComparisonDensity.Address.Orbit.Mood (D v)) (fun x=>d x i U)) : Multilinear D (replace T (tape T d)) := by
  refine ⟨h.regular,?_,h.unit,h.captions⟩
  intro i j U
  obtain ⟨j,rfl⟩:=(roster Γ).surjective j
  cases j with
  | inl l=>
    let j := roster Γ (.inl l)
    change Letter ℂ (fun v=>ComparisonDensity.Address.Orbit.Mood (D v)) ((tape T d).mode i j).val (fun x=>(tape T d).value x i j U)
    have m := (QLocalCompulsoryJoinedTape.original T d (fun _=>0) i l U).1
    have v : (fun x=>(tape T d).value x i j U)=(fun x=>T.menu.force x i l U) :=
      funext (fun x=>(QLocalCompulsoryJoinedTape.original T d x i l U).2)
    rw [show (tape T d).mode i j=T.menu.marks i l from m]
    exact (congrArg (Letter ℂ (fun v=>ComparisonDensity.Address.Orbit.Mood (D v)) (T.menu.marks i l).val) v).mpr (h.forced i l U)
  | inr s=>
    by_cases hs:s=Γ.quiet
    · subst s
      simp only [replace,tape,mode,entry,Equiv.symm_apply_apply,Sum.elim_inr]
      exact Letter.still
    · simpa [replace,tape,mode,entry,hs] using hd i U s

def Knows (A:TestSpace D→Bands Γ Q) : Prop:=∃T:Taste (TestSpace D) o Q Γ,(∀x,A x=T.menu.terms x) ∧ Multilinear D T

theorem next (K:Guard.Keeper Q.p Q.activities) {A:TestSpace D→Bands Γ Q}
    (old:Knows (o:=o) A) (fin:∀x,Financed (A x)) (s:Γ.Mode) (f:TestSpace D→ℕ→ Config G n→ℂ)
    (letters:∀r U,Letter ℂ (fun v=>ComparisonDensity.Address.Orbit.Mood (D v)) s.val (fun x=>f x r U)) :
    Knows (o:=o) (fun x=>bands (A x) (addition (Y:=Y) K (A x) s (f x))) := by
  obtain ⟨T,eqn,ht⟩:=old
  have eq:A=T.menu.terms:=funext eqn
  rw [eq] at fin ⊢
  let d x:=addition (Y:=Y) K (T.menu.terms x) s (f x)
  exact ⟨replace T (tape T d),fun _=>rfl,typed T ht d (addition_published K T ht fin s f letters)⟩

theorem recovered {G:Gauge} {V:Type} [Fintype V] [DecidableEq V] {Γ:Census V} {n:Side} {Q:Rep G n} {D:V→ ComparisonDensity.Address.Orbit} {o:V→Site n} (T:Taste (TestSpace D) o Q Γ) (M:Multilinear D T) (H:Compulsory (TestSpace D) Γ G n)
    (got:Knows (o:=o) (replace T H).menu.terms) : Multilinear D (replace T H) := by
  obtain ⟨B,e,hB⟩:=got
  refine ⟨M.regular,?_,M.unit,M.captions⟩
  intro i j U
  have m:H.mode i j=B.menu.marks i j:=congrArg (fun z:Bands Γ Q=>z.marks i j) (e (fun _=>0))
  have f:(fun x=>H.value x i j U)=(fun x=>B.menu.force x i j U):=funext fun x=>
    congrArg (fun z:Bands Γ Q=>z.entries i j U) (e x)
  change Letter ℂ (fun v=>ComparisonDensity.Address.Orbit.Mood (D v)) (H.mode i j).val (fun x=>H.value x i j U)
  rw [m]
  exact (congrArg (Letter ℂ (fun v=>ComparisonDensity.Address.Orbit.Mood (D v)) (B.menu.marks i j).val) f).mpr (hB.forced i j U)

theorem field {G:Gauge} {V:Type} [Fintype V] [DecidableEq V] {Γ:Census V} {n:Side} {D:V→ ComparisonDensity.Address.Orbit} (P:MarkedPackets D G n Γ) {p:BudgetPoint} {a:V→Support n}
    {region:Comparison.Density.Testing.Region (fun v=>ComparisonDensity.Address.Orbit.Mood (D v)) n} {w:V→ℝ} {g width b:ℝ} {off cov:ℕ}
    (H:P.Paid p a region w g width b off cov) (phys:BudgetPoint) (c:ℂ) (s:Γ.Mode) (i:ℕ) (U:Config G n) :
    Letter ℂ (fun v=>ComparisonDensity.Address.Orbit.Mood (D v)) s.val (fun x=>QLocalThermalJoinedSource.row P phys g c s x i U) := by
  by_cases yes:QLocalThermalPacketDivision.pick P phys U i≠none ∧ s=P.mode i
  · obtain ⟨hot,rfl⟩ := yes
    have value : (fun x=>QLocalThermalJoinedSource.row P phys g c (P.mode i) x i U)=fun x=>c*P.term x g U i := by
      funext x
      simp [QLocalThermalJoinedSource.row,hot]
    exact (congrArg (Letter ℂ (fun v=>ComparisonDensity.Address.Orbit.Mood (D v)) (P.mode i).val) value).mpr ((H.term_letter i U).cmul c)
  · have value : (fun x=>QLocalThermalJoinedSource.row P phys g c s x i U)=0 := by
      funext x
      simp [QLocalThermalJoinedSource.row,yes]
    exact (congrArg (Letter ℂ (fun v=>ComparisonDensity.Address.Orbit.Mood (D v)) s.val) value).mpr Letter.still

end YM.Integration.QLocalMarkedJoinedLetters
