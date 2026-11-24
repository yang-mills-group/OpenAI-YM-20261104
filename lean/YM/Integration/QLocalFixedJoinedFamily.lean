import YM.Integration.QLocalMarkedJoinedFamily

/-! One outgoing compulsory register before all further quantitative
requests on the original complete finite marked multiplication. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QLocalFixedJoinedFamily
open Finset Lattice RG Wilson Marker Overlay Extra.Histories Planned.GuardedAtom
open RG3.Script.Picnic QLocalCompulsoryJoinedTape QLocalMarkedJoinedLinear QLocalMarkedJoinedCatalogue
open WilsonLimitConstruction.FundedMarkedFieldSplit
open scoped BigOperators Classical
variable {G : Gauge} {n : Side} {W : Rep G n} {X V : Type} [DecidableEq V] [Fintype V]
    {Γ : Census V} {o : V→Site n} {Y : ℕ→Support n} {d : X→ Config G n→Poly Γ}
    (K : Guard.Keeper W.p W.activities) (T : Taste X o W Γ) (F : Source (W:=W) Y d)

def Advances (C : (X→Bands Γ W)→ℕ→Prop) : Prop :=
  ∀ (A : X→Bands Γ W) (j : ℕ),j<Fintype.card Γ.Mode → C A j →
    (∀x,Financed (A x)) → ∀ s : Γ.Mode,s≠Γ.quiet →
      C (fun x=>bands (A x) (addition (Y:=Y) K (A x) s (F.field s x))) (j+1)

structure Fixed where
  book : Compulsory X Γ G n
  preserves (C : (X→Bands Γ W)→ℕ→Prop) (start : C T.menu.terms 0) (step : Advances K F C) :
    C (replace T book).menu.terms (Finset.univ.erase Γ.quiet).card
  field x : Financed ((replace T book).menu.terms x) ∧ ∀U,
    ((replace T book).leaf x).contents.cluster U=Poly.pass (d x U)*(T.leaf x).contents.cluster U ∧
    ((replace T book).leaf x).density U=Poly.pass (d x U)*(T.leaf x).density U

theorem sale (quiet : ∀x U,(d x U).part Γ.quiet=0) (prior : ∀x,Financed (T.menu.terms x)) :
    Nonempty (Fixed K T F) := by
  let C (A : X→Bands Γ W) (j : ℕ):=
    ∀ H : (X→Bands Γ W)→ℕ→Prop,H T.menu.terms 0 → Advances K F H → H A j
  have first : C T.menu.terms 0:=fun _ base _=>base
  have next : Advances K F C:=by
    intro A j hj current finance s hs H base lift
    exact lift A j hj (current H base lift) finance s hs
  obtain ⟨B,tests,full⟩:=QLocalMarkedJoinedFamily.issued K T F quiet C first prior next
  exact ⟨⟨B,tests,full⟩⟩

end YM.Integration.QLocalFixedJoinedFamily
end
