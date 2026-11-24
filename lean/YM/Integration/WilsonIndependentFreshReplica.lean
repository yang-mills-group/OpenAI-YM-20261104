import YM.Integration.WilsonIndependentFreshQuietReel
import YM.RegulatorIR.Halo.Celestial

/-! Enlarged inversion boards for one genuine captured word. Each board
inherits the full evolved unmarked finite vacuum from its own fine regulator.
Only the new measuring word is folded at its birth. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
namespace YM.Integration.WilsonIndependentFreshReplica
open RegulatorIR RegulatorIR.Binding RegulatorIR.Ledger RegulatorIR.Ledger.Sky
open Lattice RegulatorIR.Taping RegulatorIR.Geometry RegulatorIR.Laplace RegulatorIR.Quadratic
open RegulatorIR.Diagram RegulatorIR.Budget RegulatorIR.Halo RegulatorIR.Halo.Sight
open RegulatorIR.Uniform RegulatorIR.Profiles RegulatorIR.Prim RegulatorIR.Ward
open scoped Topology ContDiff
variable {G : Gauge} {W : Type} {M : W → ℕ} {n : Page M → Side} {S : Heir n G}

def copy (E : Era M) (w : W) : Era (extent M w) :=
  ⟨fun _ => E.age w, fun _ => E.spans w, fun _ => E.duration w⟩

def page (E : Era M) (w : W) (i : Page (copy E w).spans) : Page E.spans :=
  ⟨w,i.downW,i.good⟩

def wing (E : Era M) (w : W) (j : Flap (copy E w).spans) : Flap E.spans :=
  ⟨w,j.offset,j.ok⟩

def retained (H : Reel S) (T : S.Accounts) (E : Era M) : (E.expanse S).Accounts where
  bulk j := T.bulk (E.page j)
  orb j := T.orb (E.page j)
  step_v j := T.step_v (E.wing j)
  step_o j := T.step_o (E.wing j)
  top_v _ := T.cap_b (essential H) _
  top_o _ := T.cap_o (essential H) _

variable (H : Reel S) (T : S.Accounts) (quiet : H.Follows T) (large : Common H)
  (E : Era M) {L : Meter W} {p b m s : ℕ} (B : S.Primitive L p b)
  (Z : (E.part S T B).Report m) (w : W)

def field (j : Page (copy E w).spans) : Orders (Foot G) := fun e r =>
  echo (shiftE (S := S) w ((copy E w).page j)) (Z.main (page E w j) e r)

def report : (retained (grove H w large) (tele H T w) (copy E w)).Report m where
  main := field T E B Z w
  point := seriesC (X := fun j => Orders (Book G (big w n ((copy E w).page j))))
    (fun z e r => let j := Page.opening (copy E w).spans z
      (radar H w ((copy E w).page j)).scroll (field T E B Z w j e r))
    (fun j => (stations H w ((copy E w).wing j)).island m
      ((tele H T w).orb ((copy E w).page j.prev)))
  step_p j := (laterC j).symm
  step_m j := by
    let k := E.wing (wing E w j)
    change (S.frames k).each m (T.bulk k.prev) (field T E B Z w j.prev) =
      fun e r => echo _ (Z.main (wing E w j).next e r)
    rw [← Z.step_m (wing E w j)]
    exact step_echo _ (alloy H T quiet k) (hort H k) (suitable H k)
  ceilingM z e r h := Z.ceilingM w e r (fun zero => h (by
    change echo _ (Z.main (Page.opening E.spans w) e r) = 0
    rw [zero,echo_zero]))
  ceilingP z e r h := Z.ceilingM w e r (fun zero => h (by
    rw [earlierC]
    change Deck.scroll _ (echo _ (Z.main (Page.opening E.spans w) e r)) = 0
    rw [zero,echo_zero,Deck.scroll_zero]))
  same _ _ _ := rfl

def root (z : Side) : Cover := (n (E.page (Page.opening E.spans w))).val • journey z

theorem origin (film : W → Portrait G)
    (stamp : ∀ w, BasisT m s (film w) (Z.main (Page.opening E.spans w))) (z : Side) :
    BasisT m s (convey (root (n := n) E w z) (film w))
      ((report H T quiet large E B Z w).main (Page.opening (copy E w).spans z)) := by
  let j := (copy E w).page (Page.opening (copy E w).spans z)
  change BasisT m s _ (fun e r => echo (shiftE (S := S) w j)
    (Z.main (Page.opening E.spans w) e r))
  have moved : shiftE (S := S) w j = carryX (root (n := n) E w z) := by
    unfold shiftE
    rw [H.realms]
    ext1 k
    rfl
  rw [moved]
  exact (stamp w).vayne _

end YM.Integration.WilsonIndependentFreshReplica
