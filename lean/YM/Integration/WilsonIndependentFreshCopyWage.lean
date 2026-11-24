import YM.Integration.WilsonIndependentFreshCopyRange
import YM.RegulatorIR.Halo.Trail

/-! Uniformity in the auxiliary period at each fixed original regulator. The
root of the occupied copy is moved by the deck at its actual age. All charges
for the unmarked vacuum are taken from the original programme. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace YM.Integration.WilsonIndependentFreshCopyWage
open RegulatorIR RegulatorIR.Binding RegulatorIR.Ledger RegulatorIR.Ledger.Sky
open Lattice RegulatorIR.Taping RegulatorIR.Geometry RegulatorIR.Laplace RegulatorIR.Quadratic
open RegulatorIR.Diagram RegulatorIR.Budget RegulatorIR.Halo RegulatorIR.Halo.Sight
open RegulatorIR.Budget.Layer RegulatorIR.Budget.Packet RegulatorIR.Budget.Deck RegulatorIR.Budget.Tuple
open RegulatorIR.Uniform RegulatorIR.Spatial RegulatorIR.Profiles RegulatorIR.Prim RegulatorIR.Ward
open RegulatorIR.Step RegulatorIR.Halo.Aug RegulatorIR.Motion
open WilsonIndependentFreshReplica
open scoped Topology ENNReal BigOperators
variable {G : Gauge} {W : Type} {M : W → ℕ} {n : Page M → Side} {S : Heir n G}

theorem absAge (E : Era M) (w : W) {j : ℕ} (h : j ≤ E.spans w) : E.age w + j ≤ M w :=
  (Nat.add_le_add_left h _).trans (E.duration w)

def sheetAt (E : Era M) (w : W) (j : ℕ) (h : j ≤ E.spans w) (z : Side) : Page (copy E w).spans :=
  ⟨z,j,h⟩

def edgeAt (E : Era M) (w : W) (j : ℕ) (h : j < E.spans w) (z : Side) : Flap (copy E w).spans :=
  ⟨z,j,h⟩

variable (H : Reel S) (T : S.Accounts) (quiet : H.Follows T) (large : Common H)
  (E : Era M) {L : Meter W} {p k m s a : ℕ} (B : S.Primitive L p k)
  (Z : (E.part S T B).Report m) (w : W)
local notation "Zc" => report H T quiet large E B Z w

theorem relocate (j : ℕ) (h : j ≤ E.spans w) (z : Side) (e r : ℕ) :
    markQ ((lpost H w (E.age w+j) (absAge E w h)).rooted (centre S w) a z)
        ((Zc).main (sheetAt E w j h z) e r) =
      markQ (S.census.rooted (fun _ => 0) a (E.page ⟨w,j,h⟩))
        (Z.main ⟨w,j,h⟩ e r) := by
  let x := shiftE (S := S) w (sheet w (E.age w+j) (absAge E w h) z)
  let path := Equiv.piCongrRight (fun _ : Fin r => x)
  unfold markQ quota
  rw [← path.tsum_eq]
  apply tsum_congr
  intro i
  exact congrArg₂ (·*·) (congrArg (fun t : ℝ => ‖t‖ₑ) (echos x _ i))
    (root_shape H w (E.age w+j) (absAge E w h) z i _)

variable (bank : S.Supplies T L p k) (C : Amenities S L p k) (film : W → Portrait G)
  (stamp : ∀ w, BasisT m s (film w) (Z.main (Page.opening E.spans w)))
include stamp bank C in
theorem rooted (j : ℕ) (h : j ≤ E.spans w) (paid : a ≤ k) :
    ∀ e, e ≤ p → ∀ r, Claim light
      ((lpost H w (E.age w+j) (absAge E w h)).rooted (centre S w) a) 1
      (fun z => (Zc).main (sheetAt E w j h z) e r) := by
  induction j with
  | zero =>
    intro e _ r
    unfold Claim
    simp_rw [relocate]
    refine Carry.regular (Poly.standard light ?_)
    exact support_cost _ _ _ _ _ ((stamp w).canopy e r)
  | succ j ih =>
    let d := E.age w+j
    have after : d+1 ≤ M w := absAge E w h
    let F := known H w d after
    let A := fun _ : Side => delay (S := S) w d after
    let hv (z : Side) : 0 < A z := (eternal H w).hl ((stepf w d after z).next)
    let G' := F.incoming A hv
    let K := F.insideRoom A hv
    let X := F.outgoing A hv
    let Hp := grove H w large
    let g (z : Side) := (edgeAt E w j h z).prev
    let YV (z : Side) := (tele H T w).bulk ((stepf w d after z).prev)
    let Fm (z : Side) := (Zc).main (g z)
    intro i hi r
    have hm e' (hi' : e' ≤ p) r : Claim light (G'.rooted (centre S w) a) 1 (fun z => Fm z e' r) := by
      have earlier := ih (Nat.le_of_succ_le h) e' hi' r
      exact Post.few_cover hv (M := lpost H w d (Nat.le_of_succ_le after))
        (fun z => (eternal H w).climb (stepf w d after z)) earlier
    have hx (v : ℕ) : Claim light (K.rooted (centre S w) a) 1
        (fun z => F.primary YV Fm z v i r) := by
      cases v with
      | zero => unfold Batch.primary; simp_rw [markHeat_first]; exact F.onto_bill (hm i hi r)
      | succ v =>
        apply Batch.issue F YV Fm (K.descent (beams H w C d after) paid)
          (fun e he r => K.writes (F.fine_work (conflict H w T bank d after (he.trans hi))
            (added H w C d after (he.trans hi))) paid)
          (fun z => GridStep.joint_vac_shape _ ((tele H T w).cap_b (fun i => essential Hp i) _)
            (essential Hp (stepf w d after z))) _ _ (by omega)
        exact fun e r lower _ => hm e (by unfold Earlier at lower; omega) r
    have total := Claim.sum (L := light) (B := K.rooted (centre S w) a) _
      (Finset.range (m+3*i+1)) (fun v _ => hx v)
      |>.draft_budget (K.descent (spurs H w C d after) paid)
    have result := F.out_post total
    change Claim light (X.rooted (centre S w) a) 1 _
    convert result using 1
    ext1 z
    exact Eq.symm (congrFun (congrFun ((Zc).step_m (edgeAt E w j h z)) i) r)

end YM.Integration.WilsonIndependentFreshCopyWage
