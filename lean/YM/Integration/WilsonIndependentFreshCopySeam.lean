import YM.Integration.WilsonIndependentFreshCopyWage
import YM.RegulatorIR.Halo.Trail

/-! The complete finite-to-cover discrepancy on each growing auxiliary board,
including the measured nonbare quiet history that preceded the new word. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace YM.Integration.WilsonIndependentFreshCopySeam
open RegulatorIR RegulatorIR.Binding RegulatorIR.Ledger RegulatorIR.Ledger.Sky
open Lattice RegulatorIR.Taping RegulatorIR.Geometry RegulatorIR.Laplace RegulatorIR.Quadratic
open RegulatorIR.Diagram RegulatorIR.Budget RegulatorIR.Halo RegulatorIR.Halo.Sight
open RegulatorIR.Budget.Layer RegulatorIR.Budget.Packet RegulatorIR.Budget.Deck RegulatorIR.Budget.Tuple
open RegulatorIR.Uniform RegulatorIR.Spatial RegulatorIR.Profiles RegulatorIR.Prim RegulatorIR.Ward
open RegulatorIR.Step RegulatorIR.Halo.Aug RegulatorIR.Motion
open WilsonIndependentFreshReplica WilsonIndependentFreshCopyWage
open scoped Topology ENNReal BigOperators
variable {G : Gauge} {W : Type} {M : W → ℕ} {n : Page M → Side} {S : Heir n G}

variable (H : Reel S) (T : S.Accounts) (quiet : H.Follows T) (large : Common H)
  (E : Era M) {L : Meter W} {p k m s a : ℕ} (B : S.Primitive L p k)
  (Z : (E.part S T B).Report m) (w : W)
local notation "Zc" => report H T quiet large E B Z w

variable (bank : S.Supplies T L p k) (C : Amenities S L p k) (film : W → Portrait G)
  (stamp : ∀ w, BasisT m s (film w) (Z.main (Page.opening E.spans w)))
include stamp bank C in
theorem winding (j : ℕ) (he : j ≤ E.spans w) (hq : 14 ≤ k) :
    ∀ e, e ≤ p → ∀ r, Claim light
      ((lpost H w (E.age w+j) (absAge E w he)).anchored (centre S w) 0) debt
      (fun z => (Zc).deviation (sheetAt E w j he z) e r) := by
 induction j with
 | zero=>
    intro i _ r; have hx(z:Side):(Zc).deviation (sheetAt E w 0 he z) i r=0:=by change Deck.scroll _ _ - Deck.scroll _ _=0; exact sub_self _
    simp_rw [hx]; exact Claim.zeroQ
 | succ j ih=>
    let d := E.age w+j
    have after : d+1 ≤ M w := absAge E w he
    let F:= known H w d after
    let A:= fun _ : Side => delay (S:=S) w d after
    let hv (z : Side) : 0 < A z := (eternal H w).hl ((stepf w d after z).next)
    let G':= F.incoming A hv; let K:=F.insideRoom A hv; let X:=F.outgoing A hv
    let Hp := grove H w large
    let g (z : Side) := (stepf w d after z).prev
    let g0 (z : Side) := (edgeAt E w j he z).prev
    let t (z : Side) := (tele H T w).bulk (g z)
    let u (z : Side) := (tele H T w).orb (g z)
    let v (z : Side) := (Zc).main (g0 z)
    let y (z : Side) := (Zc).point (g0 z)
    intro i hi r; let C':= C.enough (show k≥glaze 1 from hq); let B':= T_enough T bank hq
    let B₀:=lpost H w d (Nat.le_of_succ_le after)
    have hm(z): B₀.length z≤A z:=(eternal H w).climb (stepf w d after z)
    have hx (a) (h:a≤p) b : Claim light (G'.anchored (centre S w) 0) debt fun z=>(Zc).deviation (g0 z) a b:= Post.few_orb hv hm (ih (Nat.le_of_succ_le he) a h b)
    let W' z:=F.kick (fun z=>(Zc).deviation (g0 z) i r) z
    letI : ∀ z:Side,Fintype (Book G (big w n (g z))):= fun _=>inferInstance
    letI :∀ z:Side,Fintype (Book G (big w n ((stepf w d after z).next))):= fun _=>inferInstance
    have hy : Claim light (X.anchored (centre S w) 0) debt fun z=> (show Packet (Book G (big w n ((stepf w d after z).next))) r from (Zc).deviation ((edgeAt E w j he z).next) i r) - W' z:=by
       have hU:= Batch.node F t u v y (e:=i) (r:=r) (u:=0) (b:=1) (q:=6) (l₀:=A) (l:=A) (hl₀:=hv) (hl:=hv) le_rfl (beams H w C' d after) (fete H w d after) (fun z=>hort Hp (stepf w d after z)) (fun z _ _ _=>natural_o Hp _ _ _) (fun z _ _ _=>helium Hp _ (knows H T w large quiet) _ _ _) (fun z=> essential Hp _) (fun z=>(tele H T w).cap_b (fun i=> essential Hp i) (g z)) (fun z=>(tele H T w).cap_o (fun i=>essential Hp i) (g z)) (fun i ha _=> conflict H w T B' d after (ha.trans hi)) (fun i ha _=> added H w C' d after (ha.trans hi)) (fun i ha _ hr=> Post.fewer hv (M:=B₀) hm (horizons H T C' B' quiet large w d (Nat.le_of_succ_le after) i (ha.trans hi) _ hr)) (fun i ha r _=> Post.few_cover hv hm (rooted H T quiet large E B Z w bank C film stamp j (Nat.le_of_succ_le he) (by omega) i (ha.trans hi) r)) (fun _=> ENNReal.one_ne_top) (debtCost H w d after) (fun i r h _=> hx _ (by unfold Earlier at h; omega) _) (K.descent (spurs H w C d after) (Nat.zero_le k)) (fun z=> suitable Hp (stepf w d after z)) m
       convert hU using 1; ext1 z; unfold Accounts.Report.deviation;rw [← (Zc).step_p (edgeAt E w j he z),← (Zc).step_m (edgeAt E w j he z)];rfl
    have hW: Claim light (X.anchored (centre S w) 0) debt W' := F.out_mark (Claim.draft_budget (F.orb_bill_mark (hx i hi r)) (K.wrap_beam (K.descent (spurs H w C _ _) (Nat.zero_le k)) (fun z=> suitable Hp (stepf w d after z))))
    change Claim light (X.anchored (centre S w) 0) debt _; convert Claim.add hy hW using 1;ext1 z; exact Eq.symm (sub_add_cancel ..)

end YM.Integration.WilsonIndependentFreshCopySeam
