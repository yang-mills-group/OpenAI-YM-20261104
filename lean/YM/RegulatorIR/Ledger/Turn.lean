import YM.RegulatorIR.Ledger.Ages

/-! Applying soft propagation after measuring mesh and up to or beyond the
older stop. Estimates still refer to point testing. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Ledger.Sky
open Budget Spatial Budget.Packet Budget.Tariff Budget.Layer Budget.Tuple Budget.Deck Uniform Uniform.Post Function Step Diagram Gradient ENNReal
open scoped Topology ENNReal NNReal BigOperators Classical
variable {W:Type}{M:W→ℕ} {X Y:Page M→Type}
variable (S:Sky X Y) (T:S.Accounts){m:ℕ} (Z:T.Report m)
variable {r p u b α e:ℕ}{x:W→Room}{c:Flap M→ℝ≥0∞}{d: Page M→ℝ≥0∞}{L:Meter W}{s:W→ℝ≥0∞}{k j:Choice M}
structure Bend (Z:T.Report m)(u p:ℕ)(k:Choice M)(x:W→Room)(d:Page M→ℝ≥0∞)(s:W→ℝ≥0∞) (α:ℕ)(L:Meter W): Prop where
  young i : i ≤ p → ∀ j,0<j→ Claim L (fun w=> S.coverQ x u (k.choose w)) (fun w=> ticket d s (k.choose w)) fun w=> Z.main (k.choose w) i j
  consent : ∀ w i,i≤ p → (S.sight w).Way (Z.main w.prev) i
  sanctity : ∀ w i j,i≤ p → 0<j → j<α → Z.main w i j=0
  compact : ∀ w,s w≠⊤

variable (B:S.Primitive L p b)(N:S.Supplies T L p b) (A:S.Softness u L c d α)
   (J : S.Bend T Z u p k x d s α L)
include J
lemma saddle : let E:= k.after; (E.expanse S).Imprints (E.part S T B) (fun w=> Z.main (E.page w)) u p m x (d ∘ E.page) s α L:= by
 let E:= k.after
 refine { starts:= J.young, force:=?_, consent:= fun w=> J.consent (E.wing w), rank:=fun w i _=> Z.cap_b B.grade _ _, sanctity:=fun w=> J.sanctity (E.page w), compact:=J.compact }
 intro i hi j
 let N':= E.part S T B; let R:=fun w=> Z.main (E.page w)
 change Claim _ _ _ (fun w=>Z.main (E.page w.next) i j - (E.expanse S).reportOut N' R m w i j)
 have hh (w: Flap E.spans) : Z.main (E.page w.next) i j-(E.expanse S).reportOut N' R m w i j=0:=by
   unfold reportOut; change Z.main (E.wing w).next i j-(S.frames _).each _ _ _ _ _=0; rw [← Z.step_m (E.wing w)]; exact sub_self _
 simp_rw [hh]; exact Claim.zeroQ

variable (hu:u≤ b)
include B N A hu
lemma apogee (he:e ≤ p)(hr:0<r): Claim (coverL k.after.spans L) (fun w=> S.coverQ x u (k.after.page w)) (fun w=>ticket d s (k.after.page w)) fun w=> Z.main (k.after.page w) e r := by
 let E:= k.after
 exact (E.expanse S).glides (E.part S T B) (fun w=> Z.main (E.page w)) (E.sector S B) (E.getN S N B) (E.credit S A) (S.saddle T Z B J) hu _ he _ hr

private def atJ (_:k.age≤j.age)(w: W): Page k.after.spans:=⟨w,j.age w-k.age w,Nat.sub_le_sub_right (j.young w) _⟩
omit B N A J hu in
private lemma equals (hj:k.age≤j.age)(w : W): k.after.page (atJ hj w) = j.choose w:=by unfold Choice.after Era.page Choice.choose atJ; simp [Nat.add_sub_of_le (hj w)]
lemma success (hj:k.age≤j.age) (he:e≤p)(hr:0<r): Claim L (fun w=> S.coverQ x u (j.choose w)) (fun w=>ticket d s (j.choose w)) fun w=> Z.main (j.choose w) e r:= by
 have he': Carry L (fun w=>ticket d s (k.after.page (atJ hj w))) fun w=> markQ (S.coverQ x u (k.after.page (atJ hj w))) (Z.main (k.after.page (atJ hj w)) e r):= Carry.us (S.apogee T Z B N A J hu he hr) (atJ hj)
 unfold Claim; convert he' using 1
 · ext1 w; rw [equals]
 ext1 w; rw [equals]
lemma marled (hj:k.age≤j.age) (he:e≤p): Carry L (fun w=> ticket d s (j.choose w)) (fun w=> ‖note (Z.main (Page.finallyW M w) e 0)- note (Z.main (j.choose w) e 0)‖ₑ):=by
 let E:=j.after; let R:=fun w=> Z.main (E.page w)
 have hJ : S.Bend T Z u p j x d s α L:= { J with young:=fun _ he _ hr=> S.success T Z B N A J hu hj he hr }
 have hp: Carry L (fun w=> ticket d s (j.choose w)) fun w=> ‖note (Z.main (j.after.page (Page.finallyW j.after.spans w)) e 0)-note (Z.main (j.choose w) e 0)‖ₑ := Carry.us ((E.expanse S).till _ R (E.sector S B) (E.getN S N B) (E.credit S A) (S.saddle T Z B hJ) hu he) (Page.finallyW _)
 convert hp using 1; ext1 w; rw [Choice.finalPage]
lemma woven (hj:k.age≤j.age) (he:e≤p): Carry L (fun w=> ticket d s (k.choose w)) (fun w=> ‖note (Z.main (j.choose w) e 0) - note (Z.main (k.choose w) e 0)‖ₑ):=by
 let E:= k.after; let R:= fun w=> Z.main (E.page w)
 have hq := (E.expanse S).till _ R (E.sector S B) (E.getN S N B) (E.credit S A) (S.saddle T Z B J) hu he
 have hp: Carry L (fun w=> ticket d s (k.choose w)) fun w=> ‖note (Z.main (k.after.page (atJ hj w)) e 0)-note (Z.main (k.choose w) e 0)‖ₑ:= Carry.us hq (atJ hj)
 convert hp using 1; ext1 w; rw [equals]
end YM.RegulatorIR.Ledger.Sky
