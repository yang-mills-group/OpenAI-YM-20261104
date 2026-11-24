import YM.RegulatorIR.Budget.Channels
import YM.RegulatorIR.Budget.RayScroll
import YM.RegulatorIR.Budget.Algebra

/-! Deterministic transmission of an unmixed rank component through one
step, later used as the only repeated component in an iteration. Convention
here: view L as map on tensors (new index on **left**). Use transpose of
the row estimates on the predictor. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Budget
open Function Motion Layer Tuple Packet Deck
open scoped Topology ENNReal NNReal BigOperators Classical
variable {X Y Z : Type} {r : ℕ} {P:ℝ}
namespace Packet

def drawing (T:Packet X r)(K:Layer X X): List (Fin r) → Packet X r
| [] => T
| a::as => ray a (drawing T K as) K

def draft (K:Layer X X)(T:Packet X r):Packet X r:=Packet.symmetry (drawing T K (List.finRange r))
variable {T:Packet X r} {K:Layer X X}{A:Tariff X} {B:Premium A}{c d:ℝ≥0∞}
lemma local_draw (h:row K A id id c)(hh:row (swap K) A id id c)(ht:localQ A T d)(w:List (Fin r)):
    localQ A (drawing T K w) (d*c^w.length):=by
 induction w with
 | nil=>simpa [drawing] using ht
 | cons a l ih=> rw [List.length_cons,pow_succ,← mul_assoc]; exact ray_local _ _ h hh ih
lemma local_draft (h:row K A id id c)(hh:row (swap K) A id id c)(ht:localQ A T d):
    localQ A (draft K T) (d*c^r):= local_symmetry <| by simpa only [List.length_finRange] using local_draw h hh ht (List.finRange r)
lemma mark_draw (h:row (swap K) A id id c)(T:Packet X r)(w:List (Fin r)):
   markQ B (drawing T K w) ≤ markQ B T*c^w.length := by
 induction w with
 | nil=> simp [drawing]
 | cons a l ih=> rw [List.length_cons,pow_succ,← mul_assoc]; exact (ray_mark a _ h).trans (mul_le_mul_left ih _)
lemma mark_draft (h:row (swap K) A id id c)(T:Packet X r):
   markQ B (draft K T) ≤ markQ B T*c^r := mark_symmetry.trans <| by simpa only [List.length_finRange] using mark_draw (B:=B) h T (List.finRange _)

section period
variable (S:Deck P X Y)
lemma ready_draw (hh:Layer.Sym S S K)(ht:S.Ready T)(w:List (Fin r)) : S.Ready (drawing T K w):=by
 induction w with
 | nil=> exact ht
 | cons a l ih => exact ray_ready S _ ih hh
lemma draft_ready (hh:Layer.Sym S S K)(ht:S.Ready T): S.Ready (draft K T):=S.symm_ready (ready_draw S hh ht _)
variable [Fintype Y]
lemma drawn (hh:Layer.Sym S S K)(ht:S.Ready T)(h:row K A id id c)(hh':row (swap K) A id id c)(hT:localQ A T d) (hc:c≠⊤)(hd:d≠⊤)(w:List (Fin r)): S.deckSum (drawing T K w)=drawing (S.deckSum T) (wrapL S S K) w := by
 induction w with
 | nil=>rfl
 | cons a l ih=>rw [drawing,drawing,ray_period S _ (local_draw h hh' hT l) h (by finiteness) hc hh (ready_draw S hh ht l),ih]
lemma draft_per (hh:Layer.Sym S S K)(ht:S.Ready T)(h:row K A id id c)(hh':row (swap K) A id id c)(hT:localQ A T d)(hc:c≠⊤)(hd:d≠⊤): S.deckSum (draft K T)=draft (wrapL S S K) (S.deckSum T) := by unfold draft; rw [S.desk_sym (local_draw h hh' hT _) (by finiteness) (ready_draw S hh ht _),drawn S hh ht h hh' hT hc hd]
omit [Fintype Y] in
lemma draw_scroll (hh:Layer.Sym S S K)(ht:markQ B T≠⊤)(h:row K A id id c)(hh':row (swap K) A id id c)(hc:c≠⊤)(w:List (Fin r)) : S.scroll (drawing T K w) = drawing (S.scroll T) (wrapL S S K) w := by
 induction w with
 | nil=>rfl
 | cons a l ih=> rw [drawing,drawing,ray_scroll S _ hh (mark_draw (B:=B) hh' _ l) h hh' (by finiteness) hc, ih]
omit [Fintype Y] in
lemma draft_scroll (hh:Layer.Sym S S K)(ht:markQ B T≠⊤)(h:row K A id id c)(hh':row (swap K) A id id c)(hc:c≠⊤): S.scroll (draft K T)=draft (wrapL S S K) (S.scroll T):= by
 unfold draft; rw [S.scroll_sym,draw_scroll S hh ht h hh' hc]; exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ht (by finiteness)) ((quota_mono _ (w:=1) (fun x=> B.width_unit x)).trans (mark_draw hh' _ _))
end period
end Packet
end YM.RegulatorIR.Budget
