import YM.RegulatorIR.Step.Cap
import YM.RegulatorIR.Uniform.RelaxMark

/-! Family-based *uniform* step. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Uniform
open Budget Budget.Packet Budget.Tuple Budget.Deck Budget.Layer Budget.Tariff Diagram Function Step Step.GridStep Post
open scoped Topology ENNReal NNReal BigOperators Classical
variable {W:Type} {X Y U V:W→Type} {r:ℕ}
structure Batch (X Y U V : W→Type) where
 period : W→ℝ
 positive : ∀ w,0<period w
 fine : ∀ w, Deck (period w) (X w) (U w)
 coarse : ∀ w, Deck (period w) (Y w) (V w)
 grid : ∀ w, GridStep (fine w) (coarse w)

namespace Batch
variable (F:Batch X Y U V)

def incoming (l:W→ℝ) (h:∀ w,0<l w) : Post X U:=⟨F.period,F.positive,l,h,F.fine⟩
def insideRoom (l:W→ℝ) (h:∀ w,0<l w): Post (fun w=> X w ⊕ Y w) (fun w=>U w⊕ V w):=⟨F.period,F.positive,l,h,fun w=> combine (F.fine w) (F.coarse w)⟩
def outgoing (l:W→ℝ)(h:∀ w,0<l w):Post Y V:= ⟨F.period,F.positive,l,h,F.coarse⟩

variable {L : Meter W}{l:W→ℝ}{hl:∀ w,0<l w}
variable {u:ℕ}{T:(w:W)→Packet (X w) r}
lemma fine_bill (hT:Workday L ((F.incoming l hl).cone u) T):
    Workday L ((F.insideRoom l hl).cone u) fun w=> offer (firstChannel (F.fine w) (F.coarse w)).native (T w):=by
 obtain ⟨f,hf,H⟩:=hT;refine ⟨_,hf,fun w=>?_⟩
 let C:=firstChannel (F.fine w) (F.coarse w)
 change localQ (((native (l w) (hl w) u)).uses (combine (F.fine w) (F.coarse w)).pos) _ _
 apply local_offer ; rw [Channel.native_paid]; exact H _

lemma fine_work {T:(w:W)→ Orders (X w)}{i j:ℕ}(hT: Workday L ((F.incoming l hl).cone u) fun w=>T w i j)(hF: Workday L ((F.insideRoom l hl).cone u) fun w=>(F.grid w).addon i j): Workday L ((F.insideRoom l hl).cone u) fun w=> (F.grid w).jVac (T w) i j:= Workday.add (F.fine_bill hT) hF
lemma onto_bill {x:W→Room}{v}(hT:Claim L ((F.incoming l hl).rooted x u) v T): Claim L ((F.insideRoom l hl).rooted x u) v fun w=> offer (firstChannel (F.fine w) (F.coarse w)).native (T w):=by
 apply Carry.mono hT
 intro w
 let A:=combine (F.fine w) (F.coarse w); let C:=firstChannel (F.fine w) (F.coarse w); let B:= Premium.rooted (native (l w) (hl w) u) (x w)
 change markQ (B.uses A.pos) (offer C.native (T w))≤markQ (B.uses _) _
 have he:= mark_offer C.native (B:=B) (y:=A.pos) (T:=T w);rw [Channel.native_paid] at he;exact he
lemma orb_bill {Z:(w:W)→Packet (U w) r}(hT:Claim L ((F.incoming l hl).pear u) 1 Z): Claim L ((F.insideRoom l hl).pear u) 1 fun w=> offer (firstChannel (F.fine w) (F.coarse w)).tile (Z w):=by
 apply Carry.mono hT;intro w
 have he:=mark_offer (firstChannel (F.fine w) (F.coarse w)).tile (B:=Premium.remnant _ (F.positive w) _ (hl w) u) (y:=(combine (F.fine w) (F.coarse w)).atO) (T:=Z w);rw [Channel.tile_paid] at he;exact he
lemma orb_bill_mark {x:W→Room}{v}{Z:(w:W)→Packet (U w) r}(hT:Claim L ((F.incoming l hl).anchored x u) v Z): Claim L ((F.insideRoom l hl).anchored x u) v fun w=> offer (firstChannel (F.fine w) (F.coarse w)).tile (Z w):=by
 apply Carry.mono hT;intro w
 have he:=mark_offer (firstChannel (F.fine w) (F.coarse w)).tile (B:=Premium.rooted (Tariff.onFold _ (F.positive w) _ (hl w) u) (x w)) (y:=(combine (F.fine w) (F.coarse w)).atO) (T:=Z w);rw [Channel.tile_paid] at he;exact he
lemma out_bill {Z:(w:W)→Packet (U w ⊕ V w) r}(hT:Claim L ((F.insideRoom l hl).pear u) 1 Z): Claim L ((F.outgoing l hl).pear u) 1 fun w=> crop (lastChannel (F.fine w) (F.coarse w)).tile (Z w):=by
 apply Carry.mono hT;intro w
 have he:= mark_crop (lastChannel (F.fine w) (F.coarse w)).tile (B:=Premium.remnant _ (F.positive w) _ (hl w) u) (y:=(combine (F.fine w) (F.coarse w)).atO) (T:=Z w); rw [Channel.tile_paid] at he;exact he
lemma out_mark {x:W→Room}{v}{Z:(w:W)→Packet (U w ⊕ V w) r}(hT:Claim L ((F.insideRoom l hl).anchored x u) v Z): Claim L ((F.outgoing l hl).anchored x u) v fun w=> crop (lastChannel (F.fine w) (F.coarse w)).tile (Z w):=by
 apply Carry.mono hT;intro w
 have he:=mark_crop (lastChannel (F.fine w) (F.coarse w)).tile (B:=Premium.rooted (Tariff.onFold _ (F.positive w) _ (hl w) u) (x w)) (y:=(combine (F.fine w) (F.coarse w)).atO) (T:=Z w); rw [Channel.tile_paid] at he; exact he
lemma out_post {x:W→Room}{v}{Z:(w:W)→Packet (X w ⊕ Y w) r}(hT:Claim L ((F.insideRoom l hl).rooted x u) v Z): Claim L ((F.outgoing l hl).rooted x u) v fun w=> crop (lastChannel (F.fine w) (F.coarse w)).native (Z w):= by
 apply Carry.mono hT;intro w
 have he:= mark_crop (lastChannel (F.fine w) (F.coarse w)).native (T:=Z w) (B:=Premium.rooted (Tariff.native _ (hl w) u) (x w)) (y:=(combine (F.fine w) (F.coarse w)).pos); rw [Channel.native_paid] at he;exact he
end Batch
end YM.RegulatorIR.Uniform
