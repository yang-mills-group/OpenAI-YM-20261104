import YM.RegulatorIR.Step.Quota
import YM.RegulatorIR.Gradient.Straight
import YM.RegulatorIR.Gradient.Polynomial

/-! Ward-specific diagonal replacement and gain. Contract form just asks the
**algebraic gauge identity**, not the contraction or norm transport; the finite
period version can use Gradient.Polynomial to check it from direct finite
Wilson gauge identities. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Step
open Gradient Budget Motion Budget.Deck Budget.Tariff Budget.Packet Budget.Layer Diagram Function
open scoped Topology ENNReal NNReal BigOperators Classical
variable {X Y U V:Type}{P:ℝ}{A:Deck P X U}{B:Deck P Y V} (S:GridStep A B)

-- k=0-only counterpart (plain linear substitution)
def inert (p:X↪U) (q:Y↪U) (K:Layer U U) : Curve X Y:=fun x i t=> if i=0 then K (q (t 0)) (p x) else 0
lemma inert_d (p:X↪U)(q:Y↪U)(K:Layer U U): Gradient.diagonal p q K (inert p q K):=fun _ _=>if_pos rfl
lemma inert_b (p:X↪U)(q:Y↪U)(K:Layer U U): Blank (inert p q K):=by intro i v hv; funext x; exact if_neg hv.ne'

/-- Includes the proposed repeated substitute. When binding, `pole` only on
fine input species, from period-compatible prelength predictor A₀. `space` and
`run` are the gauge-transformed link substitution tensors, and `Ground`
records the linear gradient relationship. -/
structure Strip (S:GridStep A B) where
 pole: Layer (X⊕Y) (X⊕Y)
 space : Curve X Y
 run : Curve U V
namespace Strip
variable {S} (M:Strip S)

def perimeter : Layer (U⊕V) (U⊕V):= Layer.wrapL (combine A B) (combine A B) M.pole

def straight : Curve X Y:= inert (firstChannel A B).native (lastChannel A B).native M.pole
def tunnel : Curve U V:=inert (firstChannel A B).tile (lastChannel A B).tile M.perimeter
structure Ground (M:Strip S):Prop where
 horizontal : Layer.Sym (combine A B) (combine A B) M.pole
 links : Gradient.diagonal (firstChannel A B).native (lastChannel A B).native S.driftL M.space
 inverted : Gradient.diagonal (firstChannel A B).tile (lastChannel A B).tile S.mean M.run

def Way (C:Orders X)(e : ℕ):Prop := shot M.straight C e = shot M.space C e
def WayO (C:Orders U)(e : ℕ): Prop:= shot M.tunnel C e= shot M.run C e

lemma repairI (h:M.Ground) (T:Orders X){e j :ℕ} (H:M.Way T e) {c:ℝ≥0∞} (hc:c≠⊤)(hQ:height S.driftL c)(hv:quota (T e j) 1≠⊤):
    S.pullI (offer (firstChannel A B).native (T e j)) - updateQ M.straight (T e j) 0 = -correction M.space T e j :=by
 rw [← show _= S.pullI _ from carriage (firstChannel A B).native _ S.driftL (T e j) h.links hv hQ hc]
 have H:= congr_fun H j; rw [blankShot M.straight (inert_b _ _ _), comprehensive] at H;rw [H];abel
lemma repairO (h:M.Ground) (T:Orders U){e j :ℕ} (H:M.WayO T e) {c:ℝ≥0∞} (hc:c≠⊤)(hQ: height S.mean c)(hv:quota (T e j) 1≠⊤):
   S.pullJ (offer (firstChannel A B).tile (T e j))- updateQ M.tunnel (T e j) 0= -correction M.run T e j:=by
 rw [← show _=S.pullJ _ from carriage _ _ _ _ h.inverted hv hQ hc];have H:=congr_fun H j;rw [blankShot M.tunnel (inert_b _ _ _),comprehensive] at H;rw [H];abel

-- costs on same norms; small field-independent scalar doesn't receive a power of the width (use r=0).
lemma upright {l:ℝ}{b:ℕ}{r:ℕ}(hl:0<l) (C:Premium (native l hl b)){c:ℝ≥0∞}(hc:c≠⊤)(hh: Layer.row (swap M.pole) (native l hl b) (combine A B).pos (combine A B).pos c) (T:Packet X r)(hf:quota T 1 ≠ ⊤):
  markQ (C.uses B.pos) (Gradient.updateQ M.straight T 0) ≤ markQ (C.uses A.pos) T*c^r :=by
 have hp:height M.pole c:=fun a b=> Layer.row_to_sup hh b a
 rw [carriage _ _ _ _ (show Gradient.diagonal (firstChannel A B).native (lastChannel A B).native M.pole M.straight from inert_d _ _ _) hf hp hc]
 let T':= combine A B; let f:=firstChannel A B; let t:=lastChannel A B
 have hf' : T'.pos ∘ f.native=A.pos:= f.native_paid
 have ht : T'.pos ∘ t.native=B.pos:= t.native_paid
 have hi := mark_crop t.native (T:=draft M.pole (offer f.native T)) (B:=C) (y:=T'.pos);rw [ht] at hi
 apply hi.trans ((mark_draft (A:=Tariff.uses _ T'.pos) hh _).trans ?_)
 have hh:= mark_offer f.native (T:=T) (B:=C) (y:=T'.pos);rw [hf'] at hh; exact mul_le_mul_left hh _
lemma tunnel_price (hg:M.Ground) {l : ℝ}{b r:ℕ}(h:0<P)(hl:0<l)(C:Premium (onFold P h l hl b)){c:ℝ≥0∞}(hc:c≠⊤)(hh:Layer.row (swap M.pole) (native l hl b) (combine A B).pos (combine A B).pos c) (T:Packet U r)(hf:quota T 1 ≠ ⊤):
   markQ (C.uses B.atO) (updateQ M.tunnel T 0) ≤ markQ (C.uses A.atO) T*c^r := by
 let T':=combine A B; let f:=firstChannel A B; let t:=lastChannel A B
 have H : row (swap M.perimeter) (onFold P h l hl b) T'.atO T'.atO c:= by rw [show swap M.perimeter= wrapL T' T' (swap M.pole) from funext fun x=>funext fun y=> Layer.other T' T' M.pole hg.horizontal y x]; exact row_cost T' T' (Function.swap M.pole) h hl b hh
 have hp: height M.perimeter c:= fun x y=>row_to_sup H y x
 rw [carriage _ _ _ _ (show Gradient.diagonal f.tile t.tile M.perimeter M.tunnel from inert_d _ _ _) hf hp hc]
 have hi:= mark_crop t.tile (T:=draft M.perimeter (offer f.tile T)) (B:=C) (y:=T'.atO); rw [Channel.tile_paid] at hi
 apply hi.trans ((mark_draft (A:=Tariff.uses _ T'.atO) H _).trans ?_)
 have h:= mark_offer f.tile (T:=T) (B:=C) (y:=T'.atO); rw [Channel.tile_paid] at h; exact mul_le_mul_left h _
end Strip
end YM.RegulatorIR.Step

-- uniform adapters. Need these even for varying periods where finite
-- summability at each regulator no longer is enough.
namespace YM.RegulatorIR.Uniform.Batch
open Gradient Step Budget Budget.Packet Budget.Deck Budget.Tuple Budget.Tariff Diagram Function
open scoped Topology ENNReal NNReal BigOperators Classical
variable {W:Type} {X Y U V:W→Type}{l:W→ℝ}{L:Meter W}{F:Batch X Y U V}{hl:∀ w,0<l w}
variable (S:∀ w,Strip (F.grid w)) {b e r:ℕ} {s:W→ℝ≥0∞}
-- supply per-step chosen approximation to exact horizontal plane with its graded variation
lemma recover {T:(w:W)→Orders (U w)}(B:∀ w,Premium (onFold (F.period w) (F.positive w) (l w) (hl w) b))
   (h:∀ i ≤ e,SmoothPrice L (fun w=> onFold _ (F.positive w) _ (hl w) b) (fun w=> (F.fine w).atO) (fun w=>(F.coarse w).atO) (fun w=>(S w).run) i)
   (ht:∀ i<e,∀ j, 0<j → Claim L (fun w=> (B w).uses (F.fine w).atO) s fun w=> T w i j) (hv:∀ w, (S w).Ground) (hw:∀ w,(S w).WayO (T w) e) (hc:Beam L ((F.insideRoom l hl).per b) (fun w=> (F.grid w).mean)) [∀ w,Fintype (U w)] :
     Claim L (fun w=> (B w).uses (F.coarse w).atO) s fun w=> F.kick (fun w=>T w e r) w-updateQ (S w).tunnel (T w e r) 0:= by
 obtain ⟨c,hc,H⟩:=hc
 let A : ∀ w,Packet (V w) r:= fun w=> correction (S w).run (T w) e r
 have hS w : F.kick (fun w=>T w e r) w-updateQ (S w).tunnel (T w e r) 0= (-1:ℝ) • A w:=by
    rw [neg_one_smul]; exact (S w).repairO (hv w) (T w) (hw w) (hc.cost _) (Layer.row_to_sup (H w).1) (by
      rw [quota_base]; exact tsum_enorm_ne_top_iff_summable_norm.mpr (hasSum_fintype ..).summable)
 simp_rw [hS]; exact Claim.csmul (correction_bill h ht) _
lemma land {T:(w:W)→Orders (X w)}(B:∀ w,Premium (native (l w) (hl w) b))
   (h:∀ i ≤ e,SmoothPrice L (fun w=> native _ (hl w) b) (fun w=> (F.fine w).pos) (fun w=>(F.coarse w).pos) (fun w=>(S w).space) i)
   (ht:∀ i<e,∀ j,0<j → Claim L (fun w=> (B w).uses (F.fine w).pos) s fun w=> T w i j)(hf:∀ w,quota (T w e r) 1≠⊤)
   (hv:∀ w, (S w).Ground)(hw:∀ w,(S w).Way (T w) e)(hc:Beam L ((F.insideRoom l hl).cone b) F.forecast):
    Claim L (fun w=> (B w).uses (F.coarse w).pos) s fun w=> F.bump (fun w=>T w e r) w-updateQ (S w).straight (T w e r) 0:= by
 obtain ⟨c,hc,H⟩:=hc
 let A := fun w=> correction (S w).space (T w) e r
 have he w:F.bump (fun w=>T w e r) w-updateQ (S w).straight (T w e r) 0= (-1:ℝ) • A w:=by rw [neg_one_smul];exact (S w).repairI (hv w) (T w) (hw w) (hc.cost _) (Layer.row_to_sup (H w).1) (hf w)
 simp_rw [he]; exact Claim.csmul (correction_bill h ht) _
end YM.RegulatorIR.Uniform.Batch
