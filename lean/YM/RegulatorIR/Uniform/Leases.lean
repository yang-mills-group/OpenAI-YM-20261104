import YM.RegulatorIR.Uniform.Periodic

/-! Covariance budgets and singular image counts need different radii than
position-source tariffs at fine UV scales. Also elementary rate/reindex tools.
-/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Uniform
open Budget Spatial Motion Budget.Packet Budget.Deck Budget.Tuple Budget.Tariff Diagram Function
open scoped Topology ENNReal NNReal BigOperators Classical
variable {W Z:Type} {X Y:W→Type} {L:Meter W}

def Meter.us (f:Z→W)(L:Meter W) : Meter Z := ⟨L.val ∘ f,fun _=> L.above _,fun _=> L.below _⟩
lemma Poly.us {g: W→ℝ≥0∞} (h:Poly L g)(f: Z→W): Poly (L.us f) (fun z=>g (f z)):=by obtain ⟨c,p,hc,H⟩:=h; exact ⟨c,p,hc,fun _=> H _⟩
lemma Carry.us {g v: W→ℝ≥0∞}(h:Carry L v g)(f:Z→W): Carry (L.us f) (fun z=>v (f z)) fun z=>g (f z):= by obtain ⟨c,hc,H⟩:=h; exact ⟨_,hc.us f,fun _=>H _⟩
lemma Workday.us {A:(w:W)→Tariff (X w)}{r:ℕ}{T:(w:W)→Packet (X w) r}(h:Workday L A T)(f:Z→W): Workday (L.us f) (fun z=> A (f z)) (fun z=>T (f z)) := by obtain ⟨c,hc,H⟩:=h; exact ⟨_,hc.us f,fun _=>H _⟩
lemma Beam.us {A:(w:W)→Tariff (X w)}{T:(w:W)→Layer (X w) (X w)}(h:Beam L A T)(f:Z→W): Beam (L.us f) (fun z=> A (f z)) (fun z=> T (f z)) := by obtain ⟨c,hc,H⟩:=h; exact ⟨_,hc.us f,fun _=>H _⟩
lemma Claim.us {A:(w:W)→Tariff (X w)}{B:(w:W)→Premium (A w)}{r:ℕ}{T:(w:W)→Packet (X w) r}{v:W→ℝ≥0∞}(h:Claim L B v T)(f:Z→W): Claim (L.us f) (fun z=> B (f z)) (fun z=> v (f z)) (fun z=>T (f z)) := Carry.us h f

namespace Post
variable {M : Post X Y} {v l: W→ℝ} (hl: ∀ w,0<l w){x:W→Room}{u b e r:ℕ}

def lease (M:Post X Y)(l:W→ℝ)(hl:∀ w,0<l w):Post X Y:={ M with length:=l,spacing:=hl }
variable (he:M.length ≤ l)
private lemma budget {d e l:ℝ}(h:0<l)(hp:l≤d)(hv:0≤e): amount d u e ≤ amount l u e:=by unfold amount; gcongr
include he
lemma beam_fewer {K: ∀ w,Layer (X w) (X w)}(H: Beam L (M.cone u) K): Beam L ((M.lease l hl).cone u) K := by
 obtain ⟨f,hf,H⟩:=H
 have hz w (x y:X w): ((M.lease l hl).cone u w).road x y ≤ (M.cone u w).road x y:= budget (M.spacing ..) (he w) dist_nonneg
 exact ⟨_,hf,fun w=>⟨Layer.row_mono (hz w) (H w).1,Layer.row_mono (hz w) (H w).2⟩⟩
lemma work_fewer {T:(w:W)→Packet (X w) r}(H:Workday L (M.cone u) T): Workday L ((M.lease l hl).cone u) T:=by
 obtain ⟨f,hf,H⟩:=H
 have hh w (x:Tuple (X w) r): ((M.lease l hl).cone u w).diameter x ≤ (M.cone u w).diameter x:=Tariff.diam_mono (fun _ _=>budget (M.spacing w) (he w) dist_nonneg) _
 exact ⟨_,hf,fun w i x=>(quota_mono (fun z:Hold i x=>T w z.val) (fun z=> hh w z.val)).trans (H w i x)⟩
lemma place_fewer (w) (T:Packet (Y w) r): markQ ((M.lease l hl).pear u w) T ≤ markQ (M.pear u w) T:= quota_mono T fun _=> Premium.prem_mono (fun _ _=>budget (M.spacing w) (he w) (distance_nonneg ..)) (fun _=>budget (M.spacing w) (he w) (singular_nonneg ..)) _
lemma orb_fewer (w) (T:Packet (Y w) r): markQ ((M.lease l hl).anchored x u w) T ≤ markQ (M.anchored x u w) T := quota_mono T fun _=> Premium.prem_mono (fun _ _=>budget (M.spacing w) (he w) (distance_nonneg ..)) (fun _=>budget (M.spacing w) (he w) (distance_nonneg ..)) _
lemma on_fewer (w) (T:Packet (X w) r): markQ ((M.lease l hl).rooted x u w) T ≤ markQ (M.rooted x u w) T := quota_mono T fun _=> Premium.prem_mono (fun _ _=>budget (M.spacing w) (he w) dist_nonneg) (fun _=>budget (M.spacing w) (he w) dist_nonneg) _
lemma fewer {T:(w:W)→Packet (Y w) r}{v:W→ℝ≥0∞}(h:Claim L (M.pear u) v T) : Claim L ((M.lease l hl).pear u) v T:= Carry.mono h fun w=> place_fewer hl he w _
lemma few_orb {T:(w:W)→Packet (Y w) r}{v:W→ℝ≥0∞}(h:Claim L (M.anchored x u) v T) : Claim L ((M.lease l hl).anchored x u) v T:= Carry.mono h fun w=> orb_fewer hl he w _
lemma few_cover {T:(w:W)→Packet (X w) r}{v:W→ℝ≥0∞}(h:Claim L (M.rooted x u) v T) : Claim L ((M.lease l hl).rooted x u) v T:= Carry.mono h fun w=> on_fewer hl he w _
end Post
end YM.RegulatorIR.Uniform
