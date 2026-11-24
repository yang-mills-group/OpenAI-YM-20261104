import YM.RegulatorIR.Cluster.Minus
import YM.RegulatorIR.Ledger.Hold

/-! Keep Λ families and Ward costs distinct from singular-volume and global
IR costs. Fine side at fixed geometry caps. Record exact hypotheses. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Cluster
open Function Set Budget Budget.Packet Budget.Layer Budget.Tuple Budget.Tariff Uniform Gradient Step Diagram Ledger Ledger.Sky Ledger.Sky.Accounts Collapsed
open scoped ENNReal NNReal Topology BigOperators Classical
variable {W I Z:Type}{M:W→ℕ}{X Y:Page M→Type}
  (S:Sky X Y)(T:S.Accounts){p e u n b a:ℕ} {L: Meter W}

-- Layout adapter. Requires row primal & additional symmetry (Beam work).
def Vac (w: Flap M):= T.bulk w.prev
structure Milieu (u p:ℕ)(L:Meter W): Prop where
 core : S.Primitive L p u
 sky : S.Supplies T L p u
 align : ∀ w,gradedSymmetric (now S.lifts (Vac S T) w)
 mirror : ∀ w i j,S.lifts.lineL w i j=S.lifts.lineL w j i

namespace Milieu
variable {S T}(G:Milieu S T u p L)
include G
lemma fund (hb:b≤u): Fund p (flapL M L) S.high (Zone S.lifts) b (now S.lifts (Vac S T)) S.lifts.lineL:=
 ⟨fun _=>GridStep.joint_vac_shape _ (T.cap_b G.core.grade _) (G.core.grade _), fun i h j=> S.ceilingRoom.writes (S.lifts.fine_work (T.deposit G.sky i h j) (G.core.add_cost i h j)) hb, S.ceilingRoom.descent G.core.line hb,G.align,G.mirror⟩
lemma solid (hb:b≤u): Beam (flapL M L) (home S.high (Zone S.lifts) b) S.lifts.forecast:=S.ceilingRoom.descent G.core.drift hb
end Milieu

variable (J:Composite I)(A:I→(w:Page M)→ Orders (X w))

def chargeC (J:Composite I)(A:I→(w:Page M)→ Orders (X w)) (i): Orders (X i):= J.product fun j=> A j i
abbrev Stations (v : Page M) := (S.maps v).pos
abbrev island (Y:I→ W→Set Room)(j:I)(v:Page M):= Y j v.bindW
abbrev merits (v:Page M→ℝ≥0∞)(w:Flap M):= v w.prev
variable {S T A J}
variable {v:I→ Page M→ℝ≥0∞}{D:I→W→Set Room}{d: W→ℝ}{m:I→ℕ}

def TrainWay (S:Sky X Y)(J:Composite I)(A:I→(w:Page M)→ Orders (X w)) (p:ℕ):Prop:= ∀ i, J.In i→∀ w e,e ≤ p → (S.sight w).Way (A i w.prev) e
structure Crown (L:Meter W)(S:Sky X Y)(T:S.Accounts)(A:I→(w:Page M)→Orders (X w))(p u:ℕ) (D:I→ W→ Set Room)(v:I→Page M→ℝ≥0∞)(d:W→ℝ)(m:I→ℕ)(J:Composite I):Prop where
  shape : Composite.Shaped (coverL M L) S.hl (Stations S) (island D) v (fun w=> d w.bindW) u p A m J
  -- Way at all inputs. Scalar invariance applies after interpreting gauge
  follows : TrainWay S J A p
  steps : ∀ i, J.In i → ∀ w, (S.frames w).each (m i) (T.bulk w.prev) (A i w.prev)= A i w.next

namespace Crown
variable (B:Crown L S T A p u D v d m J)
include B
lemma folded : Composite.Shaped (flapL M L) S.high (Gate S.lifts) (fun i w=> island D i w.prev) (fun i w=>v i w.prev) (fun w=>d w.volW) u p (fun i w=> A i w.prev) m J := by
 have s:= B.shape
 refine ⟨?_,fun i hi w=>s.lit i hi _,fun i hi w=>s.shut i hi _,fun w=>s.apart w.prev, fun i hi w=> s.valence i hi _, fun i hi w=>s.symmetric i hi _, fun i hi w=> s.price i hi _, fun w=> s.nonneg w.prev⟩
 intro i hi e he r; apply Carry.mono (Carry.us (s.width i hi e he r) Flap.prev); intro w;apply quota_mono; intro z; exact finer (S.hl _) (S.climb w) (D i w.volW) (Stations S w.prev) z
lemma bills (i) (hi:J.In i)(w): Bill (A i w) p:=((B.shape.width i hi).pay (B.shape.price i hi) w)
lemma product_price (w): Bill (chargeC J A w) p:= B.shape.gather.pay (fun v=> (B.shape.estate_shape v).2.2) w
lemma continuity_at (w:Flap M) : solo S.lifts (Vac S T) J m (fun i w=> A i w.prev) w=chargeC J A w.next:= by
 apply path B.steps w
where
 path (hh:∀ i,J.In i→∀ w:Flap M,(S.frames w).each (m i) (T.bulk w.prev) (A i w.prev)= A i w.next) (w:Flap M): J.product (fun i=>(S.frames w).each (m i) (T.bulk w.prev) (A i w.prev))= chargeC J A w.next := by
   -- induction remove B
   clear B
   induction J with
   | atom i=> exact hh i rfl w
   | pair P Q ih ih'=> exact congr_arg₂ accord (ih fun i hi=> hh i (Or.inl hi)) (ih' fun i hi=>hh i (Or.inr hi))
omit B in
private lemma ways_pair {X Y U V: Type}{P:ℝ}{F:Deck P X U}{C:Deck P Y V} {Q:GridStep F C}(B:Strip Q){T S:Orders X}(he:e ≤ p) (h₁:CostRow B.straight p)(h₂:CostRow B.space p) (hA:Bill T p)(hB:Bill S p)(hV:Ranks n T)(hW:Ranks b S)(ht:∀ i≤p,B.Way T i) (hu:∀ i≤p,B.Way S i): B.Way (accord T S) e:= by
 unfold Strip.Way; rw [shot_product B.straight h₁ hA hB hV hW he, shot_product B.space h₂ hA hB hV hW he]; ext1 i; unfold accord;apply Finset.sum_congr rfl; intro j hj; have hv:= Finset.mem_antidiagonal.mp hj; rw [ht j.1 (by omega),hu j.2 (by omega)]

lemma ways (h:∀ w:Flap M,CostRow (S.sight w).straight p)(hh:∀ w:Flap M,CostRow (S.sight w).space p) : ∀ (w:Flap M) e,e≤p→ (S.sight w).Way (chargeC J A w.prev) e:=by
 induction J with
 | atom i=> intro w i' hi; exact B.follows i rfl w i' hi
 | pair P Q ih ih'=>
    have P': Crown L S T A p u D v d m P:=⟨B.shape.left,fun i hi=> B.follows i (Or.inl hi),fun i hi=> B.steps i (Or.inl hi)⟩
    have Q': Crown L S T A p u D v d m Q:=⟨B.shape.right,fun i hi=> B.follows i (Or.inr hi),fun i hi=> B.steps i (Or.inr hi)⟩
    intro w e he; exact ways_pair (S.sight w) he (h w) (hh w) (P'.product_price _) (Q'.product_price _) (P'.shape.graded w.prev).1 (Q'.shape.graded w.prev).1 (ih P' w) (ih' Q' w)
end Crown
end YM.RegulatorIR.Cluster
