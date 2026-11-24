import YM.LocalLTE.Keels.Ability
/-! Reach the calibrated norm on changing actual probes. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Keels
open Function Filter Lattice Wilson RG Source Labels Extra.Histories Bid
open LocalLTE.Vinca LocalLTE.Drift LocalLTE.FrameBox AnalyticBridge VerifiedReset Collection Price PhysicalNext.Repeat Blush
open Push Local Planned.GuardedAtom LocalLTE.River YM.MergeProof
open Finset MeasureTheory
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{H:History G}{N m p:ℕ}{d:ℕ}(F:Labels.Frame G d)
open Work.G08
variable {a b e α κ η c v s:ℝ}{k ℓ:ℕ}
local notation "Ψ"=> F.Coeff
local notation "K"=> F.coeffSize
variable (D:SectionData F) (B: Hol G)
section
variable {n:Side}{R:Rep G n}{P Q U:Coefficient F n}
lemma mergerX (h: P.Format 0 B R)(hq:Q.Format 0 B R)(ht:Tab P 0 R κ v v)(hr:Tab Q 0 R κ s s)(hP:P.support=U.support)(hQ:Q.support=U.support)(hv:U.regular=P.regular+Q.regular)(hb:U.forced=P.forced+Q.forced): Tab U 0 R κ (v+s) (v+s):=by
   obtain ⟨a,ha,hV⟩:=ht.regular; obtain ⟨b,hx,hZ⟩:=hr.regular
   obtain ⟨j,hj,hA⟩:=ht.forced; obtain ⟨k,hk,hB⟩:=hr.forced; have hΓ:= add_nonneg ht.first hr.first
   refine ⟨ht.divisor,hΓ,hΓ,?_,?_⟩
   · rw [hP] at ha hV; rw [hQ] at hx hZ
     refine ⟨a+b, ?_, fun i=> ?_⟩; swap
     · rw [hv]; exact Next.Foundations.bound_add (hP ▸ h.smooth i) (hQ ▸ hq.smooth i) (hV i) (hZ i)
     simpa only [BudgetPoint.mass,Pi.add_apply, mul_add] using! Local.sumBudget_add ha hx
   rw [hb]; refine ⟨j+k, ?_,fun i=>⟨add_nonneg (hA i|>.1) (hB i|>.1), fun U=> (norm_add_le _ _).trans (add_le_add (hA i|>.2 U) (hB i|>.2 U))⟩⟩
   simpa only [BudgetPoint.mass, Pi.add_apply, mul_add] using! Local.sumBudget_add hj hk
end
local notation "δ" => Real.sqrt (H.levels.clock.forcedAllowance m)
local notation "T" => H.rep N p m
local notation "X" => H.S.side m p
variable (P': F.Coeff→ Coefficient F (H.S.side m p)) (W:Voice F H p m) (h:Heard D H N p B m W)
set_option quotPrecheck false
local notation "G₀"=> H.levels.params m |>.columns
variable (x y: F.Coeff)
local notation "U" x=> W.plays x
local notation "Y0"=> W.index
local notation "Q"=> (P' y)
local notation "Qp"=> (decrement (U y) Q)
local notation "Qx"=> (decrement (U x) Q)
local notation "Qz"=> (U (x-y))
local notation "r"=> (H.levels.params m).columns
-- invoice after normalization.Sensor.Field.b.Total.As
include h
lemma remark (ht: Exhibition D α ℓ k B (H.rep N p m) (W.plays y) (P' y) δ a b) : let f:= K ((Qz).x); let t:= b+(r*f); Exhibition D α ℓ k B T (U x) Q δ a t:=by
    intro f t
    have hV := h.earns (x-y)
    have hw: 0 ≤ r:=zero_le_one.trans (H.levels.params m).columns_ge
    have hs: Tab (Qz) 0 T δ (r*f) (r*f):=by
        obtain ⟨s,e,hs,he,hp,hq,hP,hQ⟩:=hV.2; have hy: s+e ≤ r*f:= (by unfold f; rw [h.currents]; exact hp.trans ((h.cone (x-y)).trans (mul_le_mul_of_nonneg_left (Work.G08.size_core ..) hw)))
        exact River.tabWeaken (show Tab _ _ _ _ _ _ from (⟨hq,hs,he,hP,hQ⟩:Tab (Qz) 0 T δ s e)) ((le_add_of_nonneg_right he).trans hy) ((le_add_of_nonneg_left hs).trans hy)
    have hX(u v:F.Coeff): (W.plays u).support=(W.plays v).support:= (h.book.tags u).trans (h.book.tags v).symm
    have hh :(W.plays x).support =(Q).support:=(hX x y).trans ht.layout
    have hΛ : (Qx).x=(Qp).x+(Qz).x:=by change (W.plays x).x-(Q).x =(W.plays y).x-(Q).x+_; simp_rw [h.currents,map_sub];abel
    refine ⟨ht.stock,ht.format,hh,River.offFormat (h.earns x|>.1) ht.format ht.stock.forced hh, mergerX F B ht.trade hV.1 ht.fee hs (hX y x) (hX (x-y) x) ?_ ?_,?_⟩
    · have hp := h.book.reg.map_add y (x-y); change (W.plays (y+(x-y))).regular = _ at hp; change (W.plays x).regular-_=_; rw [show y+(x-y)=x from by abel] at hp -- edit identity
      rw [hp]; change (W.plays y).regular + _ -_= (W.plays y).regular - _ + _; abel
    · have hp:= h.book.f.map_add y (x-y); change (W.plays (y+(x-y))).forced = _ at hp; change (W.plays x).forced-_=_; rw [show y+(x-y)=x from by abel] at hp
      rw [hp]; change (W.plays y).forced + _ -_= (W.plays y).forced - _ + _;abel
    rw [hΛ]; exact (Size.add ..).trans (add_le_add ht.canon (le_mul_of_one_le_left (Work.G08.size_nonneg ..) (H.levels.params m).columns_ge))
end YM.LocalLTE.Keels
