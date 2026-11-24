import YM.LocalLTE.River.Wheel
/-!
# Conservation under charged camera pans/Bar

Use only the actual lay of lands. For probing the resulting exhibition.
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.River
open Function Filter Lattice Wilson RG Source Labels Extra.Histories Bid
open LocalLTE.Vinca LocalLTE.FrameBox FrameBox.Hall AnalyticBridge VerifiedReset Collection Price PhysicalNext.Repeat Blush
open Push Local Planned.GuardedAtom Motion
open Finset MeasureTheory
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{n κ:Side}{p:BudgetPoint}{d:ℕ}{F:Labels.Frame G d}{A:Hol G}{D:SectionData F}{R:Rep G n}{k v a u u' s t e x y z:ℝ}{m ℓ j:ℕ}{i:Site n}
local notation "Xp"=> Config G n→ℂ
open Next.Foundations Push.AbsoluteSums Animals
variable {L:Support n}
set_option quotPrecheck false
variable (r:Extra.Histories.Motion)(S:R.activities.Moves r.1 0)
local notation "q"=> turnSites r.1 (0:Site n)
local notation "rp"=> rotationP F R.p.order R.p.power
local notation "P'" P=> audition (z:=r) S P
variable {P Q:Coefficient F n}
lemma reshape (i:ℕ): (P' P).support i=(P.support i).image q ∧ (P' P).regular i= dance r (P.regular i):=by
    rcases r with ⟨r,ri⟩; cases ri
    all_goals exact ⟨rfl,rfl⟩
lemma glide : Vinca.decrement (P' P) (P' Q) = P' (Vinca.decrement P Q):=by
    rcases r with ⟨r,ri⟩; cases ri
    · unfold audition; simp [Vinca.decrement,reorient]; exact ⟨rfl,rfl⟩
    unfold audition; simp [Vinca.decrement, reorient,barAll]; constructor<;> funext i v<;> simp
lemma pitch (h:Exhibition D k ℓ m A R P Q s t e)(hD:D.Sound A)(hr:ConnectedActivityE6.Reliable G k v)(hn:2≤ n.val): Exhibition D k ℓ m A R (P' P) (P' Q) s (rp*t) (rp*e):=by
    have hY:= h.stock; obtain ⟨hx,hV,hQ,hx'⟩:= audition_receipt r S hn hD h.format (h.stock.bill h.fee.divisor)
    obtain ⟨hx₁,hP,hQ',h'⟩:= audition_receipt r S hn hD h.trade h.fee
    rw [← glide r S] at hx₁ hP hQ' h'
    have hC: 1 ≤ rp:= rotation_one ..
    have hh_:0≤e:= h.fee.first
    have hp (v:F.Coeff){x:ℝ}(h:F.coeffSize v ≤ x): F.coeffSize (Motion.patch F r v) ≤ rp*x:= (patch_cost ..).trans (mul_le_mul (rotation_price .. |>.2) h (Work.G08.size_nonneg ..) (zero_le_one.trans hC))
    refine ⟨⟨hx.symm ▸ hp _ hY.principal, ?_,?_⟩,hV,funext fun i=> ?_,hP, tabWeaken hQ' (mul_le_mul_of_nonneg_right (rotation_price ..|>.1) hh_) (le_mul_of_one_le_left hh_ hC),hx₁.symm ▸ hp _ h.canon⟩ -- rewriting term layout tactic issues.
    · obtain ⟨β,hB,hf⟩:= hY.regular
      let t i:= rp*β i; have hi(i): Canvas D k ℓ m R.p ((P' Q).support i) ((P' Q).regular i) (t i):=by rw [(reshape r S _).1,(reshape r S _).2]; exact Canvas.orbit r (hf _) (h.format.smooth i) hD hr
      have ht i : R.p.mass ((P' Q).support i) (t i)= rp*(R.p.mass (Q.support i) (β i)):=by rw [(reshape r S _).1]; unfold BudgetPoint.mass; rw [cover_map _ (turn_sep r.1 0)]; unfold t; ring
      refine ⟨t,?_,hi⟩; simp_rw [ht]; exact Local.sumBudget_mul_left hB (zero_le_one.trans hC)
    · unfold audition; split_ifs with h' -- in goal
      · simp [reorient,barAll,hY.forced];rfl -- maybe congr
      simp [reorient,hY.forced]; rfl
    rw [(reshape r S _).1,(reshape r S _).1,h.layout]
end YM.LocalLTE.River
