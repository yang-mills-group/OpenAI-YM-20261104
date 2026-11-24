import YM.Integration.WilsonOlderFreshGraphSingleShelf
import YM.QuadraticLocal.Campaign.Stencil

/-! The before-test one-name group salary itself makes the pupil a voter
on the booked school. The source may be the signed grouping of several
old ordinary faces. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshUnaryVoter
open Lattice Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Earn.Scene QuadraticLocal.Mentor AllOrder
open scoped Classical BigOperators

theorem original {G:Gauge}{n:Side}{P:Passport n Unit}{R:Census Unit}{ι α:Type}
    (X:ι→Row P R G α)(w:Unit→ℝ)(d p seats h:ℕ)(σ b:ℝ)
    (earned:Armada X w (fun _=>d) σ b p seats h)
    {stage vac shelf:ℕ} (book:p+1 ≤ stage)(docket:p+d≤Burn.horizon vac+2)
    (order:p ≤ shelf)(pole:d ≤ shelf):Cruise.Voter X σ p seats stage vac shelf:=by
  have low:=WilsonOlderFreshGraphSingleShelf.original X w d p seats h σ b earned
  refine ⟨fun i=>?_,low.quota,book,fun C=>?_⟩
  · have st:=(earned.purchases.usable i)
    refine ⟨earned.honor i,earned.purchases.spend i,st.1.trans order,?_⟩
    exact st.2 ▸ (low.crew (X i).mode).trans pole
  · rw [Press.tall X C (fun _=>d) earned.purchases.usable]
    exact (Nat.add_le_add_left (low.crew (Club.alliance X C)) p).trans docket

end YM.Integration.WilsonOlderFreshUnaryVoter
end
