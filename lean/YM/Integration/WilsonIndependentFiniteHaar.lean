import YM.Integration.WilsonIndependentFreshTerminal
import YM.RegulatorIR.Ledger.Terminal

/-! The final normalized finite Gaussian and tree-gauge Haar integration. Its
positive-rank wage is homogeneous in the captured source, including finite
subrosters of a summable group programme. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentFiniteHaar
open RegulatorIR RegulatorIR.Ledger RegulatorIR.Ledger.Sky
open Budget Budget.Packet Budget.Layer Budget.Tuple Budget.Deck Budget.Tariff Uniform Uniform.Post Function Step Diagram Gradient Spatial
open scoped Topology ENNReal NNReal BigOperators Classical
variable {W:Type}{M:W→ℕ} {X Y:Page M→Type} (S:Sky X Y) (T:S.Accounts) {m:ℕ}(Z:T.Report m)
variable {p u e r : ℕ} {L : Meter W} {x : W → Room} {d : W → ℝ≥0∞}
  (F : Margins Y) (H : S.Epoch F L u p) [∀ w, Fintype (Y w)]

include H in
theorem original (vac : ∀ w, Vacuum (T.orb (Page.finallyW M w)))
    (quiet : ∀ e, e ≤ p → ∀ r, Workday L (S.landQ u)
      (fun w => S.stump T F w e r))
    (salary : ∀ a, a ≤ p → ∀ s, 0 < s →
      Claim L (fun w => S.markUp x u (Page.finallyW M w)) d
        (fun w => Z.point (Page.finallyW M w) a s))
    (he : e ≤ p) : Carry L d (fun w => ‖S.vista T Z F w e -
      note (Z.point (Page.finallyW M w) e 0)‖ₑ) := by
 let U:= fun w=> logHeat (F.endK w) (S.stump T F w) true
 let V:= fun w=> markHeat (F.endK w) (U w) (Z.point (Page.finallyW M w))
 let Q:= fun w=> S.markUp x u (Page.finallyW M w)
 have normalized (w : W) : Vacuum (S.stump T F w) := by
   intro a r used
   by_cases zero : F.haar w a r = 0
   · apply vac w
     intro absent
     apply used
     change _ + F.haar w a r = 0
     rw [absent,zero,add_zero]
   · exact H.positive w a r zero
 have ht w k r : U w k 0 r=0 := Classical.byContradiction fun hit =>
   lt_irrefl 0 (heated_cap _ _ (normalized w) true 0 r k hit).1
 have hc (i): Claim L Q d fun w=> V w (i+1) e 0:= Claim.total_mark (K:=F.endK) _ H.vane (fun p hp r k _=> Workday.hot (fun v hv s=> quiet v hv s) H.vane _ _ _ _ hp) ht (fun _ hp _ hr=> salary _ hp _ hr) _ _ _ he (by omega)
 let C (w:W):=∑ i∈Finset.range (m+3*e), V w (i+1) e 0
 have he': Claim L Q d C := Claim.sum (L:=L) (fun i w=> V w (i+1) e 0) _ (fun i _=>hc i)
 apply Carry.mono he'; intro w; change ‖S.vista _ _ _ _ _ -_‖ₑ≤ markQ (Q w) (C w)
 rw [vista,endHeat,Uniform.first_payment,markHeat_first,quotaNote]
 let g:= Z.point (Page.finallyW M w) e 0
 change ‖note (g+ C w)-note g‖ₑ ≤ _; rw [show note _ = note g + note (C w) from rfl,add_sub_cancel_left]

end YM.Integration.WilsonIndependentFiniteHaar
