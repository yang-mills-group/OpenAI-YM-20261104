import YM.RegulatorIR.Cluster.Access
import YM.RegulatorIR.Ledger.Terminal

/-! ζ-discrepancy correlation variant. Can use even without a terminal
scale power price for λ_j, as long as epoch costs paid. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Cluster
open Function Set Budget Budget.Packet Budget.Layer Budget.Tuple Budget.Deck Budget.Tariff Uniform Gradient Step Diagram Ledger Ledger.Sky Ledger.Sky.Accounts Collapsed ENNReal
open scoped ENNReal NNReal Topology BigOperators Classical
variable {W I Z: Type}{M:W→ℕ} {X Y:Page M→Type} (S: Sky X Y)(T:S.Accounts)
  {p e a α u r b n q K h:ℕ}{L:Meter W} {k: Choice M} {f:W→ℝ≥0∞}{c:Flap M→ℝ≥0∞}{x:W→Room}{γ c₀:ℝ}
variable (R:T.Report a) (H:S.Registry T R L u b q p α h c₀ γ x k c)

include H
private def last (M: W→ℕ):Choice M := ⟨M,le_rfl⟩
lemma savours (hU:S.Preserved T R f K p k x (u+b+b) L) (ht:∀ w,f w≠⊤) (he:e≤p) : Claim L (fun w=> S.coverQ x (u+b+b) (Page.finallyW M w)) f (fun w=> R.main (Page.finallyW M w) e r):=by
 let j:=last M
 have hx:= S.appear T R H.light hU H.consent H.sanctity ht; have hb:=S.warmer H.light
 have hk : k.age ≤ j.age:=k.young
 have h' (w:W): ticket (S.softnessWeight γ) f (k.choose w)= f w:=by rw [ticket, softnessWeight, H.light.ref_mesh]; simp; rfl
 cases r with
 | zero=>
   have hp: Claim L (fun w=>S.coverQ x (u+b+b) (k.choose w)) f fun w=>R.main (k.choose w) e 0:= S.prevails T R H.light hU he
   have hv := S.marled T R H.space.prim H.space.space hb hx (by omega) (j:=k) le_rfl he
   apply Carry.mono (Carry.add (Carry.charge hv (Carry.mono (Carry.unit ..) (fun w=>(h' w).le))) hp);intro w; dsimp only;rw [quotaNote,quotaNote]
   exact (by nth_rw 1 [← sub_add_cancel (note (R.main (Page.finallyW M w) e 0)) (note (R.main (k.choose w) e 0))]; exact enorm_add_le ..)
 | succ r=>
   apply Carry.charge (S.success T R H.space.prim H.space.space hb hx (by omega) hk he (show 0<r+1 by omega))
   apply Carry.mono (Carry.unit ..); intro w
   change f _ * _ ≤ _; apply (mul_le_mul_right ?_ _).trans_eq (show f w*1=f w from mul_one _)
   rw [← show (1:ℝ≥0∞)⁻¹=1 by simp]; apply ENNReal.inv_le_inv.mpr; unfold softnessWeight
   have ht:S.l (k.choose w)≤ S.l (Page.finallyW M w):= S.tails (k.choose w); rw [H.light.ref_mesh] at ht
   exact ENNReal.ofReal_one.ge.trans (ENNReal.ofReal_le_ofReal (Real.one_le_rpow ht H.light.gleams.le))

def retainErr (S:Sky X Y)(u b:ℕ)(γ:ℝ)(v:W→ ℝ≥0∞)(w):= v w+ENNReal.ofReal (S.transferErr u b γ w)

variable [∀ w,Fintype (Y w)] (hU:S.Preserved T R f K p k x (u+b+b) L)(ht:∀ w,f w≠⊤)(he:e≤p)
include H
lemma offset (hU:S.Preserved T R f K p k x (u+b+b) L)(ht:∀ w,f w≠⊤) (he:e≤p): Claim L (fun w=> S.markUp x u (Page.finallyW M w)) (retainErr S h b γ f) (fun w=> R.point (Page.finallyW M w) e r):=by
 let A w:= Page.finallyW M w
 let P : Post (fun w=> X (A w)) (fun w=> Y (A w)):= ⟨S.P,S.hp,fun w=>S.radius (A w),fun _=>S.radius_pos _,fun w=>S.maps (A w)⟩
 have hh: Claim L (P.rooted x (u+b+b)) f (fun w=> R.main (A w) e r):= savours S T R H hU ht he
 have hg: Claim L (P.anchored x u) (retainErr S h b γ f) fun w=> (S.maps (A w)).scroll (R.main (A w) e r):= Carry.charge (P.folded_claim x (u:=u) (P.narrower x (b:=u+b+b) hh (by omega))) (Carry.mono (Carry.unit ..) (fun _=>le_add_right le_rfl))
 have hx: Claim L (P.anchored x u) (fun w=> ENNReal.ofReal (S.transferErr h b γ w)) fun w=> R.deviation (A w) e r:= Claim.us (S.travel_budget T R H he) A
 have hp: Claim L (P.anchored x u) (retainErr S h b γ f) fun w=> R.point (A w) e r:=by
    have hc: Claim L (P.anchored x u) (retainErr S h b γ f) fun w=> R.deviation (A w) e r:=Carry.charge hx (Carry.mono (Carry.unit ..) (fun _=>le_add_left le_rfl))
    convert hc.add hg using 1; ext1 w; unfold Report.deviation; rw [sub_add_cancel]
 exact hp
include hU ht
lemma there (F:Margins Y)(C:S.Epoch F L u p)(he:e ≤ p) : Carry L (retainErr S h b γ f) fun w=> ‖S.vista T R F w e‖ₑ:=by
 have hQ (s j w): logHeat (F.endK w) (S.stump T F w) true s 0 j=0:= Classical.byContradiction fun h=> lt_irrefl 0 (heated_cap _ _ (S.combine_v T F (T.cap_o H.space.prim.grade) C.positive w) true 0 j s h).1
 let X (w:W):= Page.finallyW M w
 let P (w:W):= S.markUp x u (X w)
 have hp: Folds p L (X:=fun w=> Y (X w)) P (retainErr S h b γ f) (fun w=> R.point (X w)):=fun i hi j=> offset S T R H hU ht hi
 have hh: Claim L P (retainErr S h b γ f) fun w=> endHeat a (F.endK w) (logHeat (F.endK w) (S.stump T F w) true) (R.point (X w)) e 0:= stays_end (X:=fun w=>Y (X w)) F.endK hp C.vane (S.combine_v T F (T.cap_o H.space.prim.grade) C.positive) (fun i hi j=> S.pack_end T R F C H hi) true a _ he _
 apply Carry.mono hh; intro i; dsimp only; rw [quotaNote]
 exact le_rfl
end YM.RegulatorIR.Cluster
