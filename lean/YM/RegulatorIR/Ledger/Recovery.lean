import YM.RegulatorIR.Ledger.Period

/-! Family uniform terminal *input*, vacuum still counted only away from its
scalar. Terminal costs of conventional PT are paid in the next development. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Ledger.Sky
open Budget Budget.Packet Budget.Tariff Budget.Layer Budget.Tuple Budget.Deck Uniform Uniform.Post Function Step Diagram Gradient Spatial
open scoped Topology ENNReal NNReal BigOperators Classical
variable {W:Type}{M:W→ℕ}{X Y:Page M→Type} (S:Sky X Y) (T:S.Accounts) {m:ℕ}(Z:T.Report m)
variable {k j : Choice M}{c₀ γ:ℝ}{p b q h α e r u:ℕ}{x: W→Room}{L:Meter W}{c:Flap M→ℝ≥0∞}

/-- analytic inputs explicitly used in the transmission bounds. Product-level
`Preserved` is often itself a theorem target given just one-mark inputs. -/
structure Registry (L:Meter W)(u b q p α h:ℕ) (c₀ γ:ℝ)(x:W→Room)(k:Choice M)(c:Flap M→ℝ≥0∞) : Prop where
  space : S.Cosmos T (u+b) q p L
  light : S.Radiants L γ (u+b+b) α c k
  many : S.Preserved T Z 1 h p k x (u+b+b) L
  consent : ∀ w i,i≤ p → (S.sight w).Way (Z.main w.prev) i
  sanctity : ∀ w i j,i ≤ p → 0<j → j<α → Z.main w i j=0
  law : ∀ w i,i ≤ p → (S.sight w).WayO (Z.deviation w.prev) i
  bpay : 0<b
  turf : S.cushion c₀ x
  contained : 0<c₀
variable (R:S.Registry T Z L u b q p α h c₀ γ x k c)
include R
lemma heat_paid (he:e≤ p)(hr:0<r): Claim (flapL M L) (S.yard x (u+b+b)) (S.priceStep h γ k) (fun w=> Z.main w.prev e r):= S.weld T Z R.light R.space.prim R.many R.space.space (S.appear T Z R.light R.many R.consent R.sanctity fun _=> ENNReal.one_ne_top) (by omega) he hr

lemma travel_budget [∀ w,Fintype (Y w)] (he:e≤ p): Claim (coverL M L) (S.markUp x u) (fun w=> ENNReal.ofReal (S.transferErr h b γ w.bindW)) (fun w=> Z.deviation w e r):=by
 apply S.archive T Z (x:=x) (s:=fun w=> ENNReal.ofReal (S.transferErr h b γ w)) R.space (S.soften R.light (by omega)).lead (t:=S.priceStep h γ k) _ _ he r
 refine { data:=fun i hi r hr=> S.heat_paid T Z R hi hr, coin:= fun w=>?_, ticket:= S.covers_cost R.light R.turf R.contained R.bpay, ward:= R.law }
 unfold priceStep; split <;> finiteness

def coverEnd (w:W) := (S.maximal.cone u (Page.finallyW M w))
private def last (M : W→ℕ) : Choice M:=⟨M,le_rfl⟩
def modifyErr (h b:ℕ) (γ:ℝ) (j:Choice M) w:= S.transferErr h b γ w+(S.l (j.choose w)^γ)⁻¹
lemma last_remainder [∀ w,Fintype (Y w)] (he:e≤p)(hr:0<r):
 Claim L (fun w=>S.markUp x u (Page.finallyW M w)) (fun w=> ENNReal.ofReal (S.modifyErr h b γ j w)) (fun w=> Z.point (Page.finallyW M w) e r):=by
 let L':= S.transferErr h b γ
 let l:= last M
 have hG:= S.warmer R.light; let d:= S.softnessWeight γ
 have hv : Claim L (fun w=> S.coverQ x (u+b+b) (Page.finallyW M w)) (fun w=> ticket d 1 (Page.finallyW M w)) (fun w=> Z.main (Page.finallyW M w) e r):= S.success T Z R.space.prim R.space.space hG (S.appear T Z R.light R.many R.consent R.sanctity fun _=> ENNReal.one_ne_top) (by omega) (j:=l) k.young he hr
 have he': Carry L (fun w=> ENNReal.ofReal (S.modifyErr h b γ j w)) (fun w=> ticket d 1 (Page.finallyW M w)):= by
   apply Carry.mono (Carry.unit ..); intro w
   change 1*(ENNReal.ofReal (S.l (Page.finallyW M w)^γ))⁻¹ ≤ _
   have hz : S.l (j.choose w) ≤ S.l (Page.finallyW M w):= S.tails (j.choose w)
   have hh:= S.hl (j.choose w)
   rw [one_mul]
   calc
     _ ≤ (ENNReal.ofReal (S.l (j.choose w) ^ γ))⁻¹ := ENNReal.inv_le_inv.mpr (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow hh.le hz R.light.gleams.le))
     _ ≤ _ := by rw [← ENNReal.ofReal_inv_of_pos (by positivity)]; exact ENNReal.ofReal_le_ofReal (le_add_of_nonneg_left (S.transfer_pos w).le)
 have hα: Claim L (fun w=> S.markUp x u (Page.finallyW M w)) (fun w=> ENNReal.ofReal (S.modifyErr h b γ j w)) (fun w=> (S.maps (Page.finallyW M w)).scroll (Z.main (Page.finallyW M w) e r)):= by
   let ℓ:= Page.finallyW M; let X:= ℓ
   let P : Post (fun w=> _ ) (fun w=> _):=⟨S.P,S.hp,fun w=>S.radius (X w),fun w=>S.radius_pos (X w),fun w=>S.maps (Page.finallyW M w)⟩
   exact Carry.charge (P.folded_claim x (u:=u) (P.narrower x (b:=u+b+b) hv (by omega))) he'
 have hβ: Claim L (fun w=> S.markUp x u (Page.finallyW M w)) (fun w=> ENNReal.ofReal (S.modifyErr h b γ j w)) (fun w=> Z.deviation (Page.finallyW M w) e r):= by
   have h : Claim L (fun w=> S.markUp x u (Page.finallyW M w)) (fun w=> ENNReal.ofReal (S.transferErr h b γ w)) (fun w=> Z.deviation (Page.finallyW M w) e r):= Claim.us (S.travel_budget T Z R he) (Page.finallyW M)
   apply Carry.charge h; apply Carry.mono (Carry.unit ..); intro w
   apply ENNReal.ofReal_le_ofReal; unfold modifyErr; apply le_add_of_nonneg_right; have h:= S.hl (j.choose w); positivity
 convert Claim.add hβ hα using 1; ext1 w; unfold Accounts.Report.deviation; rw [sub_add_cancel]
omit R in
private lemma nothing {P:ℝ}{I J : Type}(D:Deck P I J)(T: Packet I 0): note (D.scroll T) = note T:= by
 unfold note Deck.scroll Stalk.collect
 let t : Stalk D.project Fin.elim0 := ⟨Fin.elim0,Subsingleton.elim ..⟩
 rw [tsum_eq_single t]; change D.dyed T Fin.elim0 = T Fin.elim0; simp [Deck.dyed,Deck.polish]
 exact fun b hb=>(hb (Subsingleton.elim ..)).elim
lemma last_gap [∀ w,Fintype (Y w)] (he:e ≤ p)(hj:k.age≤j.age):
 Carry L (fun w=> ENNReal.ofReal (S.modifyErr h b γ j w)) (fun w=> ‖note (Z.point (Page.finallyW M w) e 0)-note (Z.main (j.choose w) e 0)‖ₑ):=by
 let E:= S.modifyErr h b γ j
 let f w:= note (Z.point (Page.finallyW M w) e 0)
 let g w:= note (Z.main (Page.finallyW M w) e 0); let r w:= note (Z.main (j.choose w) e 0)
 have ht: Carry L (fun w=> ENNReal.ofReal (E w)) fun w=> ‖f w-g w‖ₑ:= by
   have hβ: Claim L (fun w=> S.markUp x u (Page.finallyW M w)) (fun w=> ENNReal.ofReal (S.transferErr h b γ w)) (fun w=> Z.deviation (Page.finallyW M w) e 0):= Claim.us (S.travel_budget (r:=0) T Z R he) (Page.finallyW M)
   apply Carry.charge (v:=fun w=> ENNReal.ofReal (S.transferErr h b γ w)); swap
   · apply Carry.mono (Carry.unit ..); intro w
     apply ENNReal.ofReal_le_ofReal; apply le_add_of_nonneg_right; have hp:= S.hl (j.choose w); positivity
   apply Carry.mono hβ; intro w; dsimp only; rw [quotaNote]; unfold g; rw [← nothing (S.maps _)]; exact le_rfl
 have hp : Carry L (fun w=> ENNReal.ofReal (E w)) fun w=> ‖g w-r w‖ₑ:= by
   apply Carry.charge (S.marled T Z R.space.prim R.space.space (S.warmer R.light) (S.appear T Z R.light R.many R.consent R.sanctity fun _=> ENNReal.one_ne_top) (by omega) hj he)
   apply Carry.mono (Carry.unit ..); intro w; change 1* (ENNReal.ofReal (S.l (j.choose w)^γ))⁻¹ ≤ _; rw [one_mul,← ENNReal.ofReal_inv_of_pos (Real.rpow_pos_of_pos (S.hl _) _)]; exact ENNReal.ofReal_le_ofReal (le_add_of_nonneg_left (S.transfer_pos w).le)
 apply Carry.mono (Carry.add ht hp); intro w; change ‖f w-r w‖ₑ ≤ ‖f w-g w‖ₑ + ‖g w-r w‖ₑ
 rw [show f w-r w= (f w-g w)+(g w-r w) by abel]; exact enorm_add_le ..
end YM.RegulatorIR.Ledger.Sky
