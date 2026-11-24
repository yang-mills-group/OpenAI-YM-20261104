import YM.RegulatorIR.Ledger.Recovery

/-! Finite unsoftening rule, applied to terminal tree-fixed Gaussian and Haar
jets (tree-only variables held zero). Data as hypothesis of rate theorem;
provide independently in binding by the specified inversion-quotient geometry.
-/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Ledger.Sky
open Budget Budget.Packet Budget.Layer Budget.Tuple Budget.Deck Budget.Tariff Uniform Uniform.Post Function Step Diagram Gradient Spatial
open scoped Topology ENNReal NNReal BigOperators Classical
variable {W:Type}{M:W→ℕ} {X Y:Page M→Type} (S:Sky X Y) (T:S.Accounts) {m:ℕ}(Z:T.Report m)
variable {k j : Choice M}{c₀ γ:ℝ}{p b q h α e r u:ℕ}{x: W→Room}{L:Meter W}{c:Flap M→ℝ≥0∞}

abbrev Rest (Y:Page M→Type) (w) := Y (Page.finallyW M w)
structure Margins (Y:Page M→Type) where
  endK : ∀ w,Layer (Rest Y w) (Rest Y w)
  haar : ∀ w,Orders (Rest Y w)

variable (F:Margins Y)
def landQ (u:ℕ)(w) := S.maximal.per u (Page.finallyW M w)
def stump (w:W):Orders (Rest Y w):= T.orb (Page.finallyW M w)+ F.haar w
-- S in parameters?
def vista (w:W)(e:ℕ):ℝ:= note (endHeat m (F.endK w) (logHeat (F.endK w) (S.stump T F w) true) (Z.point (Page.finallyW M w)) e 0)

structure Epoch (L:Meter W)(u p:ℕ):Prop where
 vane : Beam L (S.landQ u) F.endK
 sphere : ∀ i ≤ p,∀ j, Workday L (S.landQ u) fun w=> F.haar w i j
 positive : ∀ w,Vacuum (F.haar w)

variable (H:S.Epoch F L u p)(R:S.Registry T Z L u b q p α h c₀ γ x k c)
lemma combine_v (h:∀ w,Vacuum (T.orb w))(hp:∀ w,Vacuum (F.haar w)):∀ w, Vacuum (S.stump T F w) := by
 intro w e r he; by_cases hv:F.haar w e r=0
 · apply h _; intro hm ;apply he; change _+F.haar w e r=_; rw [hm,hv,add_zero]
 exact hp w e r hv

include R H
variable [∀ w,Fintype (Y w)]
lemma pack_end (he:e ≤ p) : Workday L (S.landQ u) fun w=> S.stump T F w e r := by
 apply Workday.add _ (H.sphere e he r)
 let hQ:= R.space
 have hhR :Workday (coverL M L) (S.census.per (u+b)) (fun w=> (S.maps w).deckSum (T.bulk w e r)):= S.census.deck_work (S.census.writes (R.space.space.bulk_price e he r) (by omega)) fun w=>R.space.space.bulk_deck w e r he
 have hp : Workday (coverL M L) (S.census.per (u+b)) (fun w=>T.orb w e r):=by
   by_cases h:0<r
   · have hf:= Claim.submits (S.confined T R.space (S.soften R.light (by omega)).lead e he r h) (Poly.oneQ ..)
     convert Workday.add hf hhR using 1; ext1 w; unfold Accounts.change; rw [sub_add_cancel]
   have hh:r=0:= by omega
   subst r
   exact ⟨_,Poly.zeroQ _,fun _ i=>Fin.elim0 i⟩
 obtain ⟨f,hf,Hf⟩:= hp.us (Page.finallyW M)
 refine ⟨_,hf,fun w i z=>?_⟩
 let j:= Page.finallyW M w
 apply le_trans _ (Hf w i z)
 refine quota_mono _ (fun y : Hold i z=> Tariff.diam_mono ?_ _)
 intro x y
 let d:= Spatial.distance (S.P w) ((S.maps j).atO x) ((S.maps j).atO y)
 change amount (S.radius j) u d ≤ amount (S.l j) (u+b) d
 apply le_trans _ (moment_mono (S.hl j) (show u≤u+b from by omega) (show 0≤d from Spatial.distance_nonneg ..))
 have hv:0≤d:= Spatial.distance_nonneg ..; have hp':S.l j ≤ S.radius j:=le_max_right ..; have h₁:= S.hl j; unfold amount; gcongr

lemma sum_land (he:e≤p)(j:Choice M): Carry L (fun w=> ENNReal.ofReal (S.modifyErr h b γ j w)) fun w=> ‖S.vista T Z F w e - note (Z.point (Page.finallyW M w) e 0)‖ₑ := by
 let U:= fun w=> logHeat (F.endK w) (S.stump T F w) true
 let V:= fun w=> markHeat (F.endK w) (U w) (Z.point (Page.finallyW M w))
 let Q:= fun w=> S.markUp x u (Page.finallyW M w); let d w:= ENNReal.ofReal (S.modifyErr h b γ j w)
 have ht w k r: U w k 0 r=0:= Classical.byContradiction fun h=> lt_irrefl 0 (heated_cap _ _ (S.combine_v T F (T.cap_o R.space.prim.grade) H.positive w) true 0 r k h).1
 have hc (i): Claim L Q d fun w=> V w (i+1) e 0:= Claim.total_mark (K:=F.endK) _ H.vane (fun p hp r k _=> Workday.hot (fun v hv s=> pack_end S T Z F H R (r:=s) hv) H.vane _ _ _ _ hp) ht (fun _ hp _ hr=> S.last_remainder T Z R hp hr) _ _ _ he (by omega)
 let C (w:W):=∑ i∈Finset.range (m+3*e), V w (i+1) e 0
 have he': Claim L Q d C := Claim.sum (L:=L) (fun i w=> V w (i+1) e 0) _ (fun i _=>hc i)
 apply Carry.mono he'; intro w; change ‖S.vista _ _ _ _ _ -_‖ₑ≤markQ (Q w) (C w)
 rw [vista,endHeat,Uniform.first_payment,markHeat_first,quotaNote]
 let g:= Z.point (Page.finallyW M w) e 0
 change ‖note (g+ C w)-note g‖ₑ ≤ _; rw [show note _ = note g + note (C w) from rfl,add_sub_cancel_left]

/-- Quantitative finite-top IR *terminal operation* compared to stopped cover
operation at j. Endpoint evaluated coefficientwise. Neither is a limit in its
definition. -/
theorem terminates (he:e ≤ p)(hj:k.age≤j.age): Carry L (fun w=> ENNReal.ofReal (S.modifyErr h b γ j w)) fun w=> ‖S.vista T Z F w e-note (Z.main (j.choose w) e 0)‖ₑ := by
 apply Carry.mono (Carry.add (S.sum_land T Z F H R he j) (S.last_gap T Z R he hj)); intro w
 apply le_trans _ (enorm_add_le (S.vista T Z F w e-note (Z.point (Page.finallyW M w) e 0)) (_-note (Z.main (j.choose w) e 0)))
 exact le_of_eq (congr_arg (enorm (E:=ℝ)) (by abel))
end YM.RegulatorIR.Ledger.Sky
