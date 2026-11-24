import YM.RegulatorIR.Ledger.Energy

/-! Scalar cover estimate with inverse length gain since scale j. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Ledger.Sky
open Budget Spatial Budget.Packet Budget.Tariff Budget.Layer Budget.Tuple Budget.Deck Uniform Uniform.Post Function Step Diagram Gradient ENNReal
open scoped Topology ENNReal NNReal BigOperators Classical
variable {W: Type} {M:W→ℕ} {X Y:Page M→Type} (S:Sky X Y) (T:S.Accounts)
variable {r e p u b m:ℕ}{c : Flap M→ℝ≥0∞}{d:Page M→ℝ≥0∞}{x:W→Room}{s:W→ℝ≥0∞}{L:Meter W}
variable (R:(w:Page M)→Orders (X w))

lemma quiet (w: Flap M): note (S.lifts.bump (fun w : Flap M=>R w.prev e 0) w) = note (R w.prev e 0):= by
 let P:=combine (S.maps w.prev) (S.maps w.next); let f:=firstChannel (S.maps w.prev) (S.maps w.next); let t:= lastChannel (S.maps w.prev) (S.maps w.next); let Z:= S.frames w
 let T:=offer f.native (R w.prev e 0)
 change (crop t.native (draft Z.driftL T)) Fin.elim0 = _
 rw [show draft Z.driftL T= T from ?_]; swap
 · change symmetry T=T
   unfold symmetry; simp; rfl
 change offer f.native (R w.prev e 0) (_:Tuple (X w.prev ⊕ X w.next) 0)=_
 rw [show acrossT t.native Fin.elim0=acrossT f.native (Fin.elim0:Tuple _ 0) from Subsingleton.elim ..,offer_eq]; rfl

variable {α:ℕ} (B:S.Primitive L p b)(N:S.Supplies T L p b)
   (G:S.Softness u L c d α)(I:S.Imprints T R u p m x d s α L)(hu:u ≤ b)

include B N G I hu
lemma coil (he:e ≤ p) : Carry (flapL M L) (fun w=> ticket d s w.prev) fun w=> ‖note (R w.next e 0)- note (R w.prev e 0)‖ₑ:=by
 have H := S.glides T R B N G I hu
 have hq:= S.pruned T R B N G I hu (r:=0) (fun i j hi hj=> H i (by unfold Earlier at hi;omega) j hj) he
 apply Carry.mono hq
 intro w; dsimp only; rw [← S.quiet R w, quotaNote];exact le_rfl

lemma till (he:e ≤ p): Carry (coverL M L) (fun w=> ticket d s (Page.opening M w.bindW)) fun w=> ‖note (R w e 0)-note (R (Page.opening M w.bindW) e 0)‖ₑ:=by
 have H:= S.coil T R B N G I hu he
 have hT:∀ i : Page M, ticket d s i≤ ticket d s (Page.opening M i.bindW):=by
    apply Page.proves
    · exact fun _=>le_rfl
    intro w ih; apply le_trans _ ih; exact mul_le_mul_right (ENNReal.inv_le_inv.mpr (G.warm w)) (s w.volW)
 apply turning (v:=fun w=> ticket d s (Page.opening M w)) _ (Carry.charge H (Carry.mono (Carry.unit ..) (fun w=>hT w.prev))) ?_ B.depth ?_
 · intro w; let P:= note (R (Page.opening M w.volW) e 0); let X₀:=note (R w.prev e 0); let X₁:= note (R w.next e 0)
   change ‖X₁-P‖ₑ ≤ ‖X₀-P‖ₑ + ‖X₁-X₀‖ₑ; rw [show X₁-P=(X₀-P)+(X₁-X₀) by abel]; exact enorm_add_le ..
 exact Carry.mono (Carry.zeroQ _) fun w=>by change ‖note (R (Page.opening M w) e 0)-note (R (Page.opening M w) e 0)‖ₑ≤_;simp
end YM.RegulatorIR.Ledger.Sky
