import YM.RegulatorIR.Centered.Slice

/-! Intermediate comparison: formal terminal expectation vs formal soft
coefficient, with errors that permit scales P, λ_j, ε and the profiles and
field normalizations to be selected within the growing cap. Before binding
and before continuum. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Centered
open Topology Lattice MeasureTheory Set Metric Function Motion Spatial
open Budget Budget.Packet Budget.Tariff Budget.Layer Budget.Tuple Budget.Deck Uniform Uniform.Post Ledger Ledger.Sky Step Diagram Gradient
open scoped ENNReal NNReal BigOperators Classical
variable {W Z : Type} {M:W→ℕ}{X Y:Page M→Type}

abbrev plane (W: Type) := W × Room
def film (W:Type)(w:plane W): W:=w.1
def dwell (W:Type)(w:plane W):Room:= w.2
def court (P:ℝ):= cube (same (P/8)) (P/8)
lemma rotation {P:ℝ} (hp:0<P) (x:Room) (hx:x ∈ court P): (1/8:ℝ)*P ≤ Spatial.singular P x:=by
 let v:= nearest (P/2) x
 have h:= inside.mp hx (0:Axis)
 change P/8 ≤ x 0 ∧ x 0 < P/8+P/8 at h
 apply le_trans _ (norm_le_pi_norm (x-slide (P/2) v) 0)
 change _ ≤ ‖x 0-P/2*(v 0)‖; rw [Real.norm_eq_abs, le_abs]; rcases le_or_gt (v 0) 0 with he|he
 · left; have ht : ((v 0:ℤ):ℝ)≤0:= by exact_mod_cast he
   nlinarith
 right; have hv: (1:ℝ) ≤ (v 0:ℤ) := by exact_mod_cast (show (1:ℤ) ≤ v 0 from he)
 nlinarith

variable (S:Sky X Y) (T:S.Accounts)
def Outlook (T:S.Accounts)(m:ℕ) := (movie T (film W)).Report m
-- comparison estimates automatically apply to films with caps still common in w

variable {m:ℕ} (R:(movie T (film W)).Report m)
variable (F:Margins Y)

def outlook (i:plane W)(e:ℕ) :ℝ:= (album S (film W)).vista _ R (post F (film W)) i e

def medium (j: Choice M)(e:ℕ)(w:W) (x:Room) :ℝ := note (R.main ((spool j (film W)).choose (w,x)) e 0)
def diffuse (j:Choice M) (e:ℕ) (w:W):ℝ := let t:= S.l (j.choose w); weigh (same (-t/2)) t (medium S T R j e w)

def bright (e:ℕ) (w:W): ℝ := let P:= S.P w; weigh (same (P/8)) (P/8) (fun x=>outlook S T R F (w,x) e)

structure Seated (L: Meter W)(u b q p h α:ℕ)(γ:ℝ)(c:Flap M→ℝ≥0∞) (k: Choice M): Prop where
  space : S.Cosmos T (u+b) q p L
  detects : S.Epoch F L u p
  light : S.Radiants L γ (u+b+b) α c k
  bpay : 0 < b
  many : (album S (film W)).Preserved (movie T (film W)) R 1 h p (spool k (film W)) (dwell W) (u+b+b) (L.us (film W))
  consent : ∀ w i,i≤ p → ((album S (film W)).sight w).Way (R.main w.prev) i
  sanctity : ∀ w i j,i ≤ p → 0<j → j<α → R.main w i j=0
  law : ∀ w i,i ≤ p → ((album S (film W)).sight w).WayO (R.deviation w.prev) i

variable {e u b q p h α:ℕ}{γ:ℝ}{c:Flap M→ℝ≥0∞} {k j:Choice M}{L:Meter W}
variable (H: Seated S T R F L u b q p h α γ c k)
include H
abbrev Face (S:Sky X Y) := {i: plane W // dwell W i ∈ court (S.P (film W i))}
def introF (i : Face S):plane W:=i.val

lemma at_cube [∀ w,Fintype (Y w)] (he:e ≤ p)(hj:k.age≤ j.age): Carry (L.us (film W ∘ introF S)) (fun w:Face S=> ENNReal.ofReal (S.modifyErr h b γ j ((introF S w).1))) fun i=> ‖outlook S T R F (introF S i) e-medium S T R j e ((introF S i).1) (introF S i).2‖ₑ:=by
 let A:= album S (film W); let Z:= album A (introF S)
 let Y':= movie T (film W); let Z':= movie Y' (introF S)
 let R':= series R (introF S)
 let C:= fun w=>dwell W (introF S w)
 let C' (w:Flap _):= c (arrow (film W) M (arrow (introF S) (M ∘ film W) w))
 let L' := (L.us (film W)).us (introF S)
 have hx : Z.Registry Z' R' L' u b q p α h (1/8) γ C (spool (spool k (film W)) (introF S)) C':= by
   refine ⟨galaxy (introF S) (galaxy (film W) H.space),glow (introF S) (glow (film W) H.light), models (introF S) R H.many,fun w=> H.consent (arrow (introF S) (M ∘ film W) w),fun w=> H.sanctity (stages (introF S) _ w),fun w=> H.law (arrow (introF S) _ w), H.bpay, fun w=>rotation (Z.hp w) _ w.property, by norm_num⟩
 letI : ∀ i: Page ((M ∘ film W) ∘ introF S), Fintype (Y (stages (film W) M (stages (introF S) _ i))):= fun _=> inferInstance
 have hα:= Z.terminates Z' R' (post (post F (film W)) (introF S)) (show Z.Epoch (post (post F (film W)) (introF S)) L' u p from zest (introF S) (S:=album S (film W)) (post F (film W)) (zest (film W) F H.detects)) hx (j:=spool (spool j (film W)) (introF S)) he (fun w=> hj (film W (introF S w)))
 exact hα
lemma fading (he:e ≤ p)(hj:k.age≤j.age) : Poly (L.us (film W)) fun w:plane W=> ‖medium S T R j e w.1 w.2‖ₑ := by
 let B:= album S (film W); let f:= film W
 have hp := glow f H.light
 have hx:= B.appear _ R hp H.many H.consent H.sanctity fun _=> ENNReal.one_ne_top
 have he': Claim (L.us f) (fun w=> B.coverQ (dwell W) (u+b+b) ((spool k f).choose w)) 1 fun w=> R.main ((spool k f).choose w) e 0:= B.prevails _ R hp H.many he
 have hα: Carry (L.us f) 1 fun w:plane W => ‖medium S T R k e w.1 w.2‖ₑ:= by
    apply Carry.mono he'; intro w
    change ‖note (R.main _ e 0)‖ₑ≤markQ _ _; rw [quotaNote]
 let U:=galaxy f H.space
 let g(w:plane W):= medium S T R j e w.1 w.2; let v(w:plane W):= medium S T R k e w.1 w.2
 have hβ : Carry (L.us f) 1 fun w=> ‖g w-v w‖ₑ:= by
    apply Carry.charge (B.woven _ R U.prim U.space (warmer B hp) hx (by omega) (j:=spool j f) (fun w=> hj (f w)) he)
    apply Carry.mono (Carry.unit ..); intro w; change ticket _ 1 ((spool k f).choose w) ≤ 1; rw [ticket,softnessWeight,hp.ref_mesh]; simp
 apply Poly.mono (Carry.admit (Carry.add hβ hα) (Poly.oneQ _)); intro w
 apply le_trans _ (enorm_add_le (g w-v w) (v w)); rw [sub_add_cancel]
end YM.RegulatorIR.Centered
