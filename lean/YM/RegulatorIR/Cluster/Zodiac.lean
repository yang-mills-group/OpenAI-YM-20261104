import YM.RegulatorIR.Cluster.Halls

/-! Fine-side geometric estimates: growing profile diameters and Lipschitz
test positions at measuring geometry. Retains gains for discrepancy kernels.
-/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Cluster
open Function Set Budget Budget.Packet Budget.Layer Budget.Tuple Budget.Tariff Uniform Gradient Step Diagram Ledger Ledger.Sky Ledger.Sky.Accounts Collapsed ENNReal
open scoped ENNReal NNReal Topology BigOperators Classical
variable {W I Z: Type}{M:W→ℕ} {X Y:Page M→Type} {S: Sky X Y}{T:S.Accounts}
  {p e u r H b n:ℕ}{L:Meter W}{J:Composite I}{A:I→(w:Page M)→ Orders (X w)}
  {v:I→Page M→ℝ≥0∞}{D:I→ W→Set Room}{d:W→ℝ}{m:I→ℕ}{t:W→ℝ≥0∞}
  {x:W→Room}

abbrev area (J:Composite I)(D:I→W→Set Room) (w : W) : Set Room:= J.border w D
def heightP (T:Page M→ℝ) (b:ℕ)(i: Page M) : ℝ≥0∞:= ENNReal.ofReal (T i) ^ b

structure Zodiac (L:Meter W) (S:Sky X Y) (v:I→Page M→ℝ≥0∞)(D:I→ W→Set Room)(J:Composite I)(d:W→ℝ)(H:ℕ)(t:W→ℝ≥0∞)(x:W→Room) : Prop where
 home : ∀ w : Page M,S.l w ≤ 1
 clear : ∀ w,0<d w
 diameter : ∃ r:W→ℝ,Poly L (fun w=> ENNReal.ofReal (r w)) ∧ ∀ w, 0≤r w ∧ ∀ y∈area J D w,dist y (x w) ≤ r w
 charges : Carry (coverL M L) (fun w=> (heightP S.l H w)⁻¹*t w.bindW) (fun w=> J.rent w v)
 growth : Poly (flapL M L) (fun i=> ENNReal.ofReal (S.shift i))
 payment : Poly L fun i=> ENNReal.ofReal ((d i)⁻¹)
 stays : ∀ w,t w≠⊤
namespace Zodiac
private lemma width_eq {X:Type}{l d:ℝ}(hl:0<l)(hd:0<d) (u:ℕ)(x:Room)(h:l=d)(f:X→Room)(z:Tuple X r) : ((Premium.rooted (native l hl u) x).uses f).width z=((Premium.rooted (native d hd u) x).uses f).width z:=by subst d;rfl
lemma heighten (w:Flap M): heightP S.l H w.next = heightP S.l H w.prev * ENNReal.ofReal (S.shift w)^H:=by
 unfold heightP
 rw [S.shift_up w, ENNReal.ofReal_mul (S.shift_pos w).le,mul_pow,mul_comm]
variable (F: Zodiac L S v D J d H t x)
include F
lemma salary (H':H≤b): Carry (flapL M L) (fun w=> t w.volW) fun w:Flap M=> J.rent w.prev v * (amount (S.ceiling w) b (d w.volW))⁻¹:=by
 let g := fun w : Flap M=>J.rent w.prev v
 let h (i:Flap M):ℝ≥0∞:= heightP S.l H i.next
 have hz (i:Page M):heightP S.l H i≠0:=by unfold heightP; exact pow_ne_zero _ (ENNReal.ofReal_pos.mpr (S.hl _)).ne'
 have ht: Carry (flapL M L) (fun w : Flap M=> (heightP S.l H w.prev)⁻¹ * t w.volW) g:= Carry.us F.charges Flap.prev
 have hp : Poly (flapL M L) fun i:Flap M=> ((ENNReal.ofReal (d i.volW))⁻¹) ^ H:=by
    convert (F.payment.powQ H).us (fun w:Flap M=> w.volW) using 1 <;> try rfl
    ext1 w; rw [ENNReal.ofReal_inv_of_pos (F.clear _)]
 have h' (i:Flap M): (amount (S.ceiling i) b (d i.volW))⁻¹ ≤ h i*(ENNReal.ofReal (d i.volW))⁻¹^H:= by
    have he:= S.high i; have hh:= F.clear i.volW
    apply (ENNReal.inv_le_inv.mpr (moment_mono (S.high i) H' hh.le)).trans
    apply le_trans (ENNReal.inv_le_inv.mpr (show ENNReal.ofReal (d i.volW / S.ceiling i)^H≤ _ from ?_)) _
    · unfold amount;apply pow_le_pow_left'; apply ofReal_le_ofReal; linarith
    apply le_of_eq; rw [ENNReal.ofReal_div_of_pos he, ENNReal.inv_pow];
    rw [ENNReal.inv_div]; unfold h heightP; rw [div_eq_mul_inv,mul_pow]; rfl
    exact Or.inr (by finiteness)
    exact Or.inr (ENNReal.ofReal_pos.mpr hh).ne'
 let q:= Carry.scale (w:=h) ht
 have hh : Carry (flapL M L) (fun i=> t i.volW) fun w=>g w*h w:= by
    apply Carry.charge q
    convert Carry.mul_right (v:=fun w : Flap M=> t w.volW) (Carry.unit _ (fun w:Flap M=> t w.volW)) (F.growth.powQ H) using 1
    ext1 i; have he := heighten (H:=H) (S:=S) i
    unfold h; rw [he,← mul_assoc]; congr 1
    rw [mul_right_comm, ENNReal.inv_mul_cancel (hz _) (by unfold heightP;finiteness),one_mul]
 apply Carry.mono (Carry.mul_right hh hp)
 intro w; exact (mul_le_mul_right (h' w) (g w)).trans_eq (mul_assoc ..).symm
lemma final_width (F':Crown L S T A p (u+u+b) D v d m J) (R:(w:Flap M)→Orders (X w.next))
 (H': Folds p (flapL M L) (estate S.high (Exit S.lifts) (fun i=>area J D i.volW) (u+u)) (fun w=> t w.volW) R) : ∀ e ≤ p,∀ r, Claim (flapL M L) (fun w=>S.coverQ x u w.next) (fun w=>t w.volW) (fun w=>R w e r) := by
 intro e he r
 obtain ⟨c,hc,hC⟩:= F.diameter
 have hx : Poly (flapL M L) (fun i=> amount 1 (u+u) (c i.volW)) := by
    convert ((Poly.add (Poly.oneQ _) hc).powQ (u+u)).us (fun i:Flap M=> i.volW) using 1 <;> try rfl
    ext1 i; rw [amount,div_one,ENNReal.ofReal_add (by norm_num) (hC _).1]; simp
 apply Carry.mono (Carry.mul_right (H' e he r) hx)
 intro w
 have hz:= F.home w.next; have ht:= (F'.shape.estate_shape w.next)
 change _≤quota (R w e r) (estate S.high (Exit S.lifts) (fun i=>area J D i.volW) (u+u) w).width* _
 rw [← quota_raised]; apply quota_mono; intro z
 change ((Premium.rooted (native (S.radius w.next) (S.radius_pos _) u) (x w.volW)).uses (Exit S.lifts w)).width z ≤ _
 have hh: S.radius w.next=1:=max_eq_left hz
 rw [width_eq _ (by norm_num : (0:ℝ)<1) _ _ hh]; exact final_price (S.high _) hz u _ _ ht.1 ht.2.1 (hC w.volW).2 (hC w.volW).1 _ _
lemma grows_height (w:Page M): 1≤ (heightP S.l H w)⁻¹:=by
 nth_rw 1 [← show (1:ℝ≥0∞)⁻¹=1 by simp]; apply ENNReal.inv_le_inv.mpr; apply pow_le_one₀ (by positivity) (show ENNReal.ofReal (S.l w)≤1 from (ENNReal.ofReal_le_ofReal (F.home _)).trans_eq ENNReal.ofReal_one)
lemma each_width (F':Crown L S T A p (u+u+b) D v d m J) (e:ℕ)(he:e≤p)(r:ℕ): Claim (coverL M L) (S.coverQ x u) (fun w=> (heightP S.l H w)⁻¹*t w.bindW) (fun w=> chargeC J A w e r):=by
 have hx:= F'.shape.gather.tower (show u+u ≤ u+u+b by omega)
 obtain ⟨c,hc,hC⟩:= F.diameter
 have hm: Poly (coverL M L) (fun i=> amount 1 (u+u) (c i.bindW)):=by
    convert ((Poly.add (Poly.oneQ _) hc).powQ (u+u)).us (fun i:Page M=> i.bindW) using 1 <;> try rfl
    ext1 i;rw [amount,div_one, ENNReal.ofReal_add (by norm_num) (hC _).1];simp
 apply Carry.mono (Carry.mul_right (Carry.charge (hx e he r) F.charges) hm)
 intro w
 change _≤quota (chargeC J A w e r) (estate S.hl (Stations S) (fun i=>area J D i.bindW) (u+u) w).width* _
 rw [← quota_raised]; apply quota_mono; intro z
 have hh: S.radius w=1:= max_eq_left (F.home w)
 have ht:= (F'.shape.estate_shape w)
 change ((Premium.rooted (native (S.radius w) (S.radius_pos _) u) (x w.bindW)).uses (Stations S w)).width z ≤ _
 rw [width_eq _ (by norm_num : (0:ℝ)<1) _ _ hh]; exact final_price (S.hl _) (F.home w) _ _ _ ht.1 ht.2.1 (hC _).2 (hC _).1 _ _
end Zodiac
end YM.RegulatorIR.Cluster
