import YM.XSpace.Troubadour
/-!
# Pair charges and 3 distinct lines proof, even at endpoint
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Octave
open Function Set Filter Lattice Trace Relief Drama Sail Tide
open scoped Topology BigOperators
variable {x y z:Cover} {D L:ℝ} {i j k:ℕ}
-- shift currency
lemma tune {T:Type*}[AddCommMonoid T] (f:Cover→ T)(B:Finset Cover)(x:Cover): ∑ i∈B,f (i-x)=∑ i ∈ B.image (fun i=> i-x),f i:= by
  classical rw [Finset.sum_image]; intro i _ j _ h; exact sub_left_injective h -- test
lemma pc_in {D:ℝ} (h:i<4)(p:Finset Cover)(hD:0≤D)(H:∀ w∈p,pad (w-x)≤D): ∑ j∈p,rate i (j-x) ≤128* D^(4-i):=by
  rw [tune]; apply pay_in h _ hD; intro w hw; obtain ⟨w',hw',rfl⟩:= Finset.mem_image.mp hw; exact H _ hw'
lemma pc_mid {D:ℝ} (p:Finset Cover)(hD:1≤D)(H:∀ w∈p,pad (w-x)≤D): ∑ j∈p,rate 4 (j-x) ≤256* Real.sqrt D:=by
  rw [tune]; apply pay_mid _ hD; intro w hw; obtain ⟨w',hw',rfl⟩:= Finset.mem_image.mp hw; exact H _ hw'
lemma pc_out {D:ℝ}(h:4< i)(p:Finset Cover)(hD:0<D)(H:∀ w∈p,D≤pad (w-x)): ∑ j∈p,rate i (j-x) ≤256 * D⁻¹^(i-4):=by rw [tune]; apply pay_out h _ hD; intro w hw; obtain ⟨w',hw',rfl⟩:= Finset.mem_image.mp hw; exact H _ hw'
structure Ticket (D L:ℝ)(i:ℕ): Prop where
 cap : i≤4
 light : i=4 → Real.sqrt D ≤ L
lemma pc (h:Ticket D L i)(p:Finset Cover)(hD:1≤D)(hL:1≤ L)(H:∀ w∈p,pad (w-x)≤ D) : ∑ w∈p,rate i (w-x) ≤256* D^(4-i)*L:=by
  rcases eq_or_lt_of_le h.cap with e|e
  · subst i; norm_num; exact (pc_mid p hD H).trans (mul_le_mul_of_nonneg_left (h.light rfl) (by norm_num))
  have hD':0<D:=zero_lt_one.trans_le hD
  exact (pc_in e p hD'.le H).trans (by calc
   _ ≤ (256:ℝ)*D^(4-i):=by gcongr <;> norm_num
   _ ≤ _:= le_mul_of_one_le_right (by positivity) hL)
lemma mellow {X:Cover}(h:1≤D)(hz:D/2 ≤ pad X)(ht:k≤4) : rate k X ≤ 16 *D⁻¹^k:=by
  have hD:0<D:=zero_lt_one.trans_le h
  apply le_trans (moon_le (by positivity:0<D/2) hz); rw [inv_div, div_eq_mul_inv,mul_pow]; apply mul_le_mul_of_nonneg_right _ (by positivity); exact (pow_le_pow_right₀ (by norm_num:1≤(2:ℝ)) ht).trans_eq (by norm_num)
private lemma sunlit (hD:1≤D)(hL:1≤L)(ho:D≤pad (x-y))(hi:Ticket D L i)(hj:j≤4)(he:4< i+j)(p:Finset Cover)(hp:∀ w∈p,pad (w-x)≤pad (w-y)): ∑ w∈p,rate i (w-x)*rate j (w-y) ≤8192*D⁻¹^(i+j-4)*L:=by -- pad syntax
  have hD':0<D:=zero_lt_one.trans_le hD; let C:= 4096* D⁻¹^(i+j-4)*L
  rw [show (8192:ℝ)* D⁻¹^(i+j-4)*L=C+C from by unfold C;ring]; apply phase (p:=fun w=>pad (w-x)≤D); swap
  · intro B h HH; unfold C
    calc
     _ ≤ ∑ w∈B,rate (i+j) (w-x):= Finset.sum_le_sum fun w hw=> by rw [← moon_mul]; exact mul_le_mul_of_nonneg_left (moon_mono _ (hp _ (h hw))) (sound ..).le
     _ ≤ _:= (pc_out he B hD' (fun w hw=> le_of_not_ge (HH _ hw))).trans (by
       calc
        _ ≤ (4096:ℝ)*D⁻¹^(i+j-4):=by gcongr <;> norm_num
        _ ≤ _:=le_mul_of_one_le_right (by positivity) hL)
  intro B h HH; calc
    _ ≤ ∑ w∈B,rate i (w-x)*(16 *D⁻¹^j):= Finset.sum_le_sum fun w hw=> mul_le_mul_of_nonneg_left (mellow hD (by
      have ht:=trio x y w; rw [sym x w,sym y w] at ht; linarith [hp w (h hw)]) hj) (sound ..).le
    _ = (∑ w∈B,rate i (w-x))*(16*D⁻¹^j):= by rw [Finset.sum_mul]
    _ ≤ (256* D^(4-i)*L)*(16*D⁻¹^j):= mul_le_mul_of_nonneg_right (pc hi B hD hL HH) (by positivity)
    _ = _:=by
       have hp:=hi.cap; conv_lhs=>rw [show j=(4-i)+(i+j-4) by omega]
       unfold C; rw [pow_add,inv_pow]; field_simp <;> ring
lemma duet (hD:1≤D)(hL:1≤L)(ho:D≤pad (x-y))(hi:Ticket D L i)(hj:Ticket D L j)(he:4< i+j)(p:Finset Cover): ∑ w∈p,rate i (w-x)*rate j (w-y) ≤16384* D⁻¹^(i+j-4)*L :=by
  let C:=8192* D⁻¹^(i+j-4)*L; rw [show (16384:ℝ)* D⁻¹^(i+j-4)*L=C+C from by unfold C; ring]; refine phase (p:=fun w=>pad (w-x)≤pad (w-y)) (fun B _ H=>sunlit hD hL ho hi hj.cap he B H) (fun B _ H=>?_); rw [sym x y] at ho; unfold C; simp_rw [mul_comm (rate i _),Nat.add_comm i j]; exact sunlit hD hL ho hj hi.cap (by omega) B fun w hw=> le_of_not_ge (H w hw)
lemma solo (hD:1≤D)(hL:1≤L)(ho:D≤pad (x-y))(hi:Ticket D L i)(hj:Ticket D L j)(hk:k≤4)(he:4< i+j)(p:Finset Cover)(h:∀ w∈p,D/2≤pad (w-z)): ∑ w∈p,rate i (w-x)*rate j (w-y)*rate k (w-z) ≤262144* D⁻¹^(i+j+k-4)*L:=by
  calc
   _ ≤ ∑ w∈p,rate i (w-x)*rate j (w-y)*(16 *D⁻¹^k):= Finset.sum_le_sum fun w hw=>mul_le_mul_of_nonneg_left (mellow hD (h w hw) hk) (mul_nonneg (sound ..).le (sound ..).le)
   _ ≤ _:= ?_
  rw [← Finset.sum_mul]; have ht:0<D:=zero_lt_one.trans_le hD; apply (mul_le_mul_of_nonneg_right (duet hD hL ho hi hj he p) (by positivity :(0:ℝ)≤16 * D⁻¹^k)).trans_eq; rw [show i+j+k-4=i+j-4+k by omega,pow_add]; ring
lemma chord (hD:1≤D)(hL:1≤L)(dxy:D≤pad (x-y))(dxz:D≤pad (x-z))(dyz:D≤pad (y-z))(hi:Ticket D L i)(hj:Ticket D L j)(hk:Ticket D L k)(he:4< i+j)(hv:4< i+k)(p:Finset Cover) :
  ∑ w∈p,rate i (w-x)*rate j (w-y)*rate k (w-z) ≤524288* D⁻¹^(i+j+k-4)*L:=by
  let C:=262144* D⁻¹^(i+j+k-4)*L; rw [show (524288:ℝ)*D⁻¹^(i+j+k-4)*L=C+C from by unfold C;ring]; refine phase (p:=fun w=> D/2≤pad (w-z)) (fun B _ H=> solo hD hL dxy hi hj hk.cap he B H) (fun B _ H=>?_); unfold C; simp_rw [show ∀ w,rate i (w-x)*rate j (w-y)*rate k (w-z)=rate i (w-x)*rate k (w-z)*rate j (w-y) from fun w=>mul_right_comm .., add_right_comm i j k]; exact solo hD hL dxz hi hk hj.cap hv B fun w hw=> by have ht:=trio y z w; rw [sym y w,sym z w] at ht; linarith [not_le.mp (H _ hw)]
-- absolute Summability without clearance for unscaled volumes
lemma duet_free {x y:Cover}(he:4< i+j): Summable fun w:Cover=> rate i (w-x)*rate j (w-y):=by
  rw [← (Equiv.addRight x).summable_iff]; let v:= reach (y-x); let p:= (1+(v:ℝ))^j
  refine Summable.of_nonneg_of_le (fun w=> mul_nonneg (sound ..).le (sound ..).le) ?_ ((carry_sum he).mul_left p); intro w; simp only [comp,Equiv.coe_addRight,add_sub_cancel_right]; change rate _ w*rate _ _≤p*rate (i+j) w; rw [← moon_mul,mul_left_comm p]; apply mul_le_mul_of_nonneg_left _ (sound ..).le; apply phase_cost; apply le_trans _ (tree (w+x-y) (y-x)); exact le_of_eq (congr_arg reach (by abel))
lemma chord_free {x y z:Cover}(he:4< i+j)(k:ℕ): Summable fun w:Cover=> rate i (w-x)*rate j (w-y)*rate k (w-z):= Summable.of_nonneg_of_le (fun _w=> mul_nonneg (mul_nonneg (sound ..).le (sound ..).le) (sound ..).le) (fun _w=>mul_le_of_le_one_right (mul_nonneg (sound ..).le (sound ..).le) (carry_at ..)) (duet_free he)
-- fixed no log
lemma pay_duet (hi:i<4)(hj:j<4)(he:4< i+j)(F:Finset Cover)(x y:Cover): ∑ w∈F,rate i (w-x)*rate j (w-y)≤16384* rate (i+j-4) (x-y):= by
  rw [← mul_one (16384*_)]
  exact duet (room _) le_rfl le_rfl ⟨hi.le,by intro H; omega⟩ ⟨hj.le,by intro H;omega⟩ he F
end YM.XSpace.Octave
