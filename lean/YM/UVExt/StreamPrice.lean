import YM.UVExt.ReceiptJet
set_option maxHeartbeats 200000

set_option autoImplicit false
noncomputable section
namespace YM.UVExt.Paths
open Bid Exterior RG Function Filter Real Wilson Precision Lattice
open scoped BigOperators Classical Topology ContDiff
variable {G : Gauge} {n : Side} (v : Dir G n)
local notation "𝒟" => ‖dColor G n 1 v‖
local notation "ℓ" => breath
local notation "P" => sprout v

def driftPrice := (10*curveBill G*K G*G.colorScale) * ‖v‖ + (3*curveBill G)*𝒟

def room (L : ℝ) := (1+L)*driftPrice v

def mint (L : ℝ) := (1+L)*curveBill G*𝒟

lemma room_price {L : ℝ} (h : 0≤L) : 2*tempo v (2*L) ≤ room v L ∧ (1+L*(4:ℝ))*linkRate v ≤ room v L ∧ mint v L ≤ room v L ∧ 0 ≤ mint v L := by
  have h1 := K_pos G
  have h2 := curveBill_pos G
  have ht := G.colorScale_pos
  have hx : 0≤ ‖v‖ := norm_nonneg _
  have hr := norm_nonneg (dColor G n 1 v)
  let K1 := K G * linkRate v
  have hp : 0 ≤ linkRate v := mul_nonneg G.colorScale_pos.le (norm_nonneg _)
  have hk : 0≤K1 := mul_nonneg (zero_le_one.trans h1) hp
  have ht' : 8*K1 ≤ driftPrice v := by
    dsimp [driftPrice,K1,linkRate]
    have hg : 0 ≤ K G*G.colorScale*‖v‖ := by positivity
    have hf : (curveBill G-1)*(K G*G.colorScale*‖v‖) ≥ 0 := mul_nonneg (by linarith) hg
    have h' : 0≤curveBill G*𝒟 := mul_nonneg (by linarith) hr
    nlinarith only [hg,hf,h']
  unfold room tempo
  rw [show K G * (1+ 2*(2*L))*linkRate v=(1+4*L)*K1 by unfold K1; ring]
  refine ⟨by nlinarith, ?_, ?_, by unfold mint; positivity⟩
  · have hf : 4*linkRate v ≤ driftPrice v := (show _ ≤ 8*K1 by unfold K1; nlinarith only [hp,h1]).trans ht'
    nlinarith
  unfold mint driftPrice; rw [mul_assoc (1+L)]
  refine mul_le_mul_of_nonneg_left ?_ (by linarith)
  have : 0 ≤ 10*curveBill G*K G*G.colorScale*‖v‖ := by positivity
  nlinarith only [this,mul_nonneg hr (zero_le_one.trans h2)]

lemma room_pos {L : ℝ} (h : 0≤L) : 0≤room v L := (room_price v h).2.2.2.trans (room_price v h).2.2.1
lemma driftPrice_pos : 0≤driftPrice v := by unfold driftPrice; positivity [K_pos G,G.colorScale_pos,curveBill_pos G]
variable {Y Y' Z Z' : ℝ} {a : ℝ → ℝ}

lemma Bill.increase {i} (hY : Y≤Y') (hb : Bill Y i a) : Bill Y' i a := ⟨hb.pos.trans hY,hb.smooth,(fun i=> (hb.pay i).trans (pow_le_pow_left₀ hb.pos hY _)),hb.vanish⟩
lemma resize (hY : Y≤Y') (hZ : Z≤Z') (hb : Tri Y Z a) : Tri Y' Z' a := ⟨hb.1.increase hY,hb.2.trans hZ⟩

def crate (k : ℕ) (L : ℝ) := k * room v L

private lemma continuous_row {k} (a : Fin k → ℝ→ℝ) (h : ∀ i, ContDiff ℝ ω (a i)) : ContDiff ℝ ω (∏ i,a i) := by
  induction k with
  | zero => simp only [Finset.univ_eq_empty,Finset.prod_empty]; exact contDiff_const (c:=(1:ℝ))
  | succ k ih => rw [Fin.prod_univ_succ]; exact (h _).mul (ih _ (fun i =>h _))
lemma stream_ana {k} x (A : Token G k) : ContDiff ℝ ω (stream v x A) := continuous_row _ fun i => sprout_diff ..
private lemma rate_row {k} (a : Fin k → ℝ→ℝ) (h : ∀ i, ContDiff ℝ ω (a i)) (U R : ℝ) (hU : 0 ≤ U) (hR : 0 ≤ R) (ht : ∀ i t e, ‖iteratedDeriv e (a i) t‖≤ U*R^e) (t e) : ‖iteratedDeriv e (∏ i,a i) t‖ ≤ U^k * (k * R)^e := by
  induction k generalizing t e with
  | zero => cases e <;> simp [show (1 : ℝ→ℝ) = (fun _ : ℝ=>1) from rfl,iteratedDeriv_const]
  | succ k ih =>
    let b := fun i : Fin k => a i.succ
    calc
      _ = ‖iteratedDeriv e (a 0 * ∏ i,b i) t‖ := by rw [Fin.prod_univ_succ]
      _ ≤ U* U^k * (R+k*R)^e := peg_cost U (U^k) R (k*R) e hU (pow_nonneg hU _) hR (mul_nonneg (Nat.cast_nonneg _) hR) (h _) (continuous_row b (fun i => h _)) (fun i t=> ht _ _ _) (fun i _=>ih (a:=b) (fun i=> h _) (fun i=> ht _) _ _) _
      _ = _ := by rw [Nat.cast_add,Nat.cast_one]; ring

lemma stream_cap {k : ℕ} i (x : Site n) : cap i ((K G)^k) ((k:ℝ)*driftPrice v) (stream v x) (breath (k:=k)) := by
  refine fun A t e _ => ?_
  let L : ℝ := ℓ A
  have hL : 0≤L := breath_pos _
  have hl : ∀ j : Fin k, ((A.1 j).length:ℝ) ≤ L := fun j => Nat.cast_le.mpr (Finset.single_le_sum (f:=fun i=> (A.1 i).length) (fun _ (_ : _)=>Nat.zero_le _) (Finset.mem_univ j))
  let a := fun (i : Fin k)=> sprout v x (A.1 i) (A.2 i)
  let M := (1+L)*(driftPrice v)
  have hq : (1+2*L)*linkRate v ≤ M := ((show _≤(1+L*4)*linkRate v by
      have ht := mul_nonneg G.colorScale_pos.le (norm_nonneg v)
      unfold linkRate; nlinarith).trans (room_price v hL).2.1)
  change ‖iteratedDeriv e (∏ j : Fin k, a j) t‖ ≤ _
  rw [←mul_assoc,show (1+L) * (k:ℝ) *driftPrice v = (k:ℝ)*M by unfold M; ring]
  refine rate_row a (fun i=>sprout_diff ..) (K G) M (zero_le_one.trans (K_pos G)) (by have := driftPrice_pos v; unfold M; positivity) (fun j t i => (sprout_rate v L _ _ _ _ _ (hl _)).trans ?_) _ _
  refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ?_ hq _) (le_trans zero_le_one (K_pos _))
  unfold linkRate; positivity [G.colorScale_pos]

lemma sprout_paid {L : ℝ} {s : Slot} (h : (s.length:ℝ)≤L) x i : Tri (room v L) (mint v L) (P x s i) := by
  have h' := (Nat.cast_nonneg ..).trans h
  have ht := (sprout_bill v x s i (L) h)
  refine resize (le_trans (tempo_le (y:=2*L) v (by linarith : L ≤ 2*L)) ((le_mul_of_one_le_left (tempo_pos v _ (by positivity)) (show (1:ℝ) ≤ 2 by norm_num)).trans (room_price v h').1)) ?_ ht
  unfold mint
  refine mul_le_mul_of_nonneg_right (le_trans ((part_price i).trans (curveBill_ge G)) ?_) (norm_nonneg _)
  exact le_mul_of_one_le_left (le_trans zero_le_one (curveBill_pos G)) (by linarith)

variable {L : ℝ} {k : ℕ}

lemma paired_paid {a b : Slot} (h₁ : (a.length:ℝ)≤L) (h₂ : (b.length:ℝ)≤L) (x) (i j) :
    let s:= P x a i * P x b j
    Quad (2*room v L) (2*mint v L) s := by
  obtain ⟨ht,hv⟩ := top_two (sprout_paid _ h₁ x i) (sprout_paid _ h₂ x j)
  dsimp only
  apply And.intro (ht.increase (by linarith)) _
  exact hv.trans (by nlinarith)
lemma difference_paid {a b : Slot} (h₁ : ((a.length:ℝ)+b.length)≤L) (h₂ : a.offset=b.offset) (h₃ : a.plaq=b.plaq) (x) (i) :
    Quad (2*room v L) (2*mint v L) (P x a i - P x b i) := by
  obtain ⟨ht,hv⟩ := part_difference_rate v h₁ h₂ h₃ x i
  have hL := (show (0:ℝ)≤_ from add_nonneg (Nat.cast_nonneg a.length) (Nat.cast_nonneg b.length)).trans h₁
  have hr := curveBill_pos G
  refine ⟨ht.increase (by gcongr; exact (tempo_le v (x:=L) (y:=2*L) (by linarith)).trans ((le_mul_of_one_le_left (tempo_pos v _ (by positivity)) one_le_two).trans (room_price v hL).1)), hv.trans (pow_le_pow_left₀ (by positivity) ?_ _)⟩
  unfold mint; rw [←mul_assoc 2]
  have h4 : curveBill G * L ≤ 2*((1+L)*curveBill G) := by linear_combination (2+L) * (by have h := curveBill_pos G; linarith : curveBill G ≥ 0)
  exact mul_le_mul_of_nonneg_right h4 (norm_nonneg _)

private lemma drift_3 {L f F e} (hL : 0≤L) (hf : Tri (room v L) (mint v L) f) (hF : Quad (2*room v L) (2*mint v L) F) (he : e=3 ∨ e=4) :
    |tag e (f*F)| ≤ 10*((1+L)^(e))*gain (6*curveBill G*𝒟) (2*driftPrice v) e := by
  let M := room v L
  let D := mint v L
  have hY : D≤M := (room_price v hL).2.2.1
  have hM : 0≤M := room_pos v hL
  have hD : 0≤D := (room_price v hL).2.2.2
  obtain ⟨h,h'⟩ := triplePrice hF.1 (hf.1.increase (show room v L≤2*M by linarith)) (Y:=2*M) (show (0:ℝ)≤2*D by positivity) (by gcongr) (hf.2.trans (by change D≤_; linarith)) hF.2 le_rfl
  rcases he with he|he <;> subst e
  · simp only [gain,if_true, ↓reduceIte]
    refine h.trans ?_
    unfold D mint; have ht : 0 ≤ ((1+L) * curveBill G * 𝒟)^3 := by have h := curveBill_pos G; positivity
    nlinarith only [ht]
  exact h'.trans (by unfold D mint M room gain; rw [if_neg (by decide : ¬(4:ℕ)=3)]; have hp := driftPrice_pos v; nlinarith [mul_nonneg (show 0≤(1+L)^4 * curveBill G *𝒟 by have h := curveBill_pos G; positivity) (pow_nonneg hp 3)])

lemma stream3 x (T : Token G 3) {e} (he : e=3 ∨ e=4) : |tag e (stream v x T)| ≤ 10*((1+ℓ T)^e)*gain (6*curveBill G*𝒟) (2*driftPrice v) e := by
  let L := ℓ T
  let F i := P x (T.1 i) (T.2 i)
  have h (i : Fin 3) : ((T.1 i).length:ℝ) ≤ L := Nat.cast_le (α:=ℝ)|>.mpr (Finset.single_le_sum (fun j _ => show 0 ≤ (_ : ℕ) from Nat.zero_le (T.1 j).length) (Finset.mem_univ i))
  rw [stream,Fin.prod_univ_three,mul_assoc]
  exact drift_3 v (breath_pos _) (sprout_paid _ (h 0) _ _) (paired_paid v (h 1) (h 2) _ _ _) he

lemma stream4 x (T : Token G 4) {e} (he : e=3 ∨ e=4) : |tag e (stream v x T)| ≤ 10*((1+ℓ T)^e)*gain (6*curveBill G*𝒟) (2*driftPrice v) e := by
  let L := ℓ T
  let F i := P x (T.1 i) (T.2 i)
  have h (i : Fin 4) : ((T.1 i).length:ℝ) ≤ L := Nat.cast_le (α:=ℝ)|>.mpr (Finset.single_le_sum (fun j _ => show 0 ≤ (_ : ℕ) from Nat.zero_le (T.1 j).length) (Finset.mem_univ i))
  have hF : ∀ i : Fin 4, Tri (room v L) (mint v L) (F i) := fun i => sprout_paid v (h i) x _
  rcases he with he|he <;> subst e
  · change |tag 3 (∏ i,F i)| ≤ _; rw [show tag (3) _= 0 from (hrow 4 F (fun i => (hF i).1)).vanish 3 (by decide)]
    have := curveBill_pos G; have := breath_pos T; rw [abs_zero,gain,if_pos rfl]; positivity
  dsimp only [stream,gain]; simp only [show ¬(4 : ℕ)=3 from by decide, ↓reduceIte]
  refine le_trans (evenPrice (D:=mint v L) (fun i => (hF i).1) (fun i => (hF i).2)) ?_
  have hD : (mint v L)^4 ≤ mint v L * (room v L)^3 := by rw [pow_succ']; exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (n:=3) (room_price v (breath_pos _)).2.2.2 (room_price v (breath_pos _)).2.2.1) (room_price v (breath_pos _)).2.2.2
  norm_num [Nat.factorial]; refine (mul_le_mul_of_nonneg_left (α:=ℝ) (a:=24) hD (by norm_num)).trans ?_
  unfold mint room; have := curveBill_pos G; have := driftPrice_pos v; have hL : 0≤L := breath_pos _; have hr : 0≤𝒟 := norm_nonneg _
  change 24 * ((1 + L) * _ * 𝒟 * ((1+L)*_)^3) ≤ 10 * (1+L)^4 * (6*_ * 𝒟 * _)
  nlinarith [(by positivity : 0≤(1+L)^4* curveBill G* 𝒟* driftPrice v ^3)]

lemma dispersion x (T : Token G 2) {e} (he : e=3 ∨ e=4)  :
    |tag e (afterPair v x T - axisPair v x T)| ≤ 10* (3^e) * (1+ℓ T)^e*gain (6*curveBill G*𝒟) (2*driftPrice v) e := by
  let a := T.1 0; let b := T.1 1
  let L := 3*ℓ T
  have h := align_status a b
  have ha : L=(3:ℝ) * (a.length + b.length) := by dsimp only [L,a,b,breath]; rw [Fin.sum_univ_two,Nat.cast_add]
  have h₁ : ((relay a b).length+(alignSecond a b).length : ℝ) ≤ L := by rw [ha]; exact_mod_cast (show _ ≤ 3*(a.length+b.length) by omega)
  have hT : (a.length:ℝ)≤ℓ T := by rw [← mul_le_mul_iff_right₀ (show (0:ℝ)<3 by norm_num)]; change 3*(a.length:ℝ)≤L; rw [ha]; exact_mod_cast (by omega : 3*a.length≤ 3*(a.length+b.length))
  have hE : (0:ℝ) ≤ ℓ T := breath_pos _
  have h₂ : ((ground a).length:ℝ) ≤ L := le_trans (b:=(a.length:ℝ)) (by exact_mod_cast Nat.le_add_left 4 a.walk.length) (hT.trans (by unfold L; linarith))
  have hL : (0:ℝ) ≤ L := (Nat.cast_nonneg _).trans h₂
  unfold axisPair afterPair; rw [←mul_sub]; refine le_trans (drift_3 v hL (sprout_paid v h₂ x _) (difference_paid _ h₁ (relay_end _ _) rfl x _) he) ((mul_le_mul_of_nonneg_right (α:=ℝ) (mul_le_mul_of_nonneg_left (α:=ℝ) (a:=10) (c:=(3*(1+ℓ T))^e) ?_ (show (0:ℝ)≤10 by norm_num)) (gain_pos (n:=e) (D:=6*curveBill G*𝒟) (Y:=2*driftPrice v) (by have := curveBill_pos G; positivity) (by have := driftPrice_pos v; positivity))).trans_eq (by rw [mul_pow]; ac_rfl))
  exact pow_le_pow_left₀ (by positivity) (show 1+L≤ 3*(1+ℓ T) by unfold L; linarith) _

end YM.UVExt.Paths
