import YM.FormalBulk08.Sable.Hem
import YM.FormalBulk08.Quire.Cart

/-! Charges on crosses & rows, keep the kernel expansion supplies.
No dependency per block on repeated coefficient. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Sable
open Reef Flat Lattice Laurent Bloch Exterior Filter Function Next.Free Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank
open scoped NNReal Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G: Gauge} {I J V:Type} {u m n:ℕ} {η σ A C B:ℝ} {ε θ:ℝ≥0}
def baili (I J:Type)(u:ℕ) (ε:ℝ≥0): Solar (grain (fame I) ε) (grain (fame J) ε) (u:ℝ) u where
   capsule x y:=Gorge.shine u (plum ε (size (y.1-x.1)))
   fare:=1
   good:=zero_le_one
   carried :=fun v w=>by rw [ENNReal.ofReal_one,one_mul]; exact room (grain (fame I) ε) (grain (fame J) ε) (fun a b=>plum ε (capD b.1 a.1)) (fun x y a b=> by
      have H : capD a.1 b.1 ≤ capD a.1 x.1+ capD b.1 y.1+capD x.1 y.1:= by have he:=cap_travel a.1 x.1 y.1; have hh:=cap_travel a.1 y.1 b.1;rw [cap_turn y.1 b.1] at hh;omega
      exact (plum_mono H).trans ((plum_tri ..).trans (add_le_add_left (plum_tri _ _) _))) _ (Nat.cast_nonneg _) v w
lemma cost_sheen (u:ℕ)(X : Biglot I)(y:Biglot J)(hs:0 < η)(hw:ε ≤1): (baili _ _ u ε).capsule X y≤ ENNReal.ofReal (sack u η) * linkshine η X y:= by
    unfold linkshine Gorge.shine; rw [← ENNReal.ofReal_mul (sack_pos u hs)]; exact ENNReal.ofReal_le_ofReal (sack_for u hs hw _)
variable [Fintype I] [Fintype J]
lemma sea_counts (R: Row I J)(h:R.strip η B)(hp:0<η)(hc:0 ≤ B)(he:ε≤1):
    Hill (baili _ _ u ε).capsule (lands R) (sack u η*(Fintype.card J*B)) (sack u η*(Fintype.card I * B)):= by
    have ht:=sack_pos u hp
    have hh(x:Biglot I)(y:Biglot J): (baili _ _ u ε).capsule x y* ‖lands R x y‖ₑ ≤ ENNReal.ofReal (sack u η)*(linkshine η x y*‖lands R x y‖ₑ):= (mul_le_mul_left (cost_sheen u x y hp he) _).trans_eq (mul_assoc ..)
    refine ⟨by positivity,by positivity,fun x=> (ENNReal.tsum_le_tsum (hh x)).trans ?_,fun y=> (ENNReal.tsum_le_tsum (fun x=> hh x y)).trans ?_⟩
    · rw [ENNReal.tsum_mul_left, ENNReal.ofReal_mul (sack_pos u hp)]; exact mul_le_mul_right ((grad_line R h hc).rows x) _
    rw [ENNReal.tsum_mul_left, ENNReal.ofReal_mul (sack_pos u hp)]; exact mul_le_mul_right ((grad_line R h hc).columns y) _
lemma school (R:Fin m → Row I J)(T:Tile (Biglot I) m)(X:Biglot I)(y:J)(B:Fin m→ℝ)(ht:Knoxville (grain (fame _) ε) u X T A)(hs:0<η)(hm:ε ≤1)(he:∀ i,(R i).strip η (B i))(hB :∀ i,0≤B i):
    Allow (grain (fame _) ε) u (X.1,y) (fun v t=> T t *∏ i,lands (R i) (t i) (v i)) (1*(A*∏ i:Fin m,sack u η*(Fintype.card J* B i))):= by
   apply Quire.rose_bill (B:=fun i=> sack u η * (Fintype.card I* B i)) (baili _ _ u ε) _ _ ht _
   · intro i; exact mul_nonneg (sack_pos u hs) (mul_nonneg (Nat.cast_nonneg _) (hB _))
   · simp [baili,Gorge.shine,plum,slant]
   intro i; exact sea_counts _ (he i) hs (hB i) hm
variable {L: Side}
omit [Fintype I] in
lemma ice_sc (x y:Biglot (Co L I))(hs:ε ≤ 1)(he:ε ≤ L.val*θ) : (grain (fame _) ε).d x y≤ plum 1 8 + (grain (fame _) θ).d ((scroll L I).symm x) ((scroll L I).symm y):= by
   let X:=capD x.1 y.1; let Y:=capD ((scroll L I).symm x).1 ((scroll L I).symm y).1; have hx : (L.val:ℝ)* (X:ℝ) ≤ (Y:ℝ)+8* ↑L.val:=by exact_mod_cast extent_ray x y
   have hw: ((ε:ℝ)/ (L.val:ℝ))≤θ:= by rw [div_le_iff₀ (by positivity), mul_comm]; exact_mod_cast he
   have hk:(ε:ℝ)* X ≤ (θ:ℝ)* (Y:ℝ)+ 8:= by
      let l:ℝ:=L.val;have hl:0<l:=by positivity
      have ht := mul_le_mul_of_nonneg_left hx (show 0≤(ε:ℝ)/l by positivity); have hg : (ε:ℝ) / l * (l* (X:ℝ))= (ε:ℝ)* X:= by simp [←mul_assoc,hl.ne' ]
      change (ε:ℝ)/l*(l* X) ≤ (ε:ℝ)/l* ((Y:ℝ)+8*l) at ht; rw [hg, mul_add, show (ε:ℝ) /l*(8*l)=8*(ε:ℝ) from (by field_simp)] at ht; refine ht.trans (add_le_add (mul_le_mul_of_nonneg_right hw (Nat.cast_nonneg _)) ?_); have hp:(ε:ℝ) ≤ 1:=by exact_mod_cast hs
      linarith
   let M := (1:ℝ)+(θ:ℝ)* Y; have hz:0 ≤ (θ:ℝ)*Y:=by positivity
   have ht:=Real.log_le_log (x:=1+(ε:ℝ)* X) (y:=9*M) (by positivity) (by unfold M;linarith)
   rw [Real.log_mul (by norm_num) (by unfold M; positivity)] at ht
   apply Nat.ceil_le.mpr; rw [Nat.cast_add]; apply ht.trans; apply add_le_add _ (Nat.le_ceil _); have hh:=Nat.le_ceil (slant 1 8); simp only [slant, NNReal.coe_one,one_mul,Nat.cast_ofNat] at hh; convert hh using 2 <;> norm_num [plum,slant]
omit [Fintype I] in
lemma ice_turn (v:chain (Biglot (Co L I)) m)(hs:ε≤1)(he:ε≤ L.val*θ) : wide (grain (fame _) ε) v≤ plum 1 8+ wide (grain (fame _) θ) ((scroll L I).symm ∘ v):= known_wide _ _ _ (fun i j=>(ice_sc (v i) (v j) hs he).trans (add_le_add_right (reached (grain (fame I) θ) ((scroll L I).symm ∘ v) i j) _)) -- add right mathlib
omit [Fintype I] in
lemma flipping (T:Tile (Biglot I) m)(x:Biglot (Co L I))(hs:ε≤1)(he: ε≤L.val*θ)(h:Knoxville (grain (fame _) θ) u ((scroll L I).symm x) T B): Knoxville (grain (fame _) ε) u x (jetty (scroll L I).symm T) (Real.exp ((u:ℝ)*plum 1 8)*B):= by
   refine ⟨mul_nonneg (Real.exp_pos _).le h.1,?_⟩; let D:=grain (fame I) θ
   let f:chain (Biglot (Co L I)) m ≃ chain (Biglot I) m:=Equiv.arrowCongr (Equiv.refl _) (scroll L I).symm
   have hz(v:chain (Biglot (Co L I)) m): wide (grain (fame _) ε) (Fin.cons x v) ≤ plum 1 8+ herb D ((scroll L I).symm x) (f v):= by change wide (grain (fame _) ε) (Fin.cons x v) ≤ plum 1 8 + wide D (Fin.cons _ ((scroll L I).symm ∘ v)); simpa only [Fin.comp_cons] using ice_turn (Fin.cons x v : chain (Biglot (Co L I)) (m+1)) hs he
   rw [ENNReal.ofReal_mul (Real.exp_pos _).le]; refine le_trans ?_ (mul_le_mul_right h.2 _); rw [← ENNReal.tsum_mul_left, ←Equiv.tsum_eq f (fun i=> ENNReal.ofReal _*(Gorge.shine (u:ℝ) (wide D (Fin.cons ((scroll L I).symm x) i))* ‖T i‖ₑ))]; refine ENNReal.tsum_le_tsum fun i=>?_ ; refine (mul_le_mul_left (shine_le _ (Nat.cast_nonneg _) (hz i)) _).trans_eq ?_; rw [shine_add,mul_assoc];rfl
lemma icy_counts (S:Fin m→ Cross L I J)(x:Biglot I)(y:J)(hs:ε≤1)(he: ε ≤ L.val*θ)(T:Tile (Biglot I) m)(ht:Knoxville (grain (fame _) θ) u x T B)(hp:0 < η)(hf:∀ i,(S i).strip η C)(hc:0≤C): Knoxville (grain (fame _) ε) u (piz L x y) (prism (fun i=>merit (S i)) T)
   ((Real.exp ((u:ℝ)*plum 1 8)* B) * (sack u η *(Fintype.card J*C))^m):= by
   rw [tower _ _ rfl S]; have hh := (show Knoxville (grain (fame _) θ) u ((scroll L I).symm ((scroll L I) x)) T B from by rw [Equiv.symm_apply_apply];exact ht)
   have hv:= (school S _ ((scroll L I) x) y (fun i=>C) (flipping T _ hs he hh) hp hs hf (fun _=>hc)).bill; rw [Finset.prod_const, Finset.card_univ,Fintype.card_fin,one_mul] at hv; exact hv
end YM.FormalBulk08.Sable
