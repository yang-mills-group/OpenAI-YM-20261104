import YM.UVExt.FlowPrice

/-! Power arithmetic for a clean path of tangents selected once per level. L invoices need all preprices BEFORE block lengths. No environment multiplier included. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExt.Paths
open Function RG Wilson Precision Lattice Exterior Laurent Bid Bloch Matrix Next.Free Filter Real Set Asymptotics
open scoped Topology BigOperators Classical ContDiff
variable {G : Gauge} (A : Levels G) (P : MapPrices)

def TowerGate := ∀ m,(towerPrice A.clock.kernel.penalty P (A.clock.J (m+1)) (A.clock.J m))^(16:ℕ) ≤ ((A.S.block m).val:ℝ)

def stageCost (a : Levels G) (i : ℕ) : ℝ := let p:=a.params i; 1+p.paths + p.width⁻¹ + p.columns + p.clip.relaxation + p.supportExponent

lemma stage_one (n : ℕ) : 1 ≤ stageCost A n := by
 unfold stageCost
 let hp := A.params n
 have h := hp.paths_pos; have he := hp.price_pos; have ht := hp.width_pos; have hx := hp.clip.radius_pos; have hy := hp.columns_ge
 change 1≤1+hp.paths+hp.width⁻¹+hp.columns+hp.clip.relaxation+hp.supportExponent
 linarith [inv_nonneg.mpr ht.le]
set_option maxRecDepth 4000 in
lemma stage_fee (i : ℕ) : stageCost A (i+1)^16 ≤ (A.S.a (i+1))⁻¹ := by
 have h := A.fits.logCost i
 have hE := A.S.block_large i
 let L := ((A.S.block i).val:ℝ)
 have hL : 1 < L := lt_of_lt_of_le (by norm_num : (1:ℝ)<2) (by change (2:ℝ)≤ (A.S.block i).val; exact_mod_cast (hE.trans' (by decide : (2:ℕ)≤_)) ) -- replace
 let x := stageCost A (i+1)
 have hx := stage_one A (i+1)
 have hl : 0≤ Real.log x := Real.log_nonneg hx
 have hw : 16 ≤ ((A.clock.J (i+1): ℕ):ℝ)^2 := by have hx : (4:ℝ) ≤ (A.clock.J (i+1):ℝ) := Nat.cast_le (α:=ℝ)|>.mpr (A.clock.adm (i+1)); nlinarith
 change Real.log x / Real.log L ≤ ((A.clock.J (i+1):ℝ)^2)⁻¹ at h
 rw [div_le_iff₀ (Real.log_pos hL)] at h -- wrong direction
 obtain he := (Real.log_le_log_iff (x:=x^(16:ℕ)) (y:=L) (by positivity [hx]) (zero_lt_one.trans hL)).mp (by rw [Real.log_pow]; change 16*Real.log x ≤ _; have hb := (inv_mul_cancel₀ (by positivity : (A.clock.J (i+1):ℝ)^2≠0)); nlinarith only [h,hw,hl,hb, Real.log_pos hL]) -- named
 refine le_trans he (show _ ≤ (A.S.a _)⁻¹ from (le_of_mul_le_mul_left ?_ (A.S.a_pos (i+1)))) -- check direction of left
 rw [mul_inv_cancel₀ (A.S.a_pos _).ne',A.S.a_step, show ((A.S.block i).val:ℝ) = L from rfl,div_mul_cancel₀ _ (zero_lt_one.trans hL|>.ne')]
 exact (A.S.strictAnti.antitone (Nat.zero_le i) |>.trans_eq A.S.a_zero) -- check field_simp
 

lemma paths_width (i : ℕ) : (A.params i).paths+1 ≤ stageCost A i ∧ (1+2/(A.params i).width) ≤ 2*stageCost A i := by
  let p:=A.params i; change p.paths+1 ≤ _ ∧ _
  have h := p.paths_pos; have he := p.price_pos; have ht := p.width_pos; have hx := p.clip.radius_pos; have hy := p.columns_ge; have hb := inv_nonneg.mpr ht.le
  constructor <;> unfold stageCost <;>
    (try change _ ≤ 2*(1+p.paths+p.width⁻¹ + p.columns + p.clip.relaxation+p.supportExponent)) <;> first |(rw [div_eq_mul_inv];simp only [p] at *; linarith) |simp only [p] at *; linarith -- replace tactics. first goal expression constants; unfold p to fix

section rate
abbrev Roller := ∀ (m p : ℕ), Dir G (A.S.side m p) → Dir G (A.S.side (m+1) p)
variable (R : Roller A)
def ascender (m p : ℕ) (v : Dir G (A.S.side m p)) : (j : ℕ) → Dir G (A.S.side (m+j) p)
    | 0 => v
    | j+1 => R (m+j) p (ascender m p v j)

variable (m : ℕ) (p : ℕ) (v : Dir G (A.S.side m p))
abbrev fieldFee i := ‖ascender A R m p v i‖
def dCur i := ‖dColor G _ 1 (ascender A R m p v i)‖
def walkFee i := gradD (ascender A R m p v i)

def powaid (s : ℕ) (X : ℕ→ℝ) := ∃ C:ℝ,(0<C ∧ ∀ i:ℕ, 0≤X i ∧ X i ^16 ≤ C*(A.S.a (m+i))^s)

theorem afford (s) {g : ℕ→ℝ} (gs : 0<s) (hi:∀ i, 0≤g i) (hp : ∀ i,
   (((A.S.block (m+i)).val):ℝ)^(16*s-1:ℕ)*(g (i+1))^16 ≤ g i ^16) : powaid A m (16*s-1) g := by
  let D := 1+ g 0 ^16/(A.S.a (m+0))^(16*s-1:ℕ)
  refine ⟨D,by unfold D; exact add_pos_of_pos_of_nonneg zero_lt_one (div_nonneg (pow_nonneg (hi 0) _) (pow_nonneg (A.S.a_pos _).le _)),fun i=>⟨hi _,?_⟩⟩
  induction i with
  | zero => dsimp only [D]; have h := pow_pos (A.S.a_pos (m+0)) (16*s-1:ℕ); rw [add_mul, one_mul,div_mul_cancel₀ _ h.ne']; linarith -- positivity
  | succ i h =>
     rw [show m+(i+1)=m+i+1 by omega,A.S.a_step] -- rw via a_step
     rw [div_pow, ←mul_div_assoc, le_div_iff₀ (by positivity)]; exact Eq.trans_le (mul_comm _ _) ((hp i).trans h)

variable {R} (h : ∀ i t (v: Dir G (A.S.side i t)), let D:=towerPrice A.clock.kernel.penalty P (A.clock.J (i+1)) (A.clock.J i); let L:=A.S.block i
   ‖R i t v‖ ≤ D/L.val * ‖v‖ ∧ ‖dColor G _ 1 (R i t v)‖ ≤ D/(L.val:ℝ)^2 *‖dColor G _ 1 v‖ ∧ gradD (R i t v) ≤ D/(L.val:ℝ)^3 * gradD v) (hG : TowerGate A P)

private lemma pow_step (x y D L : ℝ) (s : ℕ) (hs : 0 < s) (h : 0 ≤ x) (hL : 0<L) (hy : 0≤y) (hY : x≤D/L^s*y) (hm : D^(16:ℕ) ≤ L) : L^(16*s-1:ℕ) * x^(16:ℕ) ≤ y^(16:ℕ) := by
  have hv := pow_le_pow_left₀ h hY 16
  calc
     _ ≤ L^(16*s-1:ℕ)*(D/L^s*y)^ (16:ℕ) := mul_le_mul_of_nonneg_left hv (pow_nonneg hL.le _)
     _ = D ^16/L * (y^16) := by
       rw [mul_pow,div_pow,← pow_mul,←mul_assoc, ←mul_div_assoc]
       congr 1; apply (div_eq_div_iff (pow_ne_zero _ hL.ne') hL.ne').mpr
       rw [show L^(16*s-1:ℕ)*D^16 * L=L^(16*s-1:ℕ) * D^16 * L^(1:ℕ) by rw [pow_one]]
       rw [mul_right_comm _ (D^16) _,←pow_add,show 16*s-1+1=s*16 by omega]; exact mul_comm ..
     _ ≤ _ := mul_le_of_le_one_left (by positivity) (by rw [div_le_one hL];exact hm)

include h hG
lemma basic_aid : powaid A m 15 (fieldFee A R m p v) ∧ powaid A m 31 (dCur A R m p v) ∧ powaid A m 47 (walkFee A R m p v) := by
  have hF j := h (m+j) p (ascender A R m p v j); dsimp only at hF
  have hl j := show (0:ℝ)<(A.S.block j).val by exact_mod_cast ((show (0:ℕ)< (A.S.block j).val from (A.S.block j).property))
  exact ⟨afford A m (g:=fieldFee A R m p v) 1 zero_lt_one (fun _=>norm_nonneg _) (fun j=>pow_step _ _ _ _ _ (by decide) (norm_nonneg _) (hl _) (norm_nonneg _) (show fieldFee A R m p v (j+1) ≤ towerPrice _ _ _ _/ (_:ℝ)^1*fieldFee A R m p v j from (by rw [pow_one]; exact (hF j).1)) (hG _)),
      afford A m (g:=dCur A R m p v) 2 (by decide) (fun _=>norm_nonneg _) (fun j=>pow_step _ _ _ _ _ (by decide) (norm_nonneg _) (hl _) (norm_nonneg _) ((hF j).2.1) (hG _)),
      afford A m (g:=walkFee A R m p v) 3 (by decide) (fun _=>norm_nonneg _) (fun j=>pow_step _ _ _ _ _ (by decide) (norm_nonneg _) (hl _) (norm_nonneg _) ((hF j).2.2) (hG _))⟩
end rate

end YM.UVExt.Paths
