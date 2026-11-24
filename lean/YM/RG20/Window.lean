import YM.RG20.Winter
import YM.OPE.Strobe.Flick
/-!
# Cumulative entropy budget

Order-independent pay for repeated insertion of localized unmarked projections.
Later stencil consumer can run this model toward finer levels over a window with
polynomial total spacing ratio (projection *of readouts*, not generating new vacuum reps).
Cone radius estimate includes halo at every patch mm, J from kernel branch choices, and
shrinking spacings. As in `Stowage`, length payments disappear in a coupling credit,
we re-run with THIS (true, possibly not RG17.Run) history.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG20
open Function Set Filter RG Lattice Wilson MeasureTheory Next Next.Rank Push GridApprox
open OPE.Therm House Portolan Pert.Asymptotics
open scoped BigOperators Classical Topology ContDiff Matrix.Norms.Frobenius
variable {G:Gauge} {C:Family G}
local notation "H" => C.path
local notation "L" => C.path.levels
local notation "X" i:max => C.path.levels.clock.hatBeta i
local notation "A" i:max => C.S.a i
local notation "g" => regulatorRun C
local notation "D" i:max => burning C.path.levels i
variable (Y:Poetry C.path.levels)(h:G.Simple)(F:C.Makes)

variable {p k i j N q:ℕ}

def tom (G:Gauge) := G.slopeConstant* Real.log 2
include h
lemma tom_pos : 0<tom G:= mul_pos (Gauge.slopeConstant_pos h) (Real.log_pos one_lt_two)
-- cumulative exponential loss budget in this (actual) schedule. adapted from RG17 Refresh hatted spacing comparison
lemma strides20 : X i+tom G≤ X (i+1):=by
   unfold Calendar.hatBeta tom; rw [Schedule.scale_succ,mul_add]; rw [← add_assoc]; apply add_le_add_right; exact mul_le_mul_of_nonneg_left (Real.log_le_log two_pos (show (2:ℝ)≤ ((C.S).block i).val from by exact_mod_cast (show 2 ≤ ((C.S).block i).val from Nat.le_trans (by norm_num : 2 ≤ 3) ((C.S).block_large i)))) (Gauge.slopeConstant_pos h).le
lemma climbs20 : Monotone (fun i=> X i) := monotone_nat_of_le_succ fun i=> (le_add_of_nonneg_right (tom_pos h).le).trans (strides20 (i:=i) h)
lemma stride_gain (d:ℕ) : ((X (i+1))^(d+2))⁻¹ ≤
    (tom G)⁻¹ * (((X i)^(d+1))⁻¹- ((X (i+1))^(d+1))⁻¹):= by
   have hv := strides20 (C:=C) (i:=i) h; let x:=(X i); let y:= (X (i+1)); let c:=tom G
   have hr:0 < x:=zero_lt_one.trans ((L).fits.delayed _); have hx:x≤ y:= climbs20 h (Nat.le_succ i); have hs: x+c ≤ y:= hv; have he:0<c:=tom_pos h
   have hy:= hr.trans_le hx; rw [inv_mul_eq_div,le_div_iff₀ he]; simp only [← inv_pow]
   have hδ: y⁻¹+y⁻¹^2*c≤ x⁻¹ :=by field_simp; nlinarith only [mul_le_mul_of_nonneg_left hs hy.le,mul_le_mul_of_nonneg_right hx he.le]
   have hT:= mul_le_mul_of_nonneg_right hδ (show 0≤ y⁻¹^d from by positivity)
   have hB:= pow_le_pow_left₀ (show 0≤ y⁻¹ by positivity) (inv_anti₀ hr hx) d
   change y⁻¹^ _ *c ≤ x⁻¹^_ - y⁻¹^_
   have ho:=hT.trans (mul_le_mul_of_nonneg_left hB (inv_pos.mpr hr).le)
   rw [le_sub_iff_add_le]; exact Eq.trans_le (show y⁻¹^(d+2)*c+y⁻¹^(d+1)=(y⁻¹+y⁻¹^2*c)*y⁻¹^d from by ring) (ho.trans_eq (by ring))

-- recursion accounts all supports. radius def with arbitrary ℕ j, from empty above k; monotone ancestor relation. plume for walking crescendo
omit h in
/-- entering radius q; recursive expansion of outgoing `parcel`. -/
def plume (C: Family G)(p N k q:ℕ) :ℕ→ℕ
  | 0 => q
  | m+1 => if k ≤ m then expansion C.path.levels
           (Portolan.parcel (C.path.rep N p m) (burning C.path.levels m) (plume C p N k q m)) m
       else q
omit h in
lemma start_plume : plume C p N k q k=q:= by cases k with | zero=> rfl| succ k=> rw [plume, if_neg (by omega)]
local notation "Z" j:max => plume C p N k q j
local notation "Q" j:max => parcel (C.path.rep N p j) (D j) (plume C p N k q j)
local notation "E" i:max => X i

omit h in
private lemma bankDiscount {u:ℝ}{b:ℕ} (hp:u ≤ X k^(b+8)) (hv : 4 ≤ X k) : u ≤ X k^(b+9)/4:= by
    refine hp.trans (le_div_iff₀ (by norm_num)|>.mpr ?_); rw [pow_succ (X k) (b+8)]; exact mul_le_mul_of_nonneg_left hv (pow_nonneg (zero_lt_one.trans ((L).fits.delayed _)).le _)
private def Outline (C:Family G)(k b:ℕ) : Prop :=
    4 ≤ C.path.levels.clock.hatBeta k ∧ GridApprox.tail C.path.levels k≤ C.S.a k*((C.path.levels.clock.hatBeta k^(b+9))/4) ∧ ∀ N p, k≤ N→
      (2*(Stove.haloFee (C.path.rep N p k) (burning C.path.levels k))+8:ℝ) ≤ C.path.levels.clock.hatBeta k^(b+8)
include Y F
private lemma outlines (b:ℕ): ∀ᶠ k:ℕ in atTop, Outline C k b:=by
   filter_upwards [(Station.hat_rate L h).eventually_ge_atTop 10000,tended («H»:=C.path) Y h F.wilson] with k hk ht
   set x:= X k; have hX:10000 ≤ x :=hk; have hx:1≤ x := le_trans (by norm_num) hX; have hx':4 ≤ x:= le_trans (by norm_num) hX; have h':=zero_le_one.trans hx
   have hl : Real.log x ≤ x:= Real.log_le_self h'
   have hp:100000*((L).clock.J k+1:ℝ) ≤ x:= (Y.stage k).pedestal.trans hl
   refine ⟨hx',?_,fun N p hN=>?_⟩
   · unfold GridApprox.tail; have hh:=pow_le_pow_right₀ hx (show 1≤ b+9 by omega);
     have ht : 30*((L).clock.J k+5:ℝ) ≤ x^(b+9)/4 := by rw [pow_one] at hh; linarith only [hh,hp,Nat.cast_nonneg (α:=ℝ) ((L).clock.J k),hX]
     change 30*A k*_ ≤ A k*(x^_/4); rw [mul_comm 30,mul_assoc]; exact mul_le_mul_of_nonneg_left ht (C.S.a_pos _|>.le)
   have hr:= (ht N p hN).2; have hh:=pow_le_pow_left₀ (Real.log_nonneg hx) hl 6; have hy:=pow_le_pow_right₀ hx (show 7≤ b+8 by omega); change _ ≤ x^_; change (_:ℝ) ≤ 200*Real.log x^6 at hr
   linarith only [mul_le_mul_of_nonneg_right hk (pow_nonneg h' 6), hr, hh, hy, one_le_pow₀ (n:=6) hx]

omit Y F
private lemma wingRoom (b e:ℕ) (hf:∀ i:ℕ, k ≤ i → Outline C i b) (hx:(q:ℝ)≤ X k^b) (hi:k≤ i)(hp: i ≤ N)
    (hm:C.S.a k / C.S.a i ≤ X k^e):
    ((plume C p N k q i:ℕ):ℝ) ≤ X i^(e+(b+9)) := by
   have he:∀ i:ℕ, k ≤ i → i ≤ N → A i*(Z i:ℝ)+GridApprox.tail L i ≤ (A k-(A i)/2)*X i^(b+9):=by
      intro i hi hp; induction i,hi using Nat.le_induction with
      | base=>
        obtain ⟨hr,he,_⟩:= hf k le_rfl; have ht:(q:ℝ) ≤ X k^(b+9)/4:= bankDiscount (hx.trans (pow_le_pow_right₀ ((L).fits.delayed k|>.le) (by omega))) hr
        rw [start_plume]; refine le_trans (add_le_add (mul_le_mul_of_nonneg_left ht (C.S.a_pos _|>.le)) he) (le_of_eq ?_) -- wait RHS two*(/4)*A→ 1/2
        ring
      | succ i hi ih=>
        obtain ⟨hh,ht,hY⟩:= hf i hi; have hx:= bankDiscount (hY N p ((Nat.le_succ _).trans hp)) hh -- hp.le? i+1≤ N
        let X':= (X i)^(b+9); let q':ℝ:= Z i; let g':ℝ:= (Q i); let H':=A i; have h₀:= C.S.a_pos i
        have hU:g'≤ q'+X'/4:=by unfold g' q'; push_cast [Portolan.parcel]; change _≤ q'+_; linarith only [hx]
        have hV:= GridApprox.scales_next L i (Q i); have hr:(A (i+1)) ≤ (A i)/2:= by
           rw [C.S.a_step]; gcongr
           exact_mod_cast (show 2 ≤ (C.S.block i).val from le_trans (by decide : 2≤ 3) (C.S.block_large _)) -- positivity ?
        have ht:=mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (zero_le_one.trans ((L).fits.delayed i).le) (climbs20 h (Nat.le_succ i)) (b+9)) (show 0 ≤ A k-A (i+1)/2 from sub_nonneg.mpr ((by linarith only [C.S.a_pos (i+1)] : A (i+1)/2 ≤ A (i+1)).trans (C.S.strictAnti.antitone (hi.trans (Nat.le_succ _)))))
        apply le_trans _ ht; rw [plume,if_pos hi]
        apply hV.trans
        specialize ih ((Nat.le_succ _).trans hp); have hx':=zero_lt_one.trans ((L).fits.delayed i); let a:=GridApprox.tail L i
        change A i*q'+a ≤ (_- _)*X' at ih; change A i*g'+a ≤ _*X'; linarith only [mul_le_mul_of_nonneg_right hr (show 0 ≤ X' from pow_nonneg hx'.le _), mul_le_mul_of_nonneg_left hU h₀.le, ih]
   let x:=(X i); have hv:0 ≤ x:= zero_le_one.trans ((L).fits.delayed _).le; have h':=C.S.a_pos i
   rw [pow_add]; apply le_of_mul_le_mul_left _ h'; calc
     _ ≤ (A k-(A i)/2)* X i^(b+9):= le_trans (le_add_of_nonneg_right (GridApprox.tail_pos _ i).le) (he i hi hp)
     _ ≤ A k*X i^(b+9):= mul_le_mul_of_nonneg_right (by linarith only [h'] : A k-(A i)/2 ≤ A k) (pow_nonneg hv _)
     _ ≤ _:= by rw [← mul_assoc]; apply mul_le_mul_of_nonneg_right _ (pow_nonneg hv _); rw [mul_comm]; exact (div_le_iff₀ h').mp (hm.trans (pow_le_pow_left₀ (zero_le_one.trans ((L).fits.delayed k).le) (climbs20 h hi) _))
-- later package hf
include Y F
lemma enough_plume (b e:ℕ): ∀ᶠ k:ℕ in atTop, ∀ p N q i:ℕ, (q:ℝ)≤ C.path.levels.clock.hatBeta k^b → k≤ i→i ≤ N → C.S.a k / C.S.a i ≤ C.path.levels.clock.hatBeta k^e →
    ((plume C p N k q i:ℕ):ℝ) ≤ C.path.levels.clock.hatBeta i^(e+(b+9)) := by
   obtain ⟨f,hf⟩:= eventually_atTop.mp (outlines Y h F b)
   filter_upwards [eventually_ge_atTop f] with k hk p N q i hq hi hp hL using wingRoom h b e (fun i hi=> hf i (hk.trans hi)) hq hi hp hL
end YM.RG20
