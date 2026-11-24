import YM.RG20.Pocket
/-!
# Poly costs and patch pockets, uniform across all true cutoffs
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG20
open Function Set Filter RG Lattice Wilson MeasureTheory Next Next.Rank
open OPE.Therm House Portolan Pert.Asymptotics
open scoped BigOperators Classical Topology ContDiff Matrix.Norms.Frobenius
variable {G:Gauge} {C:Family G}
local notation "H" => C.path
local notation "L" => C.path.levels
local notation "X" i=> C.path.levels.clock.hatBeta i
local notation "g" => regulatorRun C
local notation "D" => scene C.path

variable (T:Poetry C.path.levels)(h:G.Simple)(F:C.Makes)

-- currency adapter for future tuples; true coupling on this actual family not Mantle
variable {p k N:ℕ}
include F
-- adapted from RG17/Refresh.lean : payBand
lemma beta_band (hm:k≤ N) :
    0<g N p k ∧ (g N p k)^2 ≤ 2*(X k)⁻¹ ∧ (X k)⁻¹ ≤ 2*(g N p k)^2:=by
   let x:=(X k); let y:=(C).path.β N p k
   have H₀:1<x:= (C).path.levels.fits.delayed _; have hY:=F.wilson.represents N p k hm
   have he:x/2 ≤ y:= hY.band.1; have hp:y ≤ 2*x:=hY.band.2
   have hz: 0<x:=zero_lt_one.trans H₀
   have hy:0<y:=by linarith only [hz,he]
   refine ⟨inv_pos.mpr (Real.sqrt_pos.mpr hy), ?_⟩
   change (Real.sqrt y)⁻¹^2 ≤ _ ∧ _ ≤ 2*(Real.sqrt y)⁻¹^2; rw [inv_pow, Real.sq_sqrt hy.le]
   change y⁻¹ ≤ 2*x⁻¹ ∧ x⁻¹ ≤ 2*y⁻¹; constructor <;> field_simp <;> linarith only [he,hp]
lemma beta_power (hm:k≤N) (d:ℕ) : ((X k)^d)⁻¹ ≤ 2^d*(regulatorRun C N p k)^(2*d):= by
   rw [← inv_pow,pow_mul, ← mul_pow]; exact pow_le_pow_left₀ (inv_pos.mpr (zero_lt_one.trans ((C).path.levels.fits.delayed k))).le (beta_band F hm).2.2 _

-- whether to pay all neighbourhoods up to t, and let X chosen freely including all of it. Quote q means *outside radii charged geometry t*, actual source. View cost native.

def Bore (C:Family G) (b d k N p:ℕ) : Prop :=
    ∀ z:Site (C.side k p), ∀ q (A:Finset (Edge (Site (C.side k p)))) τ,
    A⊆ coat q z → (q:ℝ)≤ C.path.levels.clock.hatBeta k^b →
    cool C.path.levels k≤τ → 2*τ ≤ (C.path.rep N p k).p.threshold →
    let r:= burning C.path.levels k
    let W:= essence (C.path.rep N p k) r τ q z
    let t:= Portolan.parcel (C.path.rep N p k) r q
    let M:= (C.path.levels.clock.hatBeta k ^d)⁻¹
    MeasurableSet {U | press A W U=0} ∧
    (scene C.path N p k).real {U | press A W U=0} ≤ M ∧
    ∀ (Z:Config G (C.side k p)→ℂ)(s:ℝ),
      Measurable Z → fence (coat t z) Z → (∀ U, ‖Z U‖≤ s) →
        Measurable (snorkel A W Z) ∧ fence (coat t z) (snorkel A W Z) ∧
        (∀ U, ‖snorkel A W Z U‖≤ s) ∧
        ‖(∫ U,Z U∂scene C.path N p k)-(∫ U,snorkel A W Z U ∂scene C.path N p k)‖ ≤ M*s ∧
        snorkel A W Z=snorkel A W (masked (C.path.rep N p k).p.threshold (region q z) Z)

-- shelf ENTROPY plus reserve. Single bound independent of other stars/exteriors as long as fits; here r local plus haloFee.
include T h
lemma drill (b d:ℕ) : ∀ᶠ k:ℕ in atTop, ∀ p N:ℕ,k≤N →
    0 < cool C.path.levels k ∧ 2*cool C.path.levels k ≤ (C.path.rep N p k).p.threshold ∧
    Bore C b d k N p := by
   let m:= b+d+10
   have hi := Station.hat_rate L h
   filter_upwards [homes («H»:=H) T F.wilson h m (by omega),narrow («H»:=H) h,tended («H»:=H) T h F.wilson,hi.eventually_ge_atTop 1000] with k hk hη hF hZ p N hN
   obtain ⟨hY,hK⟩:= hF N p hN
   let R:= C.path.rep N p k; have he: R.p.threshold=(L).clock.threshold k:= congr_arg BudgetPoint.threshold (F.wilson.represents N p k hN).vac
   refine ⟨hη.1,?_,fun z q A τ ho hh hC hX=>?_⟩
   · change _≤ R.p.threshold; rw [he]; linarith only [hη.2, hη.1.le]
   intro r W t M
   let x:=X k; have hx: 1000 ≤ x:=hZ; have hp:1 ≤ x:= le_trans (by norm_num) hx
   have hU: (t:ℝ) ≤ x^m:=by
      change (↑(q+2*Stove.haloFee R (burning L k)+8):ℝ)≤_; push_cast
      set a:ℝ:= Real.log x; have hz : a^6 ≤ x^6:= pow_le_pow_left₀ (Real.log_nonneg hp) (Real.log_le_self (zero_le_one.trans hp)) _
      let y:ℝ:= Stove.haloFee R (burning L k)
      change (q:ℝ)+2*y+8≤ _; change y+1 ≤ 200*a^6 at hK; change (q:ℝ) ≤ x^b at hh
      set m' := b+d+9
      have hx' (a:ℕ)(h:a≤ m') : x^a ≤ x^m' := pow_le_pow_right₀ hp h
      rw [show m=m'+1 by omega,pow_succ]; linarith only [hK, hh, mul_le_mul_of_nonneg_right hx (pow_nonneg (zero_le_one.trans hp) m'), hx' 6 ((by omega)), hx' b ((by omega)), one_le_pow₀ (n:=m') hp, hz]
   have hb:4*(x^m)⁻¹ ≤ M:= by
      change _≤ (x^d)⁻¹; rw [show m=d+(b+10) by omega, pow_add,mul_inv_rev, ← mul_assoc]; apply mul_le_of_le_one_left (inv_nonneg.mpr (pow_nonneg (zero_le_one.trans hp) _)); rw [← div_eq_mul_inv,div_le_one₀ (pow_pos (zero_lt_one.trans_le hp) _)]; exact le_trans (le_trans (by norm_num) hx) (by simpa only [pow_one] using pow_le_pow_right₀ hp (show 1≤ b+10 by omega)) -- mul_inv order
   obtain ⟨hz,hb'⟩:= not_paid_cost F.wilson hY hk hN hC hX le_rfl hU ho
   have hb0:0 ≤ (x^m)⁻¹:= inv_nonneg.mpr (pow_nonneg (zero_le_one.trans hp) _)
   refine ⟨hz,hb'.trans (le_trans (show 2 * (x^m)⁻¹ ≤ 4* (x^m)⁻¹ from by linarith only [hb0]) hb),fun Z s hf hB hs=>?_⟩ -- linarith easier
   have hw: Envelope W:= essence_env hY
   have ht: τ≤ R.p.threshold:=by linarith only [hX,hη.1, hC]
   have hS:= (norm_nonneg (Z 1)).trans (hs _)
   refine ⟨snorkel_env hw ⟨hf,s,hs⟩, snorkel_site hB (essence_fenced hY (le_refl t)), snorkel_bounds essence_nonneg hw hf hs, (patchSea F.wilson hY hk hN hC hX le_rfl hU ho Z hf hB _ hs).trans ?_,mask_snorkel ht⟩
   change 4*s*(x^m)⁻¹ ≤ _; rw [mul_right_comm]; exact mul_le_mul_of_nonneg_right hb hS
end YM.RG20
