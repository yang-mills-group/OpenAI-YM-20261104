import YM.RG05Readout.Shadows.Malice
/-!
# Through the separated part of the descent

Width versus decay budgets. Explicit pressure currencies, members with
multiplicities priced earlier. Canonical quota stationary sewing. Real estimates.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Shadow
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source Bid
open Extra.Histories Push Local Planned.GuardedAtom Guard MergeProof Extra.Histories.Relay Native
open PhysicalNext.Repeat Lotus Motion Trace.Physical Offsets Copper View Address Many Pressure
open Legato Bandage Next.Rank.Station Accent
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C:Family G} {N m n b p d:ℕ}{D:Address.Rail C}{B:ℕ→ℕ→ℝ}{x e E e':ℝ}
set_option quotPrecheck false
variable (h:C.Makes){V:Sight C d p}{S:Emblems C d}
local notation "Z!"=> C.path.levels
local notation "ℓ"=> Copper.ld C.path.levels
local notation "ν"=> C.path.levels.clock.J
local notation "β"=> C.path.levels.clock.hatBeta
local notation "K" => C.path.levels.budget
local notation "L"=> C.S.block
local notation "δ"=> renal C.path.levels
local notation "T" => tab C E n

-- evaluation width
noncomputable def focus (C:Family G)(E:ℝ)(n i:ℕ):= (((C.path.levels.clock.hatBeta i)^4)*tab C E n i)⁻¹
local notation "Vt"=> focus C E n
lemma focus_ge (hx:0<E) : 0< Vt m:=inv_pos.mpr (mul_pos (pow_pos (zero_lt_one.trans ((Z!).fits.delayed _)) _) (mul_pos (Real.exp_pos _) hx))

variable (hW: Storage C D)(hG:G.Simple)
-- Conditions before feeding at all slots. Output w.Ink appears after stamp, includes engineering sign charges.
structure Pin (C:Family G) (m d:ℕ):Prop where
    lit : 12 ≤ C.path.levels.clock.J m ∧ 8≤ (C.path.levels.budget m).B
    small (E:ℝ)(n:ℕ): 0<E → 2*focus C E n (m+1)*(32*(ld C.path.levels m)^2*tab C E n (m+1))≤1
    gifts (E:ℝ)(n:ℕ): 0<E→ focus C E n m*((C.path.S.block m).val:ℝ)^d ≤ renal C.path.levels m*focus C E n (m+1)*mintK (C.path.levels.budget m).B
include hW hG
lemma feathery {w r} (L':OPE.Package C w r D) (d:ℕ):∀ᶠ m in atTop, Pin C m d:=by
    filter_upwards [(Z!).fits.deep.eventually_ge_atTop 12, Many.shifts hW hG, (Next.Rank.Station.hat_rate Z! hG).eventually (polestar 1 zero_le_one (d+1+12) 0), (Next.Rank.Station.hat_rate Z! hG).eventually_ge_atTop 64] with m hi ⟨hc,hL,hY⟩ hK hy
    let X:= (β m); let Y := (β (m+1)); have h' : 64≤ X:=hy; have hg:X ≤ Y:= Many.beta_le' (C:=C) hG m.le_succ; have hx:=lamp_nn (C:=C) m
    have hs: (ℓ m) ≤ Y:=hc.trans (hL.trans hg); have he :0 < X:= zero_lt_one.trans (Z!|>.fits.delayed _); have hφ:0 < Y:=he.trans_le hg; have hf : X^(d+1+12) ≤ mintK ((K m).B):=by simp only [one_mul,add_zero] at hK; exact hK
    refine ⟨⟨hi,L'.system.costs.stay.support _ (Nat.zero_le _)⟩,?_,?_⟩
    · intro E n hE; let U:= tab C E n (m+1); have hU: 0<U:=mul_pos (Real.exp_pos _) hE
      change 2*(Y^4*U)⁻¹*(32*(ℓ m)^2*U)≤_; suffices 64*(ℓ m)^2 ≤ Y^4 by
          field_simp; linarith only [this]
      have hz:Y≥64:= h'.trans hg; have hv: 64 ≤ Y^2:=by nlinarith only [hz]
      exact (mul_le_mul hv (pow_le_pow_left₀ (zero_le_one.trans hx) hs _) (pow_nonneg (zero_le_one.trans hx) _) (pow_nonneg hφ.le _)).trans_eq (by ring)
    intro E n hE; let U:=tab C E n (m+1); have hU:0<U:=mul_pos (Real.exp_pos _) hE
    let l':ℝ:= ((L m).val) -- ζ missing; replace
    let p:= trim (L m); have heQ: 0< p:=Copper.lit _; have hv: 1≤ l':=by unfold l'; exact_mod_cast (C.S.block m).property
    have hδ: δ m= (Y^2)⁻¹:=by unfold Bandage.renal Mallow.probe; rw [Real.rpow_neg hφ.le,Real.rpow_ofNat]
    have hp:l'⁻¹ ≤ p:=by unfold p trim; unfold l'; exact le_trans (le_of_eq (Real.rpow_neg_one ..).symm) (Real.rpow_le_rpow_of_exponent_le hv (by norm_num))
    unfold focus; rw [tab_step (m:=m),hδ]
    change (X^4* (p* U))⁻¹*l'^d ≤ (Y^2)⁻¹*(Y^4*U)⁻¹*_
    apply le_trans (b:=(Y^2)⁻¹*(Y^4*U)⁻¹ *X^(d+1+12)); swap
    · exact mul_le_mul_of_nonneg_left hf (by positivity)
    suffices hQ : l'^d*Y^2*Y^4 ≤ X^(d+1+12)*(X^4*p) by field_simp; linarith only [hQ]
    have hv: Y ≤ X^2:=hY; have hz: l' ≤ X:=hL; have hc:=show 0 ≤ l' by unfold l'; positivity
    apply (mul_le_mul (mul_le_mul (pow_le_pow_left₀ hc hz _) (pow_le_pow_left₀ hφ.le hv 2) (pow_nonneg hφ.le _) (pow_nonneg he.le _)) (pow_le_pow_left₀ hφ.le hv 4) (pow_nonneg hφ.le _) (by positivity)).trans
    have h0:X⁻¹ ≤ p:= (inv_anti₀ (show 0<l' by unfold l'; positivity) hz).trans hp
    apply le_trans _ (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h0 (pow_nonneg he.le _)) (pow_nonneg he.le _)); rw [pow_add,pow_succ]; field_simp; rw [← pow_add]; exact pow_le_pow_right₀ (by linarith only [h']) (by omega)
end YM.RG05Readout.Shadow
