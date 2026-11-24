import YM.LocalLTE.Vault.Gain
/-!
# Paying scalar ancestry from the LOCAL power contract

No approximations to equality of clock choices. Pre-L can raise the minimum
reset advance, useful to expose explicit costs across arbitrarily many stages.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato.Spool
open Function Filter Set Lattice RG RG.Shoot Pressure Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open Mallow ConnectedActivityE6 Push.AbsoluteSums LocalLTE LocalLTE.Vinca VoucherB LocalLTE.Fan
open Next.Scheduling.Clock Next.Scheduling.Instrument Progress.DirectedRecipe Pressure
variable {G:Gauge} (Y:Stage)(l p r K c d :ℕ)(e v t x:ℝ) (L:Side)
open YM.LocalLTE.Vault Animals
section
-- ahead. interest. all probes.
variable (G)
noncomputable def scaler (Y:Stage)(l:ℕ)(L:Side):ℝ:= (4*Dilation.sill Y.supportExponent l)*Doors.rate L
lemma scaler_pos : 0≤ scaler Y l L:=by unfold scaler Dilation.sill; have h:= (Doors.rate_pos L).le; positivity
variable (hG:G.Simple)
include hG
lemma aheadYear (W:Stage):∃ v:ℕ,∀ L:Side,v≤L.val → (scaler Y l L) * culture W c ≤1/2 ∧ 1 ≤ G.slopeConstant*Real.log L.val:=by
    let q:= (4*Dilation.sill Y.supportExponent l); let t:= q*(culture W c)*2
    obtain ⟨v,h⟩:=Doors.pre_tilt t 1; have hz : Tendsto (fun i:ℕ=>G.slopeConstant*Real.log (i:ℝ)) atTop atTop:= (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop (Gauge.slopeConstant_pos hG)
    obtain ⟨i,hi⟩:= eventually_atTop.mp (hz.eventually_ge_atTop 1)
    refine ⟨v+i,fun L hQ=>⟨?_,hi L.val (by omega)⟩⟩; have h:= (h L (by omega)).1; change (Doors.rate L)* (q*culture W c*2) ≤ 1 at h; change (q* _)*_ ≤ _; linarith only [h]
end
-- Uniform price ε.Wu. p+2 convention.
variable {t}
noncomputable def oath (n:ℕ)(x:ℝ):ℝ:= (x⁻¹)^(n+1)
lemma firSteps (n:ℕ)(x y:ℝ)(h:1 ≤x)(hxy:x+1≤y): oath n y+ (1/2:ℝ)*(x⁻¹)^(n+2) ≤ oath n x:=by
    let e:=x⁻¹; let b:= (x+1)⁻¹; have hx:0<x:= zero_lt_one.trans_le h; have he:0 < e:= inv_pos.mpr hx; have ht:0<x+1:=by linarith only [hx]
    have hβ:0≤b:= inv_nonneg.mpr ht.le; have heβ:b ≤ e:= inv_anti₀ hx (le_add_of_nonneg_right zero_le_one)
    have hp : y⁻¹ ≤ b:= inv_anti₀ ht hxy; refine le_trans (add_le_add_left (pow_le_pow_left₀ (inv_nonneg.mpr (ht.le.trans hxy)) hp (n+1)) _) ?_
    have hj: b+1/2*e^2 ≤e:=by unfold b e; field_simp; nlinarith only [h,hx]
    have hc:= mul_le_mul_of_nonneg_left hj (pow_nonneg he.le n)
    have hK: b^n*b ≤e^n*b:=mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hβ heβ n) hβ
    change b^(n+1)+1/2 *e^(n+2)≤e^(n+1)
    rw [pow_succ,pow_add,pow_succ e n]; linarith only [hc,hK]
variable (G:Gauge)
lemma oath_rate (p:ℕ) (L:Side): Rate G L (-((p+1:ℕ):ℝ)) (oath p):=by
   have hh:= (Mallow.flagE (G:=G) L (-((p:ℝ)+1)) (by linarith only [Nat.cast_nonneg (α:=ℝ) p])); push_cast; refine Rate.congr hh (?_); filter_upwards [eventually_ge_atTop (1:ℝ)] with x h
   apply Eq.symm; unfold oath; rw [Real.rpow_neg (x:=(x)) (zero_le_one.trans h)]; rw [← show (↑(p+1:ℕ):ℝ)=(p:ℝ)+1 from by push_cast;ring, Real.rpow_natCast,inv_pow] -- args. check syntax
local notation "p'" => (p:ℝ)+1
variable (ht: echoBit K < -((p+2:ℕ):ℝ))(hx:1 ≤ G.slopeConstant*Real.log L.val)
include ht hx
lemma alongT : ∀ᶠ x:ℝ in atTop, weightC x K+ oath p (betaF G x L)≤ oath p x ∧ ∀ y :ℝ,betaF G x L/2 ≤y→ y≤2*betaF G x L→ oath p x≤powerR p y:=by
    have hh:Rate G LocalLTE.Port.oneQ (echoBit K) (weightC · K):= by simpa only [Port.oneShift] using! (weight_rate K (G:=G) Port.oneQ)
    filter_upwards [eventually_ge_atTop (1:ℝ),nextPay (G:=G) Port.oneQ (weightC · K) _ _ hh ht (1/2) (by norm_num), Urns.actualG (G:=G) L ((p:ℝ)+1) (oath p) _ (oath_rate G p L) (by push_cast; linarith only [Nat.cast_nonneg (α:=ℝ) p])] with x hz hh hu
    refine ⟨le_trans (add_le_add_left ?_ _) ((add_comm ..|>.trans_le (firSteps p x (betaF G x L) hz (add_le_add le_rfl hx)))),hu⟩
    rw [Port.oneShift,Real.rpow_neg (zero_le_one.trans hz),Real.rpow_natCast, ← inv_pow] at hh; exact hh
end YM.PhysicalNext.Repeat.Legato.Spool
