import YM.MSbar.Fusion.Give
import YM.MergeProof.North.Economist
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Rafts
open Function Filter Lattice RG Supply MeasureTheory Finset Set Push Input
open PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Legato.Bandage PhysicalNext.Repeat.Mallow
open Ribbons (Note whence briar whack billed banket plumN)
open scoped Topology BigOperators Classical
variable {G:Gauge}
def glyph (A:Levels G)(d:ℕ)(m:ℕ):= (d+1)*65536*(A.S.block m).val*((A.budget m).B)^2
-- enhance P AFTER-L gates
structure Accept (A:Levels G):Prop where
   ready d:∀ᶠ i in atTop, ((A.budget (i+1)).supportExponent+1/2)*((((2*glyph A d i+1)^4:ℕ):ℝ)) ≤ Real.sqrt (A.clock.hatBeta i)
lemma fewL (M : ℕ) (c:ℝ)(hc:0<c) : ∀ᶠ x:ℝ in atTop,c*((((M*Nat.ceil ((Real.log x)^2)^2+1)^4:ℕ):ℝ)) ≤ Real.sqrt x:=by
   let g:ℝ:= (4*M+1:ℝ)^4; have hg:0<g:=by dsimp only [g]; positivity
   have ht':= (isLittleO_log_rpow_rpow_atTop ((16:ℕ):ℝ) (show 0<(1/2:ℝ) by norm_num)).def (inv_pos.mpr (mul_pos hc hg))
   filter_upwards [ht',eventually_gt_atTop (0:ℝ),Real.tendsto_log_atTop.eventually_ge_atTop 1] with x ht hx hv
   rw [Real.rpow_natCast, ← Real.sqrt_eq_rpow,Real.norm_of_nonneg (Real.sqrt_nonneg _),Real.norm_of_nonneg (pow_nonneg (zero_le_one.trans hv) _)] at ht
   have he: c*g * (Real.log x)^16 ≤ Real.sqrt x:= by
     exact (mul_le_mul_of_nonneg_left ht (mul_pos hc hg).le).trans_eq ((mul_inv_cancel_left₀ (mul_pos hc hg).ne' _))
   have hV:1 ≤ (Real.log x)^2:=one_le_pow₀ hv
   have hz:((Nat.ceil ((Real.log x)^2)):ℝ) ≤ 2*(Real.log x)^2:=by linarith only [Nat.ceil_lt_add_one (sq_nonneg (Real.log x)),hV]
   have hh₁:(M:ℝ)*(Nat.ceil ((Real.log x)^2):ℝ)^2+1 ≤ (4*M+1)*(Real.log x)^4:=by
       calc
         _ ≤ (M:ℝ)*(2*(Real.log x)^2)^2+(Real.log x)^4:=add_le_add (by gcongr) (one_le_pow₀ hv)
         _ =_:=by ring
   push_cast; apply le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hh₁ 4) hc.le) _; unfold g at he; ring_nf at he ⊢; exact he
variable {A:Sheet G}{P:Rolls A}{T:Protection P}
open Push.PriceCompiler
lemma asks : ∃ V:Delays T,∀ V':Delays T,DelayLe V V' → ∀ (D:Bar V')(W:Wait D) (a:Levels G),Paid W a→Accept a:=by
   let X i:= ((A.profile i).supportExponent+1/2); have hX(i):0<X i:=by unfold X; linarith only [ (A.profile i).price_pos]
   let L(i):=(P.L i).val; let Y(i):= (i+1)*65536*L i*2
   choose Z hZ using fun i=>eventually_atTop.mp (fewL (Y i) _ (hX i))
   refine ⟨⟨Z,fun _ _=>0,fun _=>1,fun _=>1⟩,fun B he D W a hx=> ⟨fun d=>?_⟩⟩
   filter_upwards [(tendsto_add_atTop_nat 1).eventually (a.fits.deep.eventually_ge_atTop d)] with m hm
   let I:= a.clock.J (m+1); let n:=(a.clock.hatBeta m); have ht:Z I ≤ n :=(he.beta I).trans (hx.pays _)
   change d ≤ I at hm; have h := hZ I n ht
   have hv: (a.budget (m+1)).supportExponent+1/2=X I:=by unfold X; change (a.clock.stage _).supportExponent+_=_; rw [hx.stage]
   rw [hv]; apply le_trans (mul_le_mul_of_nonneg_left ((Nat.cast_le (α:=ℝ)).2 (pow_le_pow_left' (add_le_add_left (?_) _) _)) (hX I).le) h
   let u:= (a.budget m).B; have hz:(a.S.block m).val=L I:=by change _ = (P.L I).val; rw [←hx.lengths]; rw [a.fits.sameFactor];
   change 2*((d+1)*65536*_ * u^2) ≤ (I+1)*65536*L I*2*u^2; rw [hz]; trans 2*((I+1)*65536*L I*u^2)
   · gcongr
   exact Nat.le_of_eq (by ring)
variable (C:Family G)
set_option quotPrecheck false
local notation "P₀"=> C.path.levels
local notation "b"=> C.path.levels.budget
local notation "B"=> glyph C.path.levels
lemma ruled (hG:G.Simple) (hh:Accept C.path.levels)(d:ℕ): Note C.S (fun i=> Real.exp (((b (i+1)).supportExponent+1/2)*((((2*B d i+1)^4:ℕ):ℝ)))) 0:=by
    refine ⟨fun i=> Real.exp_pos _,?_⟩; simp_rw [Real.log_exp]; refine squeeze_zero' (Eventually.of_forall fun i=>div_nonneg (mul_nonneg (add_nonneg (b (i+1)|>.exponent_pos.le) (by norm_num)) (by positivity)) (Shoot.scale_nn _ _)) ((hh.ready d).mono fun i hi=> ?_) (whence C hG); exact div_le_div_of_nonneg_right hi (Shoot.scale_nn _ _)
lemma ratios : Note C.S (fun i=> ((C.S.block i).val:ℝ)) 0:= by
    refine ⟨fun i=> by positivity,?_⟩; exact C.path.levels.fits.mesh
variable {r:ℕ→ℕ}{D':∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
lemma purse (hG:G.Simple)(hV:Velour C (renal C.path.levels) r D')(d:ℕ): Note C.S (fun i=> (B d i:ℝ)) 0:=by
    unfold glyph; push_cast; exact (((Ribbons.Note.notes C.S _ (by positivity :0 < (d+1:ℝ)*65536)).mills (ratios C)).mills ((briar C hG hV).powerN 2)).swapP (by norm_num)
end YM.MergeProof.Rafts
