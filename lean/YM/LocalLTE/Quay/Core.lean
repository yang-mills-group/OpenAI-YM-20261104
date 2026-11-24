import YM.LocalLTE.Sail.Tunes
import YM.LocalLTE.Concourse.Core
/-!
# True coordinate contraction for the non-unit block

The stage reserve may be extremely generous, yet purchases just with
Worth are not directly summable. Here take advantage of the positive frame grades
and exact propagation of the unit. Leave unit contributions explicit (especially
mixed moments can carry nonzero ones). Uses the **actual** aperture's determinant;
non-block contributions move with its true exponent.
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Concourse
open Function Filter Lattice Wilson RG Source Labels Extra.Histories Motion
open LocalLTE.Vinca LocalLTE.FrameBox AnalyticBridge VerifiedReset Collection Price PhysicalNext.Repeat Blush
open Push Local Planned.GuardedAtom LocalLTE.River YM.MergeProof
open Finset MeasureTheory
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{H:History G}{N m p d:ℕ}{F:Labels.Frame G d}
local notation "O" => H.rep N p m
local notation "P'" => H.rep N p (m+1)
local notation "κ" => Real.sqrt (H.levels.clock.forcedAllowance m)
local notation "κ'" => Real.sqrt (H.levels.clock.forcedAllowance (m+1))
open Legato.Bandage.Harmonics
open YM.Bid Work.G08
-- sharpen even on *all* directions.Purity proof from actual.Con.Step at nonunit inputs.
lemma layer (i:F.Index)(hi:i≠0)(x:F.Coeff)(L:Side): (L.val:ℝ)*‖Bid.vowel F L x i‖ ≤ ((L.val:ℝ)^d)*‖x i‖:=by
   have ht:= Concourse.weightPositive F i hi; have hb:=F.bound i
   unfold vowel; rw [norm_mul,norm_pow,Complex.norm_natCast,← mul_assoc,mul_comm (_:ℝ) ((_ :ℝ) ^ _),← pow_succ]; exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ ((by exact_mod_cast L.property):1 ≤ (L.val:ℝ)) (by omega)) (norm_nonneg _)
variable (L :Side)
lemma blended (x:F.Coeff): (L.val:ℝ) * F.coeffSize (vowel F L (F.core x)) ≤ ((L.val:ℝ)^d)*F.coeffSize (F.core x):=by
    unfold Labels.Frame.coeffSize; rw [mul_sum,mul_sum]; refine sum_le_sum fun i _=>?_ ; by_cases h:i=0; · subst i; simp [vowel,Frame.core]
    exact layer i h (F.core x) L
local notation "T"=> H.S.block m
variable (W: Worth) (H)
lemma cone_core (hb: Bank W H.levels) (u v:F.Coeff) {r t:ℝ} (hd:direction H W m F u (F.core v) r t) (hv:t≤(H.levels.params (m+1)).columns *F.coeffSize (F.core v)):F.coeffSize u ≤ 2*W.K (H.levels.clock.J (m+1))*F.coeffSize (vowel F T (F.core v)):=by
   let z:= H.levels.clock.J (m+1); let C:= W.K z
   let s:= (H.levels.params (m+1)).columns; let e:= barunit T; let y:=vowel F T (F.core v)
   have hC:1≤C:=W.prices _; have hcc : 0 ≤ 2*C := mul_nonneg zero_le_two (zero_le_one.trans hC)
   have hcz : C ≤ W.K (z+1) := W.growth z.le_succ; obtain ⟨he0, he⟩ : 0 ≤ e ∧ 2*C*e*(1+s) ≤ 1 := bank_slack hC hcz (H.levels.params (m+1)).columns_ge (hb _)
   obtain ⟨_,ht,B,hB,hE,hR⟩:=hd
   have hcost : ∀ x, F.coeffSize (B x) ≤ C*F.coeffSize x ∧ F.coeffSize (B.symm x) ≤ C*F.coeffSize x := fun x => ⟨(hB x).1,(hB x).2.1⟩
   have hm' : F.coeffSize (F.core (F.core v))+t ≤ (1+s)*F.coeffSize (F.core v):=by rw [add_mul,one_mul]; exact add_le_add (Work.G08.size_core ..) hv
   have h: 2*C*F.coeffSize (u-B y) ≤ F.coeffSize y:= calc
      _ ≤ 2*C*(e*((1+s)*F.coeffSize (F.core v))) := mul_le_mul_of_nonneg_left (hE.trans (mul_le_mul_of_nonneg_left hm' he0)) hcc
      _ = (2*C*e*(1+s))*F.coeffSize (F.core v) := by ring
      _ ≤ 1*F.coeffSize (F.core v) := mul_le_mul_of_nonneg_right he (size_nonneg F _)
      _ ≤ F.coeffSize y := by rw [one_mul]; exact (size_vowel F T (F.core v)).1
   exact (lead_bounds F C hC B hcost u y h).2
lemma bank_k (i:ℕ)(hb:Bank W H.levels): 2*W.K (H.levels.clock.J (i+1))≤(1/2:ℝ)*(H.S.block i).val:=by
   let l:= H.S.block i; let j:= H.levels.clock.J (i+1); have h := hb i; let s:= (H.levels.params (i+1)).columns; have hp:1≤(l.val:ℝ):= by exact_mod_cast l.property
   have hz: puffs l ≤ (l.val:ℝ):= (Real.rpow_le_rpow_of_exponent_le hp (by norm_num:(1:ℝ)/8≤1)).trans_eq (Real.rpow_one _)
   have hk: W.K j ≤ W.K (j+1)^6:= (W.growth j.le_succ).trans (by simpa using pow_le_pow_right₀ (W.prices (j+1)) (show 1 ≤ 6 by decide))
   have hs : 1 ≤ (1+s)^2:= one_le_pow₀ (le_add_of_nonneg_right (zero_le_one.trans (H.levels.params (i+1)).columns_ge))
   change 2*W.K j ≤ 1/2* (l.val:ℝ); linarith only [(show 100000*W.K (j+1)^6 * (1+s)^2 ≤ _ from h).trans hz,hs,hk,W.prices j, mul_le_mul_of_nonneg_left hs (pow_nonneg (zero_le_one.trans (W.prices (j+1))) 6)]
variable (P:Voice F H p (m+1))(Q:Voice F H p m) {A:Hol G} (D:SectionData F)
variable (hp:Heard D H N p A (m+1) P) (hq:Heard D H N p A m Q) (ht:Responds D H N p W m P Q)
set_option quotPrecheck false
local notation "g" i:max=> Sail.sampleNorm H N d i
local notation "s"=> H.S
local notation "I"=> P.index
local notation "J"=> Q.index
local notation "Y"=> (H.S.a N:ℂ)^d
local notation "z"=> (Sail.sampleNorm H N d (m+1))
local notation "c"=> (Sail.sampleNorm H N d m)
include hp hq
lemma exact_floor : c • Q.index (P.index.symm F.e0)= z • F.e0:=by
   let F₀:= (P.index.symm F.e0); let t(i:ℕ):ℂ:= (H.S.a i:ℂ)^d
   have hv' : P.index.symm (unitVec F H (m+1))=unitVec F H N := (P.index.symm_apply_eq).mpr hp.unit.symm
   have ht (i:ℕ) : g i *t i= Y:=by unfold Sail.sampleNorm YM.MergeProof.alto t; rw [mul_assoc,inv_mul_cancel₀, mul_one]; exact pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (H.S.a_pos i).ne')
   calc
     _ = ( (c*((t (m+1))⁻¹)) • Q.index (P.index.symm (unitVec F H (m+1)))) := by
         have hv:P.index.symm F.e0=(t (m+1))⁻¹ • P.index.symm (unitVec F H (m+1)) := by
             rw [← map_smul,unitVec,inv_smul_smul₀]
             unfold t; exact pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (H.S.a_pos _).ne')
         rw [hv,map_smul,smul_smul]
     _ = _:=by rw [hv',hq.unit]; unfold unitVec; rw [smul_smul]; rw [show (H.S.a m:ℂ)^d=t m from rfl]; congr 1; rw [mul_right_comm, ht m,← ht (m+1), mul_assoc,mul_inv_cancel₀,mul_one]; unfold t; exact pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (H.S.a_pos _).ne')
include ht
-- True standard estimate and additional core contraction.
set_option maxHeartbeats 330000 in
lemma forwardT (hb:Bank W H.levels) (x:F.Coeff) : ‖c‖ * F.coeffSize (F.core (Q.index x)) ≤ 1/2 * (‖z‖ * F.coeffSize (F.core (P.index x))) ∧ ‖c‖ * F.coeffSize (Q.index x) ≤ ‖z‖*F.coeffSize (P.index x)+ 1/2 * (‖z‖ * F.coeffSize (F.core (P.index x))):=by
    let y:= P.index x; let v:=P.index.symm (F.core y); let u:=Q.index v
    have hh: P.charge v ≤ _:= (hp.cone v).trans (show (H.levels.params (m+1)).columns*F.coeffSize (F.core (P.index v))≤ (H.levels.params (m+1)).columns*F.coeffSize (F.core y) from ?_); swap
    · unfold v; rw [LinearEquiv.apply_symm_apply]; exact mul_le_mul_of_nonneg_left (size_core ..) (zero_le_one.trans (H.levels.params _).columns_ge)
    have hC:= ht.tally v; rw [hp.currents,hq.currents,show P.index v=F.core y from (P.index.apply_symm_apply ..)] at hC
    let C₀:= W.K (H.levels.clock.J (m+1)); let w:= vowel F T (F.core y); let k0:=(T).val; have hH:(k0:ℝ)*F.coeffSize u≤ (1/2* (k0:ℝ)) *((k0:ℝ)^d *F.coeffSize (F.core y)):=by
        calc
           _ ≤ (k0:ℝ)*(2*C₀*F.coeffSize w):= mul_le_mul_of_nonneg_left (cone_core H W hb u y hC hh) (by positivity)
           _ = (2*C₀)* ((k0:ℝ)*F.coeffSize w):= by ring
           _ ≤ _:=mul_le_mul (bank_k H W m hb) (blended T y) (mul_nonneg (Nat.cast_nonneg _) (size_nonneg ..)) (by positivity)
    have hv : ‖c‖* F.coeffSize u ≤ 1/2*(‖z‖* F.coeffSize (F.core y)):= by
       have hz₀:= Sail.sample_step H (N:=N) (d:=d) (m:=m); rw [hz₀,norm_mul,norm_pow,Complex.norm_natCast]; apply le_of_mul_le_mul_left _ (show 0 < (k0:ℝ) from by exact_mod_cast (T).property); exact (le_of_eq (by ring : ((k0:ℝ) * _)= ‖c‖*((k0:ℝ)* F.coeffSize u))).trans ((mul_le_mul_of_nonneg_left hH (norm_nonneg _)).trans (by unfold k0; exact le_of_eq (by ring)))
    -- loss on unit is *injected* but not recurrent.Children.Primary.
    have hvc:x= y 0 • P.index.symm F.e0 +v:= by apply P.index.injective; rw [map_add,map_smul,P.index.apply_symm_apply]; exact core_split F y|>.trans (congr_arg (fun a=> _+a) (P.index.apply_symm_apply (F.core y)).symm)
    have hq': c • Q.index x = z • (y 0 • F.e0)+ c • u:=by rw [hvc,map_add,smul_add,map_smul,smul_comm c,exact_floor H P Q D hp hq,smul_comm (y 0)] -- order
    constructor
    · rw [← Size.smul, ← map_smul,hq',map_add,map_smul,map_smul,Size.unit_core,smul_zero,smul_zero, zero_add,map_smul,Size.smul]; exact (mul_le_mul_of_nonneg_left (size_core ..) (norm_nonneg _)).trans hv
    rw [← Size.smul,hq']; apply (Size.add ..).trans; rw [Size.smul,Size.smul]
    rw [Size.smul]; apply add_le_add (mul_le_mul_of_nonneg_left _ (norm_nonneg _)) hv; rw [show F.coeffSize F.e0=1 from Size.size_axis ..,mul_one]; exact (norm_le_pi_norm y 0).trans (norm_le_size ..)
end YM.LocalLTE.Concourse
