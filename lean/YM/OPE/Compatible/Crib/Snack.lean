import YM.OPE.Compatible.Myrtle.Affirm
import YM.OPE.Compatible.Juniper.Post
import YM.OPE.Compatible.Stamen.Thor
import Mathlib.LinearAlgebra.Vandermonde
/-! # real polynomial visibility. local Lipschitz transport for tattooed sensor and source tests. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Crown
open Function Filter Set Finset
open scoped Topology BigOperators Classical ContDiff
open Silt Cloud Tensor PertExtension Flume Flume.Page Flume.Script Jargon Score Drift GaussianScore Series Libra Shell Char Radial
variable {V E:Type}{r s t x:ℝ}{p q k:ℕ}
variable [NormedAddCommGroup E][NormedSpace ℝ E]
section line
variable {f:E→ℝ}
def windW (k:ℕ)(i:Fin (k+1)):ℝ:= i.val* ((k+1:ℕ):ℝ)⁻¹
lemma aim_w (i:Fin (k+1)): windW k i∈ Set.Icc (0:ℝ) 1:=by unfold windW; have hh : i.val < k+1:=i.isLt; push_cast; refine ⟨by positivity,?_⟩; rw [mul_inv_le_iff₀ (by positivity),one_mul]; exact_mod_cast hh.le
lemma wins(k:ℕ):Injective (windW k):= fun i j he=> Fin.ext (Nat.cast_injective (R:=ℝ) (mul_right_cancel₀ (show (((k+1:ℕ):ℝ)⁻¹)≠0 from by positivity) he))
abbrev ψLine (x v:E)(t:ℝ):= x+t • v
lemma Straff (h:anthem k f)(x v:E): ∃ a:Fin (k+1)→ℝ,∀ t:ℝ,f (ψLine x v t)=∑ i,t^i.val*a i:=by
         have ht: anthem k (f ∘ ψLine x v):=by
                have he (u:Module.Dual ℝ E) : anthem 1 ((⇑u) ∘ ψLine x v):=by
                     let y:= anthem.scale (anthem.lyric (LinearMap.id (R:=ℝ) (M:=ℝ))) (u v); convert! ((anthem.bank 1 (u x)).add y) using 1; funext t; simp only[Pi.add_apply, Pi.smul_apply,smul_eq_mul,LinearMap.id_apply,comp_apply,ψLine,map_add,_root_.map_smul]; rw[mul_comm _ t]
                simpa only [one_mul] using! h.comp he
         obtain ⟨a,hp,ha⟩:=ht.song; refine ⟨fun i=>a i.val fun _=>1, fun t=>?_⟩; rw [← Function.comp_apply (f:=f),ha,Strike,← Fin.sum_univ_eq_sum_range]; exact sum_congr rfl fun i _=> (show a i.val (fun _=>t)= _ from by rw [show (fun _:Fin i.val=>t)=fun _=> t • (1:ℝ) from funext fun x=>by rw [smul_eq_mul,mul_one]]; convert (a i.val).map_smul_univ (fun _=>t) (fun _=>1) using 1; rw [prod_const,card_univ,Fintype.card_fin,smul_eq_mul]) -- args
noncomputable def Glee (k:ℕ):= ∑ i:Fin (k+1),∑ j:Fin (k+1), ‖(Matrix.vandermonde (windW k))⁻¹ i j‖
lemma GleeHi (k:ℕ):0 ≤ Glee k:=sum_nonneg (fun _ _=> sum_nonneg (fun _ _=>norm_nonneg _))
lemma Lap (h:anthem k f)(ht:0≤t)(hv:t ≤1)(x y:E) (hc:∀ v∈ Set.Icc (0:ℝ) 1,‖f (ψLine x y v)‖ ≤ r) : ‖f (ψLine x y t)-f x‖ ≤ Glee k*r*t:=by
          obtain ⟨a,ha⟩:= Straff h x y; let V:= windW k; let A:= Matrix.vandermonde V; let X(i:Fin (k+1)):= f (ψLine x y (V i)); let Y:= A.mulVec a; have hx:Y=X:=funext fun i=>(ha _).symm; have hA : IsUnit A.det:=isUnit_iff_ne_zero.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr (wins k)); have he(i:Fin (k+1)): ‖a i‖ ≤ (∑ j, ‖A⁻¹ i j‖)*r:=by
               have he: (A⁻¹).mulVec X=a:=by rw [←hx, show Y=A.mulVec a from rfl, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hA,Matrix.one_mulVec]
               rw [← he]; change ‖∑ j,A⁻¹ i j*X j‖ ≤ _; apply (norm_sum_le ..).trans; rw [sum_mul]; apply sum_le_sum; intro j _; rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hc _ (aim_w j)) (norm_nonneg _)
          rw [show f x= f (ψLine x y 0) from (by rw [ψLine,zero_smul,add_zero]), ha, ha (0:ℝ), ← sum_sub_distrib]; apply (norm_sum_le ..).trans; rw [Glee,sum_mul,sum_mul]; refine Finset.sum_le_sum fun i _=>?_; change ‖_ * a i- _ * a i‖ ≤ (∑ j,‖A⁻¹ i j‖)*r*t; by_cases h:i.val=0
          · rw [h,pow_zero,pow_zero,sub_self,norm_zero]; exact mul_nonneg ((norm_nonneg _).trans (he i)) ht
          rw [zero_pow h, zero_mul,sub_zero,norm_mul,Real.norm_of_nonneg (by positivity),mul_comm]; exact mul_le_mul (he i) (pow_le_of_le_one ht hv h) (pow_nonneg ht _) ((norm_nonneg _).trans (he i))
lemma Lap2 (h:anthem k f)(x y:E)(ht: 1 ≤ t) (hx:‖y-x‖≤t)(hv:∀ v,‖v‖≤ ‖x‖+t→‖f v‖ ≤r) : ‖f y-f x‖ ≤ Glee k*r*‖y-x‖:=by
         by_cases hy:y=x; subst y; simp
         let b:= ‖y-x‖; let z:= b/t; let w:= z⁻¹ • (y-x); have hc:0<b:=norm_pos_iff.mpr (sub_ne_zero.mpr hy); have he:0<t:= zero_lt_one.trans_le ht; have hg:0<z:= div_pos hc he; have hs : z≤1:= (div_le_one he).mpr hx; have hW:‖w‖=t:=by unfold w; rw [norm_smul, Real.norm_of_nonneg (inv_pos.mpr hg).le]; change (b/t)⁻¹*b=t; field_simp
         rw [show f y=f (ψLine x w z) from congr_arg f (by unfold ψLine w; rw[smul_inv_smul₀ hg.ne'];abel)]; apply (Lap h hg.le hs x w ?_).trans; exact mul_le_mul_of_nonneg_left (div_le_self hc.le ht) (mul_nonneg (GleeHi _) ((norm_nonneg _).trans (hv x (le_add_of_nonneg_right he.le))))
         intro v hv'; exact hv _ ((norm_add_le ..).trans (add_le_add_right (show ‖v • w‖≤ t from by rw[norm_smul,hW,Real.norm_of_nonneg hv'.1]; exact mul_le_of_le_one_left he.le hv'.2) _))
end line
end YM.OPE.Crown
