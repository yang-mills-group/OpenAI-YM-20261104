import YM.MSbar.Bronze.Mirth
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Bronze
open Function Filter Whisk Lis Measuring Cacao CrossH Push Uniform Lattice RG Pressure Matrix
open Precision Gauge Midpoint Rolling Tramp Exterior Tree Wilson Laurent Bloch Wave Tensor
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {G:Gauge}{c:Side}
open MvPolynomial Finset
local notation "T"=> Measuring.chart c G
local notation "μ"=>PowerSeries.coeff
local notation "V"=>PowerSeries ℝ
local notation "E"=>Cacao.Pot (Primary c G)
variable (F:Nesting G c)(x:G.ColorIndex)(Ω:Cacao.Pot (Primary c G))(b: PowerSeries ℝ){a q r n:ℕ}{A B D K H Y w η:ℝ}
local notation "v"=>flush b r
variable (hg:0<r)(h:∀ i:ℕ,i< r → |PowerSeries.coeff i b|≤ D)(hv:PowerSeries.coeff 0 b=1)(hh:1≤ D)
variable (hp:Kind F)(hV:Expanse F 1 r)(hw:1≤w)
variable (ht:∀ i:ℕ,i<r→Tin (Measuring.chart c G) η q n w (PowerSeries.coeff i F) A)(hb:Tin (Measuring.chart c G) η q n w (PowerSeries.coeff r F) K)
variable (hA:0 ≤ B)(hq:1 ≤ n)(hr:Tin (Measuring.chart c G) η q n w Ω (w^2*B))
local notation "P₀"=> caliper c (sun G x)
variable (hy:1 ≤|caliper c (sun G x) Ω|)(hN:2≤q)(hK: Keeps (bley b F Ω) r (sun G x))(hQ:0≤η)
local notation "g!"=>salary r D A+K
local notation "C!"=>PowerSeries.coeff r b
local notation "S"=> bley b F Ω
noncomputable def straw (D:ℝ)(r:ℕ) := ((r+1:ℕ)*D:ℝ)^2
include hg h hv hh hp hV hw ht hb hA hq hr hy hN hK hQ
lemma prestige : Tin (Measuring.chart c G) η q n w (PowerSeries.coeff r (bley b F Ω)) ((salary r D A+K)*(1+B)) ∧ |PowerSeries.coeff r b|≤ (salary r D A+K)/w^2+straw D r:=by
    have he:= (ebon F b hg h hv hh hp hV hw ht hb); let T':=Wave.ticket v F; let P:= μ r T'
    let K':= caliper c (sun G x); have h0:=he.dec; have hw':0<w:=zero_lt_one.trans_le hw
    let g₁:= (salary r D A+K); let g₀:=g₁/w^2; let a:=2*C!+ μ r (v^2-1)
    obtain ⟨hx,hD,hz⟩:=bust b hg h hv hh; have hs: μ r S=P-a • Ω:=by rw [hx.wagon hp hD hg,hz,sub_zero]; rw [Wave.bley,_root_.map_sub,PowerSeries.coeff_mk,sub_sub]; unfold a; rw [add_smul, add_comm]
    have hy : |a| ≤ g₀:=by
        have h: a*K' Ω=K' P:=by apply Eq.symm; apply sub_eq_zero.mp; have h₀:= hK.sitting r le_rfl; rw [hs,map_sub,map_smul] at h₀; exact h₀
        apply (le_mul_of_one_le_right (abs_nonneg _) hy).trans; change |a| *|K' Ω| ≤ _; rw [← abs_mul,h]; exact Bronze.quant x P hQ (fun i=> he.fan 1 hq i) hN -- type
    constructor
    · rw [hs,sub_eq_add_neg, ← neg_smul]; apply (Tin.unite hw' he (Tin.real hw' _ hr)).it hw' ?_ le_rfl; rw [abs_neg]; apply (add_le_add_right (mul_le_mul_of_nonneg_right hy (show 0 ≤w^2*B from (by positivity))) _).trans_eq; unfold g₀ g₁; field_simp
    have hh : |μ r (v^2-1)| ≤ straw D r:=by rw [_root_.map_sub,PowerSeries.coeff_one,if_neg hg.ne',sub_zero]; exact Bronze.brim_pow v (burnished b hg h hv hh r) 2 (zero_le_one.trans hh) _ le_rfl
    have hm:(2:ℝ)*|C!|=|a-μ r (v^2-1)|:=by rw [show a- μ r (v^2-1)= 2*C! from add_sub_cancel_right ..]; rw [abs_mul,abs_of_pos (by norm_num : 0 < (2:ℝ))]
    exact (le_mul_of_one_le_left (abs_nonneg _) one_le_two).trans (hm.trans_le ((abs_sub ..).trans (add_le_add hy hh)))
end YM.MSbar.Bronze
