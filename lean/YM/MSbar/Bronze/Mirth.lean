import YM.MSbar.Bronze.Seat
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
variable (R:PathData G)(p: Clip)(F:Nesting G c)(x:G.ColorIndex)(b:PowerSeries ℝ){a q r n:ℕ}{A B D K' H' Y w η:ℝ}
noncomputable def flush (b:PowerSeries ℝ)(i:ℕ):=PowerSeries.mk (fun j=> if j < i then PowerSeries.coeff j b else 0)
local notation "v"=>flush b r
variable (hg:0<r)(h:∀ i:ℕ,i< r → |PowerSeries.coeff i b|≤ D)(hv:μ 0 b=1)(hh:1≤ D)
include h hg hh hv
lemma burnished (k:ℕ): brim k (flush b r) D:=by
    intro i _; unfold flush; rw [PowerSeries.coeff_mk]; split; next he=>exact h i he
    next he=>rw [abs_zero]; exact zero_le_one.trans hh
lemma bust: Hush (flush b r) b r ∧ μ 0 (flush b r)=1∧ μ r (flush b r)=0:=by refine ⟨fun i hi=>?_,?_,?_⟩<;> unfold flush <;> rw [PowerSeries.coeff_mk]; exact if_pos hi; rw [if_pos hg,hv];rw [if_neg (by omega)]
local notation "Ξ"=> ink c p R
local notation "X"=> caliper c (sun G x)
noncomputable def bud (r i :ℕ)(D:ℝ):=(∑ x∈Finset.range (i+2+1), term r x i D)
lemma bud0 (i:ℕ) : 0≤ bud r i D:=by apply Finset.sum_nonneg; intro x hx; have hx:= star (flush b r) x i (bust b hg h hv hh|>.2.1) (burnished b hg h hv hh r) hh; exact (abs_nonneg _).trans (hx 0 (by omega))
variable (hp:Kind F)(hV:Expanse F 1 r) -- shadow
variable (hw:1≤w)(ht:∀ i:ℕ,i<r→Tin (Measuring.chart c G) η q n w (PowerSeries.coeff i F) A)
variable (hb:Tin (Measuring.chart c G) η q n w (PowerSeries.coeff r F) K')
local notation "S"=>ticket v F
local notation "Tκ"=> Tin (Measuring.chart c G) η q n w
noncomputable def salary (r:ℕ)(C V':ℝ):= (∑ i∈Finset.range r,bud r i C)*V'
include hp hV hw ht hb -- hv
lemma ebon : Tin (Measuring.chart c G) η q n w (PowerSeries.coeff r (Wave.ticket (flush b r) F)) (salary r D A+K') :=by
    rw [Wave.ticket,PowerSeries.coeff_mk,sum_range_succ, Nat.sub_self]
    obtain ⟨hr,hg₀,hg₁⟩:=bust b hg h ‹μ 0 b=1› hh; let t:= flush b r
    have he(p:ℕ):μ 0 ((flush b r)^p*v⁻¹^r)=1:=by
        have hp:PowerSeries.constantCoeff (flush b r)=1:=by simpa using hg₀
        simp only [PowerSeries.coeff_zero_eq_constantCoeff_apply,_root_.map_pow,_root_.map_mul,PowerSeries.constantCoeff_inv,hp,inv_one,one_pow,mul_one]
    unfold Wave.fare; simp_rw [he]; simp only [one_smul]; rw [buys (r+2) (μ r F) (by simpa only [one_mul] using hV.profile r le_rfl)]; -- rw fare syntax
    have hw':0<w:=zero_lt_one.trans_le hw; refine Tin.unite hw' ?_ hb
    unfold salary; rw [Finset.sum_mul]; refine Tin.pool hw' (fun j=>fare t F j (r-j)) (Finset.range r) _ ?_; intro j he
    have hk:j<r:=mem_range.mp he; unfold Wave.fare bud; rw [sum_mul]; have hp:= burnished b hg h ‹μ 0 b=1› hh r; refine Tin.pool hw' _ _ _ (fun i hi=> Tin.it hw' (Tin.real hw' _ (pers (ht j hk))) (mul_le_mul_of_nonneg_right (Bronze.star (flush b r) i j hg₀ hp hh (r-j) (Nat.sub_le r j)) (ht j hk|>.dec)) le_rfl) -- syntax.Tin.real
-- projection charge from norm of ticket B'/clock.M via Keeps.Z. Only need µ(T), no |lower.clock| for current. fin.Project proof direct `bley`; fare v truncated.H.K.Transport.Salary. use exact projection.Le.this.H inputs all lower `F` tin. 
end YM.MSbar.Bronze
