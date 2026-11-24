import YM.RG17.Relief
/-!
# Coupling credit, no asymptotic start costs after original Run, STOP length independent.

p parameter PERIOD. d for requested precision in even powers. Use actual beta in band. Use different coarser ruler
(Uniform hat) for inductive credit. Products accounted at full exponential. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG17
open Function Filter Set Lattice RG Pressure Shoot Supply Wilson MeasureTheory Finset
open PhysicalNext.Repeat.Legato RG01 RG01.Kernel Pert.Asymptotics
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
set_option quotPrecheck false
variable {G:Gauge} (R:Run G){m N p :ℕ}(h:G.Simple)
local notation "C" => R.family
local notation "S"=>R.family.S
local notation "β"=>R.family.path.levels.clock.hatBeta
local notation "g"=> regulatorRun R.family
-- even OUT order (d=0 already outputs d+1=1 i.e. g²). one-step asks 2 higher. Later convert as needed.
def tally (d:ℕ) (a:ℝ):= a⁻¹^(d+1)
private lemma tally_le {x y a:ℝ}(hx:0<x)(ha:0<a)(hy:x+a ≤ y)(d:ℕ) : a*y⁻¹^(d+2)+tally d y ≤ tally d x:=by
   have hxy:x ≤ y:=by linarith
   have hh:0<y:=hx.trans_le hxy; unfold tally
   have ht:(x+a)*1 ≤ y:=by linarith
   have hr:y⁻¹ ≤ x⁻¹:= inv_anti₀ hx hxy
   have hi:1/y+a/y^2 ≤ 1/x :=by field_simp; nlinarith only [mul_le_mul_of_nonneg_left hy hh.le,mul_le_mul_of_nonneg_right hxy ha.le]
   simp only [div_eq_mul_inv,← inv_pow,one_mul] at hi
   apply le_trans (le_of_eq (show a*y⁻¹^(d+2)+y⁻¹^(d+1)= (y⁻¹+a*y⁻¹^2)* y⁻¹^d from by ring))
   rw [pow_succ' x⁻¹]; exact mul_le_mul hi (pow_le_pow_left₀ (inv_pos.mpr hh).le hr _) (pow_nonneg (inv_pos.mpr hh).le _) (inv_pos.mpr hx).le

def leap (G:Gauge) := G.slopeConstant* Real.log 2
lemma leaps' (hG:G.Simple) : 0<leap G:= mul_pos (Gauge.slopeConstant_pos hG) (Real.log_pos one_lt_two)

-- accounting uniform base at any m
def pocket (d m:ℕ):ℝ:= tally d ((β) m)  -- beware this notation R variable capture!
lemma pocket_pos (d m:ℕ): 0 < pocket R d m:= pow_pos (inv_pos.mpr (zero_lt_one.trans ((C).path.levels.fits.delayed m))) _
lemma pocket_one (d m:ℕ) : pocket R d m ≤ 1:= pow_le_one₀ (inv_pos.mpr (zero_lt_one.trans ((C).path.levels.fits.delayed m))).le (inv_le_one_of_one_le₀ (((C).path.levels.fits.delayed m).le))
lemma payBand (hm:m≤ N) :
    0<g N p m ∧ (g N p m)^2 ≤ 2*((β) m)⁻¹ ∧ ((β) m)⁻¹ ≤ 2*(g N p m)^2:=by
   let x:=(β) m; let y:=(C).path.β N p m
   have H:1<x:= (C).path.levels.fits.delayed _; have hY:=R.makes.wilson.represents N p m hm
   have he:x/2 ≤ y:= hY.band.1; have hp:y ≤ 2*x:=hY.band.2
   have hz: 0<x:=zero_lt_one.trans H
   have hy:0<y:=by linarith only [hz,he]
   refine ⟨inv_pos.mpr (Real.sqrt_pos.mpr hy), ?_⟩
   change (Real.sqrt y)⁻¹^2 ≤ _ ∧ _ ≤ 2*(Real.sqrt y)⁻¹^2; rw [inv_pow, Real.sq_sqrt hy.le]
   change y⁻¹ ≤ 2*x⁻¹ ∧ x⁻¹ ≤ 2*y⁻¹; constructor <;> field_simp <;> linarith only [he,hp]
lemma inPocket (d:ℕ)(hm:m≤ N):pocket R d m ≤ 2^(d+1) * regulatorRun R.family N p m^(2*(d+1)):= by
    rw [pow_mul, ← mul_pow]; exact pow_le_pow_left₀ (inv_pos.mpr (zero_lt_one.trans ((C).path.levels.fits.delayed m))).le (payBand R hm).2.2 _
def shorts (d:ℕ):= 2*(d+2)
include h
lemma payShorts (d:ℕ)(hm:m<N):regulatorRun R.family N p (m+1)^(shorts d) ≤ 2^(d+2)/leap G * (pocket R d m- pocket R d (m+1)):=by  -- include h
   let x:=(β) m; let y:=(β) (m+1)
   have ha:=leaps' h
   have hz: x+leap G ≤ y:=by
      unfold x y Calendar.hatBeta leap; rw [Schedule.scale_succ,mul_add]; rw [← add_assoc]; apply add_le_add_right; exact mul_le_mul_of_nonneg_left (Real.log_le_log two_pos (show (2:ℝ)≤ ((S).block m).val from by exact_mod_cast (show 2 ≤ ((S).block m).val from Nat.le_trans (by norm_num : 2 ≤ 3) ((S).block_large m)))) (Gauge.slopeConstant_pos h).le
   have hx:0<x:=zero_lt_one.trans ((C).path.levels.fits.delayed m)
   have hp: leap G*y⁻¹^(d+2) + pocket R d (m+1) ≤ pocket R d m:= tally_le hx ha hz d
   unfold shorts; rw [pow_mul]
   let U:=2^(d+2)/leap G
   have hg y': 0 ≤ (y':ℝ)^2:=sq_nonneg y'
   refine (pow_le_pow_left₀ (hg _) (payBand R hm).2.1 (d+2)).trans (le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_left (show leap G * y⁻¹^(d+2) ≤ pocket R d m -pocket R d (m+1) from by linarith only [hp]) (show 0 ≤ U by unfold U; positivity)))
   change (2*y⁻¹)^(d+2)= U*(leap G *y⁻¹^(d+2)); unfold U; rw [mul_pow]; field_simp

omit h
lemma earnings (d:ℕ) {c:ℝ} (hc:0≤c) :∃ t:ℝ, 0≤ t ∧ ∀ N p m (_h:m≤N), Real.exp (c*pocket R d m) - 1 ≤ t * regulatorRun R.family N p m^(2*(d+1)):=by
    let A:= c *2^(d+1); refine ⟨Real.exp c*A, mul_nonneg (Real.exp_pos _).le (by unfold A; positivity),fun N p m hm=>?_⟩
    let V:= c*pocket R d m; have hv:0 ≤ V:= by unfold V; positivity [pocket_pos R d m]
    have hx:= mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-V)) (Real.exp_pos V).le
    rw [← Real.exp_add,neg_add_cancel,Real.exp_zero] at hx
    apply le_trans (b:=Real.exp V * V) (by change Real.exp V - 1 ≤ _; linarith only [hx]); unfold V A; rw [mul_assoc, mul_assoc c]
    apply mul_le_mul (Real.exp_monotone (by have hb:= mul_le_mul_of_nonneg_left (pocket_one R d m) hc; rwa [mul_one] at hb)) (mul_le_mul_of_nonneg_left (inPocket R d hm) hc) hv (Real.exp_pos _).le
end YM.RG17
