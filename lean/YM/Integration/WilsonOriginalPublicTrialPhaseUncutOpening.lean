import YM.Integration.WilsonOriginalPublicTrialPhaseFittedSeats
import YM.Integration.WilsonOlderSignedOneMarkRate

/-! Native late openings for the complete uncut roster, before both cutoffs and all positions. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicTrialPhaseUncutOpening
open Finset Filter Lattice Wilson RG Source Labels Push Local Extra.Multi PhysicalNext.Repeat.Legato
open RG05Readout.Many WilsonOriginalPublicTrialPhaseRate
open scoped Classical BigOperators
variable {G:Gauge}{I:Type}[Fintype I](R:Run G)
local notation "C" => R.family
local notation "A" => (C).path
local notation "P" N:arg per:arg i:arg => (A).rep N per i

theorem original (simple:G.Simple)(d:I→ℕ):
    ∀ᶠ i:ℕ in atTop,3≤(A).levels.clock.J i ∧
      Fintype.card I*Fintype.card Signed≤apron (A).levels i ∧ ∀N per,i≤N →
      hitWidth (P N per i).p*kappa (A) i≤1 ∧ kappa (A) i≤1 ∧
      volume (P N per i).p.B*(A).levels.clock.forcedAllowance i≤Real.log 2/2 ∧
      ∀k,∀z:Site ((C).side i per),((((C).localSection (d k)).footprint z).card:ℝ)*(A).levels.clock.forcedAllowance i≤1:=by
  classical
  let n:ℝ:=∑k:I,(((C).localSection (d k)).stencil.card:ℝ)
  have np:0≤n:=sum_nonneg (fun _ _=>Nat.cast_nonneg _)
  have np1:0<1+n:=by linarith
  let ε:=min (1/(1+n)) (min 1 (Real.log 2/2))
  have ep:0<ε:=lt_min (one_div_pos.mpr np1) (lt_min zero_lt_one (half_pos (Real.log_pos (by norm_num))))
  have e1:ε≤1:=(min_le_right ..).trans (min_le_left ..)
  have el:ε≤Real.log 2/2:=(min_le_right ..).trans (min_le_right ..)
  have en:ε≤1/(1+n):=min_le_left .. 
  let load:=Fintype.card I*Fintype.card Signed
  have grades:=((A).levels.fits.deep).eventually_ge_atTop 3
  have loadable:=(((A).levels.fits.deep).comp (tendsto_add_atTop_nat 1)).eventually_ge_atTop load
  filter_upwards [grades,loadable,WilsonOlderSignedOneMarkRate.paid R simple 0 0 (by norm_num : 0 < (1:ℝ)) ep] with i grade room income
  have blocks:0<((C).S.block i).val^4:=pow_pos ((C).S.block i).property _
  refine ⟨grade,room.trans ((Nat.le_add_right _ 2).trans (Nat.le_mul_of_pos_right _ blocks)),?_⟩
  intro N per live
  let B:=((A).levels.budget i)
  have shape:(P N per i).p=B:=(R.makes.wilson.represents N per i live).vac
  have one:1≤hitWidth B:=by
    unfold hitWidth
    exact_mod_cast (one_le_pow₀ (show 1≤B.B+B.B+1 by omega):1≤(B.B+B.B+1)^4)
  have kp:0<kappa (A) i:=Real.sqrt_pos.mpr (Real.exp_pos _)
  have sq:(A).levels.clock.forcedAllowance i=(kappa (A) i)^2:=(Real.sq_sqrt (Real.exp_pos _).le).symm
  have pay:=income N per live i le_rfl 1 zero_le_one (by simp)
  have cash:hitWidth B*kappa (A) i≤ε:=by
    calc
      _=(hitWidth B*(A).levels.clock.forcedAllowance i)*1/kappa (A) i:=by rw [sq];field_simp
      _≤ε:=by simpa only [B,LocalComparison.forcedDivisor,kappa,mul_one,pow_zero] using pay
  have k0:kappa (A) i≤ε:=(le_mul_of_one_le_left kp.le one).trans cash
  have k1:=k0.trans e1
  have small: (A).levels.clock.forcedAllowance i≤ε:=by
    rw [sq,pow_two];exact (mul_le_of_le_one_right kp.le k1).trans k0
  rw [shape]
  refine ⟨cash.trans e1,k1,?_,?_⟩
  · have same:volume B.B=hitWidth B:=by simp [volume,hitWidth]
    rw [same]
    rw [sq,pow_two,←mul_assoc]
    exact (mul_le_of_le_one_right (mul_nonneg (zero_le_one.trans one) kp.le) k1).trans (cash.trans el)
  · intro k z
    have fp:((((C).localSection (d k)).footprint z).card:ℝ)≤(((C).localSection (d k)).stencil.card:ℝ):=by
      exact_mod_cast (Finset.card_image_le : (((C).localSection (d k)).footprint z).card≤((C).localSection (d k)).stencil.card)
    have up:(((C).localSection (d k)).stencil.card:ℝ)≤n:=single_le_sum (f:=fun t:I=>(((C).localSection (d t)).stencil.card:ℝ)) (fun t _=>Nat.cast_nonneg _) (mem_univ k)
    calc
      _≤(1+n)*(1/(1+n)):=mul_le_mul (fp.trans (up.trans (by linarith))) (small.trans en) (Real.exp_pos _).le np1.le
      _=1:=by field_simp

end YM.Integration.WilsonOriginalPublicTrialPhaseUncutOpening
end
