import YM.Integration.WilsonVacuumPreResetHomogeneousRows

/-! The original classical and loop rows under their actual formal kinetic
reset, including the affine contribution that is measured after the block. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetTorusClassicalReset
open Function Finset Lattice RG Gauge Pressure Precision Tree Stationary
open Primitives.TwoWave Primitives.TwoWave.RealSlice
open AllOrder AllOrder.Ker AllOrder.Floe AllOrder.Floe.Step AllOrder.Haiku
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open PertExtension.Series PowerSeries
open WilsonVacuumPreResetTorusGrade (evaluated)
open scoped BigOperators Classical
variable {G:Gauge}{n:Side}

theorem combined (A:Cost){P Q:PChart G n}(h:shellK 2 P)(q:shellK 2 Q)(t:ℕ)
    (z:rule (Coarse G) n):evaluated (mix A (P+Q)) t z=
      evaluated (mix A P) t z+evaluated (mix A Q) t z:=by
  have pair:mix A (P+Q)=mix A P+mix A Q:=by
    funext k r
    simp only [mix,Pi.add_apply,smul_add,sum_add_distrib]
  simp only [pair,WilsonVacuumPreResetTorusGrade.evaluated,
    flash_add (finite_shell (mix_length h)) (finite_shell (mix_length q)),map_add]

private theorem full (u:ℕ→ℝ)(t:ℕ):
    (∑ i∈range (t+1),coeff (t-i) (1:Cost)*u i)=u t:=by
  rw [sum_eq_single_of_mem t (mem_range.mpr (Nat.lt_succ_self _))]
  · simp
  · intro i hi off
    rw [mem_range] at hi
    have h:t-i≠0:=by omega
    simp [PowerSeries.coeff_one,h]

theorem original (p:Cost)(unit:constantCoeff p=1)(K:PathData G)(B:Clip)(t:ℕ)
    (z:rule (Coarse G) n):
    evaluated (mix (pace p) (front K B n)) t z=
      Pace.shiftB (Tested.term (p-1)) B K t n z:=by
  let H:=sprig (intended B K (m:=n)) 2
  let J:=sprig (turnSeries K.loop (m:=n)) 0
  have hb:shellK 2 H:=sprig_count _ 2
  have jb:shellK 2 J:=fun i a h=>sprig_count _ 0 i a (by omega)
  have homo (k:ℕ)(f:Lawn (Woods G n)→ℝ)(i a:ℕ)(hx:a+0≠i+k):
      sprig f k i a=0:=shine_dark (by omega)
  have main:=WilsonVacuumPreResetHomogeneousRows.weighted p unit H 0 2 (homo 2 _) t z
  have loop:=WilsonVacuumPreResetHomogeneousRows.weighted p unit J 0 0 (homo 0 _) t z
  have hprice (l:ℕ):Pace.ladder ((((2:ℕ):ℝ)-(0:ℕ))/2) (Tested.term (p-1)) l=coeff l p:=by
    simpa using WilsonVacuumPreResetCoin.deposited p unit (rise:=0) (grade:=0) (by omega) l
  have jprice (l:ℕ):Pace.ladder ((((0:ℕ):ℝ)-(0:ℕ))/2) (Tested.term (p-1)) l=coeff l 1:=by
    simpa only [pow_zero,mul_one] using WilsonVacuumPreResetCoin.original p unit 0 0 l
  change evaluated (mix (pace p) (H+J)) t z=_
  rw [combined _ hb jb,main,loop]
  simp_rw [hprice,jprice]
  rw [full]
  simp_rw [H,WilsonVacuumPreResetTorusDepositJet.classical]
  rw [show evaluated J t z = _ from WilsonVacuumPreResetTorusDepositJet.loop K t z]
  let u (i:ℕ):=Pace.base B K i n z
  have split (i:ℕ):coeff (t-i) p*u i=coeff (t-i) 1*u i+coeff (t-i) (p-1)*u i:=by
    rw [map_sub];ring
  rw [show (∑ i∈range (t+1),coeff (t-i) p*Pace.base B K i n z)=
        ∑ i∈range (t+1),coeff (t-i) p*u i from rfl,
    Finset.sum_congr rfl (fun i _=>split i),sum_add_distrib,full]
  simp only [Pace.shiftB,Pi.add_apply,Pace.weigh_right,Finset.sum_apply,
    Pi.smul_apply,smul_eq_mul,Tested.term,u]
  ring

end YM.Integration.WilsonVacuumPreResetTorusClassicalReset
