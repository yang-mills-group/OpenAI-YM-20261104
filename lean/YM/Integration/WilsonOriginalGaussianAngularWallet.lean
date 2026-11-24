import YM.Integration.WilsonOriginalCompoundVertex
import YM.Integration.WilsonVacuumPreResetMeasuredCoin

/-! The same enrolled cover action pays for a finite field evaluation in a
single block. The period only enters through the number of angular slots.
A change of the common field keeps its entire signed positive-rank table. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonOriginalGaussianAngularWallet
open Function Filter Finset Lattice Laurent Bloch Wilson RG Precision Exterior Tree Matrix PowerSeries
open PhysicalNext.Repeat.Legato WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank
open WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open FormalBulk08 Next.Foundations Org Input PhysicalNext WilsonCoeffUV.Bank.Realm WilsonCoeffUV.Cosmos
open WilsonOriginalCompoundVertex WilsonVacuumPreResetTorusGrade
open scoped BigOperators Classical Topology

theorem single {U:Type}[Fintype U]{r:ℕ}(T:Ten ℝ U r){b:ℝ}(paid:∀v,|T v|≤b)(x:U→ℝ):
    |MvPolynomial.eval x (Blue.paint r T)|≤b*((Fintype.card U:ℝ)*‖x‖)^r:=by
  rw [Blue.paint,Blue.toll]
  apply (Finset.abs_sum_le_sum_abs ..).trans
  have one (v:Fin r→U):|T v*∏q,x (v q)|≤b*‖x‖^r:=by
    rw [abs_mul,Finset.abs_prod]
    apply mul_le_mul (paid _) _ (Finset.prod_nonneg fun i _=>abs_nonneg _) ((abs_nonneg _).trans (paid v))
    exact (Finset.prod_le_prod (fun i _=>abs_nonneg _) (fun i _=>norm_le_pi_norm x (v i))).trans_eq (by simp)
  calc
    _≤∑ _v:Fin r→U,b*‖x‖^r:=Finset.sum_le_sum (fun i _=>one i)
    _=_:=by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_pi_const,
      nsmul_eq_mul,Nat.cast_pow,mul_pow];ring

theorem wrapped {G:Gauge}{r:ℕ}{T:post G r}{s b:ℝ}(hs:0<s)(paid:Amber terrain s b T)(n:Side)
    (v:stars G r n):|lagoon T n v|≤b*hinges s r:=by
  have bill:=lagoon_cost paid hs n
  rw [←Real.norm_eq_abs]
  apply (bill.2 v).trans
  exact mul_le_of_le_one_right bill.1 (Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (half_pos (hinge_paid hs r)).le) (Nat.cast_nonneg _)))

variable {G:Gauge}(R:Run G)(simple:G.Simple)(v:ℕ→Gear G→ℝ)
include simple in
theorem entries (paid:FundedMarkedCoverRows.prices v R.kit)(e h:ℕ):
    ∀ᶠ j:ℕ in atTop,∃B:ℝ,0≤B ∧∀N≥j,∀t≤e+2,∀l≤h,∀n:Side,∀x,
      |lagoon (actionW R.family.path.levels R.metals.O N j t (l+1)) n x|≤B:=by
  filter_upwards [WilsonOriginalCompoundVertex.original R simple v paid (e+2)] with j enroll
  obtain ⟨Q,levels,ratio,anchored,stock⟩:=enroll
  have home:Q.anchor≤j:=anchored.le
  let s:=(Q.mint j home).σ
  let z:=Borough.ageZ (R.family.path.levels.clock.hatBeta j)
  obtain ⟨warm,_,all⟩:=stock j home
  let I:=Fin (e+3)×Fin (h+1)
  let a (i:I):ℝ:=((tariff G (e+2) i.1.val (i.2.val+1) 0 (by omega)).buy z)*hinges s i.2.val
  have one(i:I)(N:ℕ)(hn:j≤N)(n:Side)(x):
      |lagoon (actionW R.family.path.levels R.metals.O N j i.1.val (i.2.val+1)) n x|≤a i:=
    wrapped warm ((all i.1.val (by omega) (i.2.val+1) 0 N N hn (le_refl _)).1.pose) n x
  have positive(i:I):0≤a i:=mul_nonneg ((all i.1.val (by have:=i.1.isLt; omega) (i.2.val+1) 0 j j (le_refl _) (le_refl _)).1.nn) (hinge_reserve warm _).le
  refine ⟨∑i:I,a i,Finset.sum_nonneg (fun i _=>positive i),?_⟩
  intro N hn t ht l hl n x
  let i:I:=(⟨t,by omega⟩,⟨l,by omega⟩)
  exact (one i N hn n x).trans (Finset.single_le_sum (fun i _=>positive i) (mem_univ i))

end YM.Integration.WilsonOriginalGaussianAngularWallet
end
