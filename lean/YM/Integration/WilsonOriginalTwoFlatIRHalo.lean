import YM.Integration.WilsonPlantedOrdinaryHalo

/-! Height-zero filing on one captured halo. Every nonempty block of a
partition uses its own derivative and whole-word income. The scalar and
all ordinary products are retained at any fixed finite arity. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatIRHalo
open Function Finset RG Lattice Wilson Marker Multi QuadraticLocal Ac Push.Local Source Labels
open Planned.GuardedAtom Extra.Trajectories WilsonCenteredFiledAtoms
open WilsonCapturedPrimarySoftPartition WilsonCapturedPrimarySoftMount
open WilsonCenteredLampCapture WilsonCapturedPrimarySoftLoad
open scoped Classical BigOperators
variable {G:Gauge} {n:Side} {d:ℕ} {F:Frame G d}
variable {V:Type}[DecidableEq V]{J:Census V}

def factor₀ (S:SectionData F)(Y:Hol G)(α:ℝ) :=
  2*(Real.exp ((α+2)*atomTiles S)*(1+5*|readPrice Y F|))+1

def roof (J:Census V)(s:J.Mode)(S:SectionData F)(Y:Hol G)(α K:ℝ) :=
  (Fintype.card (parts J).Mode:ℝ)*factor₀ S Y α*
    ((2:ℝ)^(s.val.card+1)+1)*Real.exp ((α+2)*81)*K^s.val.card

def power (seats pole:ℕ):ℕ := 2+2*(seats+1)+pole*seats

theorem original (p:BudgetPoint)(S:SectionData F)(Y:Hol G)(Z:Support n)(y:Site n)
    (w:V→ℝ)(wp:∀v,0<w v)(s:J.Mode)(rad pole:ℕ){μ α κ η C D x K:ℝ}
    (hx:1≤x)(near:rad≤p.B)(housed:Z⊆halo p.B {y})(support:p.supportExponent≤α)
    (live:0<κ)(hv:0≤η)(divided:hitWidth p*η/κ≤1)
    (motion:WilsonReportRetainedAnchor.reprice p p.B≤2*x^2)(μpos:0≤μ)(read:μ≤4*x^2)
    (one:1≤K)(cp:0≤C)(dp:0≤D)(dc:C≤K*x^pole)(dg:D≤K*x^pole):
    Poly.toll w s*WilsonPlantedOrdinary.fare p Z w C D rad S Y μ η κ s ≤
      roof J s S Y α K*x^(power s.val.card pole):=by
  let N:=s.val.card
  let A:=Real.exp ((α+2)*atomTiles S)*(1+5*|readPrice Y F|)
  let H:=hitWidth p*η/κ
  let B:=factor Y S p.supportExponent μ
  let E:=Real.exp ((α+2)*81)
  let M:=((2*A+1)*x^2)*((((2:ℝ)^(N+1)+1)*x^(2*(N+1)))*E*(K*x^pole)^N)
  have x0:=zero_le_one.trans hx
  have x2:1≤x^2:=one_le_pow₀ hx
  have A0:0≤A:=by dsimp only [A];positivity
  have B0:0≤B:=by unfold B factor atomPrice;have pr:=zero_le_one.trans (readPrice_pos Y F);positivity
  have H0:0≤H:=div_nonneg (mul_nonneg (by unfold hitWidth;positivity) hv) live.le
  have load:B≤A*x^2:=by
    have scaled:(1+μ)*readPrice Y F≤(5*x^2)*|readPrice Y F| :=
      (mul_le_mul_of_nonneg_left (le_abs_self _) (by linarith)).trans
        (mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _))
    have atom:atomPrice Y F μ≤(1+5*|readPrice Y F|)*x^2:=by unfold atomPrice;nlinarith only [scaled,x2]
    have tiles:=Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (show p.supportExponent+2≤α+2 by linarith) (Nat.cast_nonneg (atomTiles S):0≤(atomTiles S:ℝ)))
    exact ((mul_le_mul_of_nonneg_left atom (Real.exp_nonneg _)).trans
      (mul_le_mul_of_nonneg_right tiles (by positivity))).trans_eq (mul_assoc ..).symm
  have cash:B+H+H*B≤(2*A+1)*x^2:=by
    have zero:=mul_le_of_le_one_left B0 divided
    linarith only [zero,load,show H≤1 from divided,x2]
  have master:0≤M:=by dsimp only [M,E];positivity
  have item (h:(parts J).Mode)(ha:h∈shards J s):
      Poly.toll w s*cartage p Y S μ η κ (cost p Z w C rad h+tariff p Z w D h) 0 ≤ M:=by
    have count:h.val.card≤N:=WilsonCapturedPrimarySoftLoad.size ha
    have mov:=WilsonCenteredArityMotion.original p near (univ:Finset (Fin h.val.card)) (r:=N) (by simpa using count)
    have amp:1≤x^(2*(N+1)):=one_le_pow₀ hx
    have size:stage p rad (univ:Finset (Fin h.val.card))+1≤((2:ℝ)^(N+1)+1)*x^(2*(N+1)):=by
      have ins:=mov.trans (pow_le_pow_left₀ (by unfold WilsonReportRetainedAnchor.reprice;positivity) motion _)
      rw [mul_pow,←pow_mul] at ins
      linarith only [ins,amp]
    have plate:=WilsonCenteredCaptureGeometry.cover p Z y housed support
    have kk:1≤K*x^pole:=one_le_mul_of_one_le_of_one_le one (one_le_pow₀ hx)
    have placed:=WilsonPlantedOrdinaryPrice.partition p Z rad w wp s h ha cp dp dc dg
    have sub:=placed.trans (mul_le_mul (mul_le_mul size plate (Real.exp_nonneg _) (by positivity))
      (pow_le_pow_right₀ kk count) (pow_nonneg (zero_le_one.trans kk) _) (by positivity))
    calc _ = (B+H+H*B)*(Poly.toll w s*(cost p Z w C rad h+tariff p Z w D h)):=by unfold cartage;dsimp only [B,H];ring
         _ ≤ M:=(mul_le_mul_of_nonneg_left sub (by positivity)).trans (mul_le_mul_of_nonneg_right cash (by positivity))
  unfold WilsonPlantedOrdinary.fare
  rw [Finset.mul_sum]
  have sums:(∑h∈shards J s,Poly.toll w s*cartage p Y S μ η κ (cost p Z w C rad h+tariff p Z w D h) 0)≤((shards J s).card:ℝ)*M:=by
    simpa only [sum_const,nsmul_eq_mul] using sum_le_sum item
  have count:((shards J s).card:ℝ)≤Fintype.card (parts J).Mode:=by exact_mod_cast card_le_univ (shards J s)
  apply sums.trans ((mul_le_mul_of_nonneg_right count master).trans_eq ?_)
  dsimp only [roof,power,factor₀,M,A,E,N]
  rw [mul_pow,←pow_mul,pow_add,pow_add]
  ring

end YM.Integration.WilsonOriginalTwoFlatIRHalo
