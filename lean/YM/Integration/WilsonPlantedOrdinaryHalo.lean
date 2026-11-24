import YM.Integration.WilsonPlantedOrdinaryPrice
import YM.Integration.WilsonCenteredOccupiedFare

/-! The entire signed ordinary roster on a three-seat reporting halo costs a
fixed inverse coupling power before the aperture of its declared face. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPlantedOrdinaryHalo
open Function Finset RG Lattice Wilson Marker Multi QuadraticLocal Ac Push.Local Source Labels
open Planned.GuardedAtom Extra.Trajectories WilsonCenteredFiledAtoms
open WilsonCapturedPrimarySoftPartition WilsonCapturedPrimarySoftMount
open WilsonCenteredLampCapture WilsonCapturedPrimarySoftLoad
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} {d : ℕ} {F : Frame G d}
local notation "J" => Stock.census (Fin 3)

def master (S : SectionData F) (Y : Hol G) (α K : ℝ) :=
  (Fintype.card (parts (J)).Mode:ℝ)*
     ((2*(Real.exp ((α+2)*atomTiles S)*(1+5*|readPrice Y F|))+1)*17*Real.exp ((α+2)*81)*K^3)

theorem original (p : BudgetPoint) (S : SectionData F) (Y : Hol G) (Z : Support n) (y : Site n)
    (w : Fin 3→ℝ) (s : (J).Mode) (rad : ℕ) {μ α κ η C D x K : ℝ}
    (hx : 1≤x) (near : rad≤p.B) (housed : Z⊆halo p.B {y}) (support : p.supportExponent≤α)
    (live : 0<κ) (hv : 0≤η) (divided : hitWidth p*η/κ≤1)
    (motion : WilsonReportRetainedAnchor.reprice p p.B≤2*x^2) (μpos : 0≤μ) (read : μ≤4*x^2) (one : 1≤K)
    (each : ∀h∈shards (J) s, Poly.toll w s*(cost p Z w C rad h+tariff p Z w D h) ≤
       (stage p rad (univ : Finset (Fin h.val.card))+1)*Real.exp ((p.supportExponent+2)*coverNumber p.B Z)*
        (K*x^17)^h.val.card) :
    Poly.toll w s*WilsonPlantedOrdinary.fare p Z w C D rad S Y μ η κ s ≤ master S Y α K*x^61 := by
  let A:=Real.exp ((α+2)*atomTiles S)*(1+5*|readPrice Y F|)
  let H:=hitWidth p*η/κ
  let B:=factor Y S p.supportExponent μ
  let Z₀:=Real.exp ((α+2)*81)
  let M:=(2*A+1)*17*Z₀*K^3
  have H0 : 0 ≤ H:=div_nonneg (mul_nonneg (by unfold hitWidth;positivity) hv) live.le
  have x0:=zero_le_one.trans hx
  have x2 : 1≤x^2:=one_le_pow₀ hx
  have x8 : 1≤x^8:=one_le_pow₀ hx
  have A0 : 0≤A:=by dsimp only [A];positivity
  have Z0 : 0≤Z₀:=Real.exp_nonneg _
  have kk:=zero_le_one.trans one
  have pos : 0≤M:=by dsimp only [M];positivity
  have weight : B≤A*x^2 :=by
    have scaled : (1+μ)*readPrice Y F≤(5*x^2)*|readPrice Y F| :=
      (mul_le_mul_of_nonneg_left (le_abs_self _) (by linarith only [μpos])).trans
        (mul_le_mul_of_nonneg_right (by linarith only [read,x2]) (abs_nonneg _))
    have sold : atomPrice Y F μ≤(1+5*|readPrice Y F|)*x^2:=by unfold atomPrice;nlinarith only [scaled,x2]
    have growth : Real.exp ((p.supportExponent+2)*atomTiles S) ≤ Real.exp ((α+2)*atomTiles S):=by
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith only [support]) (Nat.cast_nonneg _))
    exact ((mul_le_mul_of_nonneg_left sold (Real.exp_nonneg _)).trans
      (mul_le_mul_of_nonneg_right growth (by positivity))).trans_eq (mul_assoc ..).symm
  have B0 : 0≤B:=by unfold B factor atomPrice;have pr:=zero_le_one.trans (readPrice_pos Y F);positivity
  have hc : B+H+H*B ≤ (2*A+1)*x^2:=by
    have:=mul_le_of_le_one_left B0 divided
    linarith only [weight,this,show H≤1 from divided,x2]
  have cash (h : (parts (J)).Mode) (ok : h∈shards (J) s) :
      Poly.toll w s*cartage p Y S μ η κ (cost p Z w C rad h+tariff p Z w D h) 0 ≤ M*x^61 :=by
    have count : h.val.card≤3 := (size ok).trans (by simpa using card_le_univ s.val)
    have moving : stage p rad (univ:Finset (Fin h.val.card))≤16*x^8:=by
      have e:=WilsonCenteredArityMotion.original p near (univ:Finset (Fin h.val.card)) (r:=3) (by simpa using count)
      refine (e.trans (pow_le_pow_left₀ (by unfold WilsonReportRetainedAnchor.reprice;positivity) motion _)).trans_eq ?_
      ring
    have cover:=WilsonCenteredCaptureGeometry.cover p Z y housed support
    have high : (K*x^17)^h.val.card≤(K*x^17)^3:=
      pow_le_pow_right₀ (one_le_mul_of_one_le_of_one_le one (one_le_pow₀ hx)) count
    have cap : Poly.toll w s*(cost p Z w C rad h+tariff p Z w D h)≤17*x^8*Z₀*(K*x^17)^3 :=
      (each h ok).trans (mul_le_mul (mul_le_mul (by linarith only [moving,x8]) cover (Real.exp_nonneg _)
        (by positivity)) high (by positivity) (by positivity))
    calc
      _ = (B+H+H*B)*(Poly.toll w s*(cost p Z w C rad h+tariff p Z w D h)) :=by
        unfold cartage;dsimp only [B,H];ring
      _ ≤ (B+H+H*B)*(17*x^8*Z₀*(K*x^17)^3) :=mul_le_mul_of_nonneg_left cap (by positivity)
      _ ≤ ((2*A+1)*x^2)*(17*x^8*Z₀*(K*x^17)^3) :=mul_le_mul_of_nonneg_right hc (by positivity)
      _ = M*x^61:=by dsimp only [M];ring
  unfold WilsonPlantedOrdinary.fare
  rw [Finset.mul_sum]
  have total : (∑h∈shards (J) s,Poly.toll w s*cartage p Y S μ η κ
      (cost p Z w C rad h+tariff p Z w D h) 0) ≤ ((shards (J) s).card:ℝ)*(M*x^61) := by
    simpa only [sum_const,nsmul_eq_mul] using sum_le_sum cash
  apply total.trans
  have c:(((shards (J) s).card:ℕ):ℝ)≤Fintype.card (parts (J)).Mode:=by exact_mod_cast card_le_univ (shards (J) s)
  exact (mul_le_mul_of_nonneg_right c (by positivity : 0≤M*x^61)).trans_eq (by dsimp only [master,M,Z₀,A];ring)

end YM.Integration.WilsonPlantedOrdinaryHalo
