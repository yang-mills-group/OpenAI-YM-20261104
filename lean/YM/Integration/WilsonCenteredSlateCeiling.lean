import YM.Integration.WilsonCenteredFareCeiling

/-! The dimensionless expense of the whole finite counterterm is YM.Integration.WilsonCenteredFareCeiling.linear in
its charged coordinates, with a fixed power for the elected source loads. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCenteredSlateCeiling
open Finset Function Lattice RG Wilson Marker QuadraticLocal Ac Source Labels Push.Local
open Planned.GuardedAtom Extra.Trajectories WilsonCenteredFiledAtoms WilsonCenteredLampCapture
open scoped Classical BigOperators
open private YM.Integration.WilsonCenteredFareCeiling.Band YM.Integration.WilsonCenteredFareCeiling.linear
  YM.Integration.WilsonCenteredFareCeiling.multiply YM.Integration.WilsonCenteredFareCeiling.raise
  YM.Integration.WilsonCenteredFareCeiling.light YM.Integration.WilsonCenteredFareCeiling.divided
  from YM.Integration.WilsonCenteredFareCeiling
open WilsonCenteredFareCeiling
variable {G : Gauge} {n : Side} {V : Type} [DecidableEq V] {R : Census V}
  {d : ℕ} {F : Frame G d}

theorem coordinate (p : BudgetPoint) (S : SectionData F) (Y : Hol G) (w : V→ℝ) (s : R.Mode)
    (z : ℂ) (Z : Support n) (rad : ℕ) (E κ η μ : ℝ) :
    WilsonCenteredSingletonFiled.fare p S Y w s z Z rad E κ η μ=
      ‖z‖*WilsonCenteredSingletonFiled.fare p S Y w s 1 Z rad E κ η μ := by
  unfold WilsonCenteredSingletonFiled.fare cartage
  dsimp only
  rw [norm_one]
  ring

theorem singleton (p : BudgetPoint) (S : SectionData F) (Y : Hol G) (w : V→ℝ) (s : R.Mode)
    (z : ℂ) (Z : Support n) (rad : ℕ) {E κ η μ M : ℝ} (hw : ∀ j,0<w j)
    (hm : 1≤M) (fee : factor Y S p.supportExponent μ≤M) (paid : 0≤E) (upper : E≤M)
    (hk : 0<κ) (hv : 0≤η) (room : hitWidth p*η≤1) (reclaim : hitWidth p*η/κ≤1)
    (single : stage p rad ({()}:Finset Unit)≤M)
    (cover : Real.exp ((p.supportExponent+2)*coverNumber p.B Z)≤M)
    (wage : (Poly.toll w s)⁻¹≤M) :
    WilsonCenteredSingletonFiled.fare p S Y w s z Z rad E κ η μ≤‖z‖*(5*M^7) := by
  rw [coordinate]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg z)
  have m : 0≤M:=zero_le_one.trans hm
  have zB:=YM.Integration.WilsonCenteredFareCeiling.linear (Real.exp_nonneg _) cover
  have tB:=YM.Integration.WilsonCenteredFareCeiling.linear (zero_le_one.trans (funded p rad ({()}:Finset Unit))) single
  have cash:=YM.Integration.WilsonCenteredFareCeiling.linear (inv_nonneg.mpr (prod_nonneg (fun i _=>(hw i).le))) wage
  have cost:=YM.Integration.WilsonCenteredFareCeiling.multiply m tB (YM.Integration.WilsonCenteredFareCeiling.multiply m zB (YM.Integration.WilsonCenteredFareCeiling.multiply m cash (YM.Integration.WilsonCenteredFareCeiling.linear paid upper)))
  have recov : 0≤hitWidth p*η/κ := div_nonneg (mul_nonneg (by unfold hitWidth;positivity) hv) hk.le
  have dark : WilsonCenteredHardMount.bill p Z η ((Poly.toll w s)⁻¹*κ)/κ ≤ 2*M^7 :=
    YM.Integration.WilsonCenteredFareCeiling.divided hm hk.ne' room (YM.Integration.WilsonCenteredFareCeiling.raise hm (YM.Integration.WilsonCenteredFareCeiling.multiply m zB cash) (by decide))
  unfold WilsonCenteredSingletonFiled.fare
  rw [norm_one,one_mul,one_mul]
  exact (YM.Integration.WilsonCenteredFareCeiling.light p S Y hm fee (YM.Integration.WilsonCenteredFareCeiling.raise hm cost (by decide)) recov reclaim).trans (by linarith only [dark])

theorem original (p : BudgetPoint) (S : SectionData F) (Y : Hol G) (w : V→ℝ) (a b : V)
    (s : R.Mode) (counter : Finset V) (c : V→ℂ) (Z : Support n) (rad : ℕ) {E κ η μ M : ℝ}
    (hw : ∀ j,0<w j) (hm : 1≤M) (fee : factor Y S p.supportExponent μ≤M) (paid : 0≤E) (upper : E≤M)
    (hk : 0<κ) (hk1 : κ≤1) (hv : 0≤η) (room : hitWidth p*η≤1) (reclaim : hitWidth p*η/κ≤1)
    (single : stage p rad ({()}:Finset Unit)≤M) (two : stage p rad ({false,true}:Finset Bool)≤M)
    (cover : Real.exp ((p.supportExponent+2)*coverNumber p.B Z)≤M)
    (wa : (w a)⁻¹≤M) (wb : (w b)⁻¹≤M) (pair : (Poly.toll w s)⁻¹≤M)
    (first : (Poly.toll w (R.fire a))⁻¹≤M) (rest : ∀u∈counter,(Poly.toll w (R.fire u))⁻¹≤M) :
    WilsonCenteredCountertermSlate.fare p S Y w a b s counter c Z rad E κ η μ ≤ (24+5*∑u∈counter,‖c u‖)*M^7 := by
  have ab:=WilsonCenteredFareCeiling.original p S Y w a b a s Z rad hw hm fee paid upper hk hk1 hv room reclaim
    single two cover wa wb pair first
  have restore:=singleton p S Y w (R.fire a) 1 Z rad hw hm fee paid upper hk hv room reclaim single cover first
  simp only [norm_one,one_mul] at restore
  have all := sum_le_sum (s:=counter) (fun u hu=>singleton p S Y w (R.fire u) (c u) Z rad hw hm fee paid upper hk hv room
    reclaim single cover (rest u hu))
  rw [←sum_mul] at all
  unfold WilsonCenteredCountertermSlate.fare
  calc
    _ ≤ 19*M^7+5*M^7+(∑u∈counter,‖c u‖)*(5*M^7) := add_le_add (add_le_add ab restore) all
    _ = _ := by ring

end YM.Integration.WilsonCenteredSlateCeiling
