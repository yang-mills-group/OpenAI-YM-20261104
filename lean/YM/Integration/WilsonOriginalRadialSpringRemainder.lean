import YM.Integration.WilsonOriginalRadialLocatedDerivatives
import YM.RG01.Kernel.Read

/-! The Taylor bill of the complete planted field under its genuine last spring. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalRadialSpringRemainder
open Function Finset Filter Set MeasureTheory Labels Lattice Wilson RG Source Next.Foundations Push.Local
open Planned.AtomRegular RG01.Kernel RG01.Kernel.Wheel WardBin.Lies WilsonCapturedPrimaryRough
open WilsonFirstReceivedRadialStencil WilsonCapturedPrimarySamples
open scoped Classical Topology BigOperators ContDiff
variable {G:Gauge} (H:History G){N p i:ℕ}
local notation "n" => H.S.side i p
local notation "Ω" => Config G (H.S.side (i+1) p)
local notation "tags" => (H.levels.clock.op i p).Choices

def total (B:BudgetPoint)(o:Site n)(J:Finset (Link n))(k:ℕ)(M:ℝ):ℝ:=
  ∑j∈range (k+1),|(probePrice (m:=i) H B o J N)^j*compensation G j (invoice j M) 3|

theorem tariff (selected:H.Selected)(live:i<N)(F:tags→Ω→ℂ){M:ℝ}
    (meas:Bounded (prior G _) F M)(gross:0≤M)
    (B:BudgetPoint)(o:Site n)(J:Finset (Link n))(w:Directions G n)(k:ℕ)
    (small:∀e∈J,‖limitAmp B o J w e‖≤1)(paid:∀e∈J,weight B o e≤1):
    let f:=fun V=>conditional H N i p V F
    ContDiffAt ℝ k (f ∘ bone B o J) w ∧
    ∀j≤k,‖iteratedFDeriv ℝ j (f ∘ bone B o J) w‖≤baseCost G k*total H (N:=N) B o J k M := by
  intro f
  let V:=bone B o J w
  have positive:0≤total H (N:=N) B o J k M:=by unfold total;exact sum_nonneg fun _ _=>abs_nonneg _
  have sf:=RG01.Kernel.angular H selected V live meas gross (List.replicate k (0:Directions G n)) (fun _=>0)
    (fun _=>le_rfl) (fun a ha e=>by rw [(List.mem_replicate.mp ha).2];simp)
  apply WilsonOriginalRadialLocatedDerivatives.chart f B o J w positive (by simpa only [List.length_replicate] using sf.1) _ small paid
  intro l len fits
  have priced:=(RG01.Kernel.located H selected V live meas gross B o J l fits).2
  refine (priced.trans (le_abs_self _)).trans ?_
  norm_num only [show (1+2*1:ℝ)=3 by norm_num]
  exact single_le_sum (f:=fun j=>|(probePrice (m:=i) H B o J N)^j*compensation G j (invoice j M) 3|)
    (fun _ _=>abs_nonneg _) (mem_range.mpr (Nat.lt_succ_of_le len))

variable {d:ℕ}
def curve (A:Hol G)(B:BudgetPoint)(o:Site n)(r:ℕ)(a:Probe G d)(F:tags→Ω→ℂ):ℝ→ℂ:=
  (fun V=>conditional H N i p V F) ∘ WilsonCapturedPrimaryRays.field A B o r a

def bill (A:Hol G)(B:BudgetPoint)(o:Site n)(r:ℕ)(a:Probe G d)(k:ℕ)(M:ℝ):ℝ:=
  WilsonCapturedPrimaryRough.price G k (WilsonCapturedPrimaryAngles.wallet A a r) *
    total H (N:=N) (quadratic B) o (WilsonCapturedPrimaryAngles.active o r) k M

theorem derivative (selected:H.Selected)(live:i<N)(F:tags→Ω→ℂ){M:ℝ}
    (meas:Bounded (prior G _) F M)(gross:0≤M)
    (A:Hol G)(B:BudgetPoint)(o:Site n)(r:ℕ)(a:Probe G d){t:ℝ}
    (ss:|t|≤1)(sm:|t| *WilsonCapturedPrimaryAngles.wallet A a r≤1)(paid:B.threshold*(1+(r:ℝ))^2≤1)
    (k:ℕ)(kd:k≤d+1):
    ContDiffAt ℝ k (curve H (N:=N) A B o r a F) t ∧
    ‖iteratedDeriv k (curve H (N:=N) A B o r a F) t‖≤bill H (N:=N) A B o r a k M:=by
  let J:=WilsonCapturedPrimaryAngles.active o r
  let u:=WilsonCapturedPrimaryAngles.angular A B o r a
  let T:=total H (N:=N) (quadratic B) o J k M
  have pc:0≤T:=by unfold T total;exact sum_nonneg fun _ _=>abs_nonneg _
  have one:=WilsonCapturedPrimaryAngles.wallet_one A a r
  have ud:ContDiffAt ℝ k u t:=by unfold u WilsonCapturedPrimaryAngles.angular;fun_prop
  have udj j (jp:0<j) (jk:j≤k):‖iteratedFDeriv ℝ j u t‖≤WilsonCapturedPrimaryAngles.wallet A a r:=
    WilsonCapturedPrimaryAngles.derivatives A B o r a ss j (jk.trans kd)
  have wu:‖u t‖≤1:=by
    exact (WilsonCapturedPrimaryAngles.size A B o r a ss).trans (by simpa only [mul_comm] using sm)
  have weights e (he:e∈J):weight (quadratic B) o e≤1:=by
    have dist:separation e.1 o≤r:=(mem_filter.mp he).2
    change B.threshold*(1+(separation e.1 o:ℝ))^2≤1
    apply le_trans _ paid
    gcongr
    exact B.threshold_pos.le
  have input e (he:e∈J):‖limitAmp (quadratic B) o J (u t) e‖≤1:=by
    rw [limit_hit he,norm_smul,Real.norm_of_nonneg (weight_pos ..).le]
    have point:=((pi_norm_le_iff_of_nonneg (show (0:ℝ)≤1 by norm_num)).mp wu) e
    nlinarith only [mul_le_mul (weights e he) point (norm_nonneg _) (show (0:ℝ)≤1 by norm_num)]
  have budget:=tariff H selected live F meas gross (quadratic B) o J (u t) k input weights
  have eqn:curve H (N:=N) A B o r a F = ((fun V=>conditional H N i p V F) ∘ bone (quadratic B) o J) ∘ u:=by
    ext s
    exact congrArg (fun V=>conditional H N i p V F) (WilsonCapturedPrimaryAngles.physical A B o r a s)
  rw [eqn,←norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  refine ⟨budget.1.comp t ud,(nest_bound ud budget.1 (le_refl _) (mul_nonneg (baseCost_nonneg ..) pc) one udj budget.2).trans_eq ?_⟩
  unfold bill WilsonCapturedPrimaryRough.price T J
  ring

end YM.Integration.WilsonOriginalRadialSpringRemainder
