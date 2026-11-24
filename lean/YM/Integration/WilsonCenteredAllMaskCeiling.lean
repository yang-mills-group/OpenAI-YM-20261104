import YM.Integration.WilsonCenteredGalleryCapture
import YM.Integration.WilsonCenteredArityMotion
import YM.Integration.WilsonCapturedPrimarySoftFare
import YM.Integration.WilsonCenteredSlateCeiling

/-! A single physical source wallet pays every occupied and disconnected face
of a fixed capture load. The exponent is fixed before the comparison order. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCenteredAllMaskCeiling
open Finset RG Wilson Lattice Marker Source Labels Extra.Histories Push.Local
open WilsonCapturedPrimarySoftPartition WilsonCapturedPrimarySoftLoad
open scoped BigOperators Classical
variable {G : Gauge} {n : Side} {V : Type} [DecidableEq V] {R : Census V} {d : ℕ} {F : Frame G d}

def scale (r : ℕ) : ℝ := ((2:ℝ)^r)*((2^(2^r):ℕ):ℝ)*(3+2*(r:ℝ)*Real.exp r)+5

theorem original (p : BudgetPoint) (S : SectionData F) (Y : Hol G) (w : V→ℝ) (hw : ∀j,0<w j)
    (s : R.Mode) (names : Finset V) (c : V→ℂ) (Z : Support n) (rad r : ℕ) (load : s.val.card ≤ r)
    (near : rad≤p.B) {E κ v μ M : ℝ} (hm : 1≤M) (cash : factor Y S p.supportExponent μ≤M)
    (income : 0≤E) (upper : E≤M) (div : 0<κ) (small : κ≤1) (hv : 0≤v)
    (room : hitWidth p*v≤1) (reclaimed : hitWidth p*v/κ≤1)
    (motion : WilsonReportRetainedAnchor.reprice p p.B≤M)
    (housed : Real.exp ((p.supportExponent+2)*coverNumber p.B Z)≤M)
    (widths : ∀t:R.Mode,t.val⊆s.val→(Poly.toll w t)⁻¹≤M)
    (named : ∀j∈names,(Poly.toll w (R.fire j))⁻¹≤M) :
    WilsonCenteredGalleryCapture.fare p S Y w s names c Z rad E κ v μ ≤
      (1+∑j∈names,‖c j‖)*scale r*M^(3*r+9) :=by
  let A:ℝ:=((2^(2^r):ℕ):ℝ)
  let B:=A*M^(2*r+1)
  let roof:=M^(3*r+9)
  have m0:=zero_le_one.trans hm
  have a0 : 0≤A :=Nat.cast_nonneg _
  have b0 : 0≤B :=mul_nonneg a0 (pow_nonneg m0 _)
  have all (j : ℕ) (h : j≤3*r+9) : M^j≤roof :=pow_le_pow_right₀ hm h
  have basic : principal p Z M E r ≤ M^(2*r+1) :=by
    have cheap : max 1 (M*E)≤M^2 :=max_le (one_le_pow₀ hm) (by simpa only [pow_two] using mul_le_mul_of_nonneg_left upper m0)
    calc
      _ ≤ M*(M^2)^r :=mul_le_mul housed (pow_le_pow_left₀ (zero_le_one.trans (le_max_left _ _)) cheap _) (by positivity) m0
      _ = _ :=by rw [←pow_mul,pow_succ,mul_comm]
  have quoted (t : R.Mode) (fit : t.val⊆s.val) : 0≤WilsonCapturedPrimarySoftInventory.fare p Z w E t ∧
      WilsonCapturedPrimarySoftInventory.fare p Z w E t≤B :=by
    constructor
    · exact sum_nonneg (fun q _=>mul_nonneg (Real.exp_pos _).le (prod_nonneg (fun j _=>mul_nonneg (inv_pos.mpr (Poly.worth hw _)).le income)))
    exact (WilsonCapturedPrimarySoftLoad.fee p Z t w hw income ((card_le_card fit).trans load)
      (fun u hu=>widths u (hu.trans fit))).trans (mul_le_mul_of_nonneg_left basic a0)
  let H:=hitWidth p*v/κ
  have h0 : 0≤H:=div_nonneg (mul_nonneg (by unfold hitWidth; positivity) hv) div.le
  have factorCost : WilsonCapturedPrimarySoftFare.factorFee p S Y μ v κ≤3*M :=by
    apply max_le (by positivity)
    have comb := (mul_le_mul_of_nonneg_left cash h0).trans (mul_le_of_le_one_left m0 reclaimed)
    change factor Y S p.supportExponent μ+H+H*factor Y S p.supportExponent μ≤_
    linarith only [cash,show H≤1 from reclaimed,comb,hm]
  have stretch : WilsonCapturedPrimarySoftFare.motion p rad r ≤ M^(r+1) :=by
    have moving:=WilsonCenteredArityMotion.original p near (univ : Finset (Fin r)) (r:=r) (by simp)
    simpa only [WilsonCapturedPrimarySoftFare.motion,WilsonCenteredLampCapture.stage,card_univ,Fintype.card_fin] using
      moving.trans (pow_le_pow_left₀ (by unfold WilsonReportRetainedAnchor.reprice; positivity) motion _)
  have pure : WilsonCapturedPrimarySoftMount.fare p Z w E rad S Y μ v κ s ≤ 3*A*M^(3*r+3) :=by
    have cap:=WilsonCapturedPrimarySoftFare.original p Z s w hw income load widths rad S Y μ v κ
    apply cap.trans
    calc
      _ ≤ (3*M*M^(r+1))*B := mul_le_mul (mul_le_mul factorCost stretch (by unfold WilsonCapturedPrimarySoftFare.motion; positivity) (by positivity))
        (mul_le_mul_of_nonneg_left basic a0) (by unfold principal; positivity) (by positivity)
      _ = _ := by dsimp [B];ring
  have due:=WilsonCenteredCompleteFare.original p s w hw (WilsonCapturedPrimarySoftInventory.fare p Z w E)
    load div small room (D0:=mul_nonneg (mul_nonneg (by norm_num) a0) (pow_nonneg m0 _))
    b0 m0 pure quoted widths
  have softHigh : 3*A*M^(3*r+3)≤ 3*A*roof :=
    mul_le_mul_of_nonneg_left (all _ (by omega)) (mul_nonneg (by norm_num) a0)
  have hardHigh : 2*(B*M)*r*Real.exp r ≤ (2*A*r*Real.exp r)*roof :=by
    calc
      _ = (2*A*r*Real.exp r)*M^(2*r+2) :=by dsimp [B];ring
      _ ≤ _ :=mul_le_mul_of_nonneg_left (all _ (by omega)) (by positivity)
  have core := due.trans (mul_le_mul_of_nonneg_left (add_le_add softHigh hardHigh) (by positivity))
  have J : WilsonCenteredLampCapture.stage p rad ({()}:Finset Unit)≤M :=
    (WilsonCenteredCaptureGeometry.motion p near _ (by simp)).trans motion
  have slate := sum_le_sum (fun j h=>WilsonCenteredSlateCeiling.singleton p S Y w (R.fire j) (c j) Z rad hw
    hm cash income upper div hv room reclaimed J housed (named j h))
  have sizes : 0≤∑j∈names,‖c j‖ :=sum_nonneg (fun _ _=>norm_nonneg _)
  have remainder : (∑j∈names,‖c j‖)*(5*M^7)≤(∑j∈names,‖c j‖)*(5*roof) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (all 7 (by omega)) (by norm_num)) sizes
  rw [←sum_mul] at slate
  apply (add_le_add core (slate.trans remainder)).trans
  dsimp only [scale,roof,A] at *
  have last : 0≤((2:ℝ)^r)*((2^(2^r):ℕ):ℝ)*(3+2*(r:ℝ)*Real.exp r) :=by positivity
  nlinarith only [mul_nonneg (mul_nonneg sizes last) (pow_nonneg m0 (3*r+9)),pow_nonneg m0 (3*r+9)]

end YM.Integration.WilsonCenteredAllMaskCeiling
