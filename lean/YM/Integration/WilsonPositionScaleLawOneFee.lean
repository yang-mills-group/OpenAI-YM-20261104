import YM.Integration.WilsonPositionScaleLawTrajectory

/-! Highest-grade propagation needs only the order-one signed position
measurements at a single dyadic ratio and only to quadratic bounded accuracy.
The true diagonal one-loop coefficient vanishes before reading those data. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawOneFee
open Function Filter Set Asymptotics Spec Table Extraction OPE OPE.Orbits Climb PhysMS Trace.Pilot
open Maxwell Maxwell.Free XSpace XSpace.Normalize PhysicalNext.Repeat.Legato MS MS.Land MS.Fleet MS.Book.Program FVA2 FVA2.Register FVA2.Scale FVA2.Arrival
open WilsonPositionScaleLawHome (sweep)
open WilsonPositionScaleLawNative (exactOp)
open WilsonPositionScaleLawGrade (cut coeffOp half)
open WilsonPositionScaleLawIndependent (trial letter)
open WilsonPositionScaleLawKinetic (kinetic)
open WilsonPositionScaleLawQinter (measured prediction)
open WilsonPositionScaleLawClock (radius)
open WilsonPhysicalPositionBornCandidates (expansion)
open scoped Topology Classical Asymptotics
variable {G:Gauge}(Z:WilsonPrescription G){hG:G.Simple}(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ:Prescription (Press.portDeck G)}{b:Bool}(H:Main.Match Z hG M σ b)(ν:ℝ)
    {R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)(J:ℝ→tower S)
set_option quotPrecheck false
local notation "E"=>(Bel R.family.book).Field

include H in
theorem exactFirst {d:ℕ}(i:Fin (d+1))(s g:ℝ):
    cut R.family i (WilsonPhysicalPositionBornCandidates.operator R.family (trial Z M ν d 1 s g)-ContinuousLinearMap.id ℂ (E d))=0:=by
  have basis:trial Z M ν d 1 s g=g • guide G d (letter Z M ν d 0 s):=by simp [trial]
  rw [expansion,basis,add_sub_cancel_left,map_smul,map_smul]
  change g • cut R.family i (coeffOp R.family Z M ν 0 s)=0
  rw [WilsonPositionScaleLawGrade.first R.family Z M H ν]
  ext1 v;change g • (0:E d)=0;rw [smul_zero]


def Earned (d:ℕ)(r:ℝ):Prop:=∃B:ℝ,0≤B ∧ ∀ᶠn:ℕ in atTop,
    ‖measured Z M ν F J d 1 (radius r n,half)‖≤B*kinetic Z F J (radius r n)^2

variable (lead:Leading F J){Y:(Bel R.family.book).Hierarchy}(paid:∀d,∀ᶠr in trail,Frame.obedient F Y (J r) d)
    {d:ℕ}(i:Fin (d+1))(raw:WilsonPositionScaleLawBranch.Raw J d)(r:ℝ)(hr:0<r)
    (earned:Earned Z M ν F J d r)

include H lead paid raw hr earned in
theorem quadratic:∃K:ℝ,0≤K ∧ ∀ᶠn:ℕ in atTop,‖cut R.family i (exactOp F J Z.store d (radius r n,half)-
    ContinuousLinearMap.id ℂ (E d))‖≤K*kinetic Z F J (radius r n)^2:=by
  let X:=E d
  letI : NormedAddCommGroup (X→L[ℂ]X):=ContinuousLinearMap.toNormedAddCommGroup
  letI : NormedSpace ℂ (X→L[ℂ]X):=ContinuousLinearMap.toNormedSpace
  letI : NormedSpace ℝ (X→L[ℂ]X):=NormedSpace.restrictScalars ℝ ℂ _
  letI : FiniteDimensional ℝ (X→L[ℂ]X):=Module.Finite.trans ℂ (X→L[ℂ]X)
  let P:(X→L[ℂ]X)→L[ℝ](X→L[ℂ]X):=(cut R.family i).toContinuousLinearMap
  let I:=ContinuousLinearMap.id ℂ X
  obtain ⟨B,hB,fee⟩:=earned
  obtain ⟨L,A,hL,hA,compare⟩:=WilsonPositionScaleLawQinter.original Z M H ν F J lead paid d 1 raw
  have pin:Tendsto (fun n:ℕ=>(radius r n,half)) atTop sweep:=(WilsonPositionScaleLawClock.falls r hr).prodMk tendsto_top
  refine ⟨‖P‖*(L*B+A),mul_nonneg (norm_nonneg _) (add_nonneg (mul_nonneg hL hB) hA),?_⟩
  filter_upwards [fee,pin.eventually compare] with n localFee bound
  let g:=kinetic Z F J (radius r n)
  let U:=exactOp F J Z.store d (radius r n,half)
  let V:=prediction Z M ν F J d 1 (radius r n,half)
  let m:=measured Z M ν F J d 1 (radius r n,half)
  have nearly:‖U-V‖≤(L*B+A)*g^2:=by
    change ‖U-V‖≤L*‖m‖+A*|g|^2 at bound
    rw [sq_abs] at bound
    calc
      _≤L*‖m‖+A*g^2:=bound
      _≤L*(B*g^2)+A*g^2:=add_le_add (mul_le_mul_of_nonneg_left localFee hL) le_rfl
      _=(L*B+A)*g^2:=by ring
  have diagonal:P (V-I)=0:=exactFirst Z M H ν i _ g
  have sum:U-I=(U-V)+(V-I):=by abel
  change ‖P (U-I)‖≤(‖P‖*(L*B+A))*g^2
  rw [sum,P.map_add,diagonal,add_zero,mul_assoc]
  exact (P.le_opNorm _).trans (mul_le_mul_of_nonneg_left nearly (norm_nonneg _))

include H lead paid raw hr earned in
theorem cost (funded:Coupling G (kinetic Z F J)):∃K:ℝ,0≤K ∧ ∀ᶠn:ℕ in atTop,
    ‖WilsonPositionScaleLawDyadic.step Z F J i r n-ContinuousLinearMap.id ℂ (E d)‖≤K/((n:ℝ)+1):=by
  obtain ⟨A,hA,fee⟩:=quadratic Z M H ν F J lead paid i raw r hr earned
  let c:ℝ:=(2*Trace.Over.b0 G*Real.log 2)⁻¹
  let cap:=|c|+1
  have bigger:c<cap:=lt_of_le_of_lt (le_abs_self c) (lt_add_one _)
  have bound:∀ᶠn:ℕ in atTop,((n:ℝ)+1)*kinetic Z F J (radius r n)^2<cap:=
    (tendsto_order.mp (WilsonPositionScaleLawClock.rate funded r hr)).2 _ bigger
  refine ⟨A*cap,mul_nonneg hA (by dsimp [cap];positivity),?_⟩
  filter_upwards [fee,bound] with n hn hm
  rw [WilsonPositionScaleLawDyadic.step,add_sub_cancel_left]
  have uq:kinetic Z F J (radius r n)^2≤cap/((n:ℝ)+1):=(le_div_iff₀ (by positivity)).mpr ((mul_comm _ _).trans_le hm.le)
  exact hn.trans ((mul_le_mul_of_nonneg_left uq hA).trans_eq (mul_div_assoc _ _ _).symm)

end YM.Integration.WilsonPositionScaleLawOneFee
end
