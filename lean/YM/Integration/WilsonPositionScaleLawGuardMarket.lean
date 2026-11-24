import YM.Integration.WilsonPositionScaleLawGuardAges
import YM.Integration.WilsonPositionScaleLawGuardCaps
import YM.Integration.WilsonPositionScaleLawGuardCombine

/-! Uniform payment of every independent and both original home terms. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawGuardMarket
open Function Filter Set Spec Table Extraction OPE OPE.Orbits Climb PhysMS Trace.Pilot
open Maxwell Maxwell.Free XSpace XSpace.Normalize PhysicalNext.Repeat.Legato
open MS MS.Land MS.Fleet MS.Book.Program FVA2 FVA2.Register FVA2.Scale PowerSeries
open WilsonPositionScaleLawHome (Ratio)
open WilsonPositionScaleLawGuardInvoice (sheet issue)
open WilsonPositionScaleLawGuardReceipt (fee)
open WilsonPositionScaleLawDressedBudget (home residual)
open WilsonPositionScaleLawDressedGear (engine cap)
open WilsonPositionScaleLawDressedTransport (dressed guard)
open WilsonPositionScaleLawNative (exactOp)
open WilsonPositionScaleLawKinetic (kinetic)
open scoped Topology Polynomial Classical BigOperators

variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}
    (F:Final R.family f S)(J:ℝ→tower S)(Z:WilsonPrescription G){hG:G.Simple}
    (M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))){σ:Prescription (Press.portDeck G)}
    {b:Bool}(H:Main.Match Z hG M σ b)(ν:ℝ)
set_option quotPrecheck false
local notation "gθ"=>kinetic Z F J

open WilsonPositionScaleLawGuardHomePrint (taylor)
open WilsonPositionScaleLawGuardCombine (Cover)
open WilsonPositionScaleLawGuardLipschitz (slope)
local instance half:WilsonPositionScaleLawWindow.RangeSpec:=⟨1/2,by norm_num⟩

def counted (d q:ℕ)(L:ℝ)(z:ℝ×Ratio):Prop:=
  let p:=sheet R.family Z M ν z.2 d
  let x:ℂ:=gθ z.1
  let y:ℂ:=gθ (z.2.val*z.1)
  Cover p (engine R.family d z.2) q x y (home F J Z d z.1) (home F J Z d (z.2.val*z.1)) L ∧
    ‖x‖≤1 ∧ ‖y‖≤1 ∧ ‖(trunc (q+1) p.scalar).eval x‖≤1

variable (lead:Leading F J){Y:(Bel R.family.book).Hierarchy}(paid:∀d,∀ᶠr in trail,Frame.obedient F Y (J r) d)
    (funded:Coupling G (kinetic Z F J))

include H lead paid funded in
theorem original (d q:ℕ):∃L:ℝ,0≤L ∧ ∀ᶠz:ℝ×Ratio in WilsonPositionScaleLawHome.sweep,counted F J Z M ν d q L z:=by
  let C:=R.family
  let X:=(Bel C.book).Field d
  letI :NormedAddCommGroup (X→L[ℂ]X):=ContinuousLinearMap.toNormedAddCommGroup
  let k:=cap C d
  let slope0:=slope q (WilsonPositionScaleLawGuardLift.pack C (WilsonPositionScaleLawDressedTransport.adjust Z d))
  have s0:0≤ slope0:=Finset.sum_nonneg fun j _=>mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)
  have k0:0≤k:=WilsonPositionScaleLawDressedGear.capPositive C
  obtain ⟨B,ms⟩:=WilsonPositionScaleLawGuardCaps.original C Z M H ν d q
  obtain ⟨K,hK,both⟩:=WilsonPositionScaleLawGuardHomeTaylor.original Z F J
    (WilsonPositionHomogeneousCoefficients.purchased Z H) hG funded d q
  have b0:0≤B:=zero_le_one.trans ms.one
  let extra:=K*(2:ℝ)^(q+1)
  have e0:0≤extra:=mul_nonneg hK (by positivity)
  let L:=2+k+B+slope0+K+extra
  have twoL:2≤L:=by dsimp only [L];linarith
  have kL:k≤L:=by dsimp only [L];linarith
  have bL:B≤L:=by dsimp only [L];linarith
  have sL:slope0≤L:=by dsimp only [L];linarith
  have baseL:K≤L:=by dsimp only [L];linarith
  have extraL:extra≤L:=by dsimp only [L];linarith
  have l0:0≤L:=le_trans (by norm_num : (0:ℝ)≤2) twoL
  refine ⟨L,l0,?_⟩
  filter_upwards [WilsonPositionScaleLawGuardAges.original hG funded B,
    (tendsto_fst (f:=trail) (g:=(⊤:Filter Ratio))).eventually both,
    WilsonPositionScaleLawCompactNative.bothHomes.eventually both,
    WilsonPositionScaleLawGuardAges.operator F J Z hG lead paid d] with z age aa bb op
  let p:=sheet C Z M ν z.2 d
  let x:ℂ:=gθ z.1
  let y:ℂ:=gθ (z.2.val*z.1)
  have nx:‖x‖=gθ z.1:=by change ‖(gθ z.1:ℂ)‖=_;rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos age.1]
  have ny:‖y‖=gθ (z.2.val*z.1):=by change ‖(gθ (z.2.val*z.1):ℂ)‖=_;rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos age.2.1]
  have hx:‖x‖≤1:=nx.trans_le age.2.2.2.1
  have hy:‖y‖≤1:=ny.trans_le age.2.2.2.2.1
  have clock:‖(trunc (q+1) p.scalar).eval x‖≤1:=by
    apply (ms.clock z.2 x hx).trans;rw [nx];exact age.2.2.2.2.2
  refine ⟨⟨l0,(WilsonPositionScaleLawGuardTurning.forward C z.2).trans kL,
    (ms.position z.2 x hx).trans bL,(ms.homogeneous z.2 x hx).trans bL,sL,(ms.fringe z.2).trans bL,op.trans twoL,?_,?_⟩,hx,hy,clock⟩
  · change ‖taylor C Z d q (gθ z.1)-home F J Z d z.1‖≤L*‖x‖^(q+1)
    rw [norm_sub_rev,nx]
    exact aa.trans (mul_le_mul_of_nonneg_right baseL (pow_nonneg age.1.le _))
  · change ‖home F J Z d (z.2.val*z.1)-taylor C Z d q (gθ (z.2.val*z.1))‖≤L*‖x‖^(q+1)
    rw [nx]
    calc
      _≤K*(gθ (z.2.val*z.1))^(q+1):=bb
      _≤K*(2*gθ z.1)^(q+1):=mul_le_mul_of_nonneg_left (pow_le_pow_left₀ age.2.1.le age.2.2.1 _) hK
      _=extra*(gθ z.1)^(q+1):=by rw [mul_pow];dsimp only [extra];ring
      _≤_:=mul_le_mul_of_nonneg_right extraL (pow_nonneg age.1.le _)

end YM.Integration.WilsonPositionScaleLawGuardMarket
