import YM.Integration.WilsonPositionScaleLawGuardReduction

/-! Two actual signed numerical tests yield the full homogeneous operator scale law. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawGuardLittle
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

open Asymptotics
open scoped Asymptotics
open WilsonPositionScaleLawHome (sweep)
open WilsonPositionScaleLawGuardReduction (clockFee)
open WilsonPositionScaleLawThermometerPay (target)

theorem absorb {ι E V W:Type*}[Norm E][Norm V][Norm W]{l:Filter ι}
    {u:ι→E}{v:ι→V}{w:ι→W}{g:ι→ℝ}{K:ℝ}(q:ℕ)(hK:0≤K)(small:Tendsto g l (𝓝 0))
    (field:v=o[l] (fun z=>g z^q))(clock:w=o[l] (fun z=>g z^q))
    (money:∀ᶠz in l,‖u z‖≤K*(‖v z‖+‖w z‖+|g z|^(q+1))):u=o[l] (fun z=>g z^q):=by
  apply isLittleO_iff.mpr;intro ε hε
  let δ:=ε/(3*K+1)
  have den:0<3*K+1:=by linarith
  have hp:0<δ:=div_pos hε den
  filter_upwards [money,isLittleO_iff.mp field hp,isLittleO_iff.mp clock hp,Metric.tendsto_nhds.mp small δ hp] with z cost hv hw hz
  simp only [Real.norm_eq_abs,abs_pow] at hv hw ⊢
  have ready:|g z|≤δ:=by simpa only [dist_zero_right,Real.norm_eq_abs] using hz.le
  have tail:|g z|^(q+1)≤δ*|g z|^q:=by
    rw [pow_succ,mul_comm _ |g z|]
    exact mul_le_mul_of_nonneg_right ready (pow_nonneg (abs_nonneg _) _)
  have cap:K*(δ+δ+δ)≤ε:=calc
    _≤(3*K+1)*δ:=by nlinarith
    _=ε:=mul_div_cancel₀ _ (ne_of_gt den)
  calc
    _≤K*(‖v z‖+‖w z‖+|g z|^(q+1)):=cost
    _≤K*(δ*|g z|^q+δ*|g z|^q+δ*|g z|^q):=mul_le_mul_of_nonneg_left (add_le_add (add_le_add hv hw) tail) hK
    _=K*(δ+δ+δ)*|g z|^q:=by ring
    _≤_:=mul_le_mul_of_nonneg_right cap (pow_nonneg (abs_nonneg _) _)

include H in
theorem realFee (q:ℕ)(z:ℝ×Ratio):clockFee F J Z M ν q z=‖gθ (z.2.val*z.1)-(target Z M ν F J q z).re‖:=by
  let u:=target Z M ν F J q z
  have iu:u.im=0:=by
    have fixed:=congrArg Complex.im (WilsonPositionScaleLawThermometerScale.real Z M H ν F J q z)
    change -u.im=u.im at fixed
    linarith
  have re:(u.re:ℂ)=u:=Complex.ext (by simp) (by simp [iu])
  change ‖(gθ (z.2.val*z.1):ℂ)-u‖=‖gθ (z.2.val*z.1)-u.re‖
  calc _=‖(gθ (z.2.val*z.1):ℂ)-(u.re:ℂ)‖:=congrArg (fun a:ℂ=>‖(gθ (z.2.val*z.1):ℂ)-a‖) re.symm
       _=_:=by rw [←Complex.ofReal_sub,Complex.norm_real]

variable (lead:Leading F J){Y:(Bel R.family.book).Hierarchy}(paid:∀d,∀ᶠr in trail,Frame.obedient F Y (J r) d)
    (funded:Coupling G (kinetic Z F J))

def scale (d q:ℕ):Prop:=(fun z:ℝ×Ratio=>dressed Z F J d z.1 z.2-WilsonPositionScaleLawGuardPhysical.expected F J Z M ν d q z.1 z.2)
    =o[sweep] (fun z=>gθ z.1^q)

include H lead paid funded in
theorem measured (d q:ℕ)
    (field:(fun z=>exactOp F J Z.store d z-WilsonPositionScaleLawQinter.prediction Z M ν F J d q z)=o[sweep] (fun z=>gθ z.1^q))
    (clock:(fun z:ℝ×Ratio=>gθ (z.2.val*z.1)-(target Z M ν F J q z).re)=o[sweep] (fun z=>gθ z.1^q)):scale F J Z M ν d q:=by
  obtain ⟨K,hK,price⟩:=WilsonPositionScaleLawGuardReduction.original F J Z M H ν lead paid funded d q
  have tiny:Tendsto (fun z:ℝ×Ratio=>gθ z.1) sweep (𝓝 0):=(WilsonPositionPrescribedZero.measured F J Z.store lead paid hG Z.criterion).comp tendsto_fst
  apply absorb q hK tiny field clock
  filter_upwards [price] with z cost
  simpa only [WilsonPositionScaleLawGuardReduction.remainder,WilsonPositionScaleLawGuardReduction.fieldFee,
    realFee F J Z M H ν,Complex.norm_real,Real.norm_eq_abs] using cost

include H lead paid funded in
theorem original (d q:ℕ)(raw:WilsonPositionScaleLawBranch.Raw J d)(six:WilsonPositionScaleLawCompactBranch.Raw J 6)
    (field:(WilsonPositionScaleLawQinter.measured Z M ν F J d q)=o[sweep] (fun z=>gθ z.1^q))
    (clock:WilsonPositionScaleLawThermometerScale.Earned Z M ν F J q):scale F J Z M ν d q:=
  measured F J Z M H ν lead paid funded d q
    (WilsonPositionScaleLawQinter.qinter Z M H ν F J lead paid d q raw field)
    (WilsonPositionScaleLawThermometerScale.qinterg Z M H ν F J lead paid q six clock)

end YM.Integration.WilsonPositionScaleLawGuardLittle
