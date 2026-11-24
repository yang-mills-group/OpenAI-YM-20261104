import YM.Integration.WilsonIndependentCollarClockRoom

/-! The two actual physical print invoices on all sufficiently late original
thermally admitted boards. The coupling exponent is fixed by the restored
incoming dose and shelf before the working jet order is chosen. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentCollarPhysicalCharges
open Filter Finset Lattice RG Wilson Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Earn.Scene
open PhysicalNext.Repeat.Legato Push.AbsoluteSums AllOrder AllOrder.Floe Laurent Comparison.Density
open Transport AnalyticBridge.SectorAffine.Offset
open WilsonIndependentCollarPrintWallet WilsonIndependentCollarPhysicalRates
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius
variable {G : Gauge} {V : Type} [DecidableEq V] {Γ:Census V}

theorem original (R:Run G) (simple:G.Simple) (D d:ℕ) (tube:LinkTube G)
    (J:ℕ) (ℓ p pieces depth:Bool→ℕ) (cap:∀a,depth a≤d) :
    let course:=R.family.path.levels
    ∀ᶠi:ℕ in atTop,∀(β:ℝ)(B:BudgetPoint)(σ:Bool→ℝ)
      (w:Bool→V→ℝ)(s:Γ.Mode)(c b:Bool→ℝ)(C:ℝ),
    let H:=course.clock.hatBeta (i+1)
    let g:=(Real.sqrt β)⁻¹
    let θ:=fun a=>WilsonEmittedCompactTariff.strip (σ a)
    H/2≤β → B.supportExponent+2≤102 → B.B=Nat.ceil ((Real.log H)^2) →
    (∀a,0<σ a) → (∀a,Real.exp ((σ a)⁻¹^2)≤H) →
    (∀a,0≤restored w s c b a) → (∑a,restored w s c b a≤C*(g^D)⁻¹) →
    groupPrice tube 0 * WilsonEmittedFiledCatalogue.rent (G:=G) w c ℓ B (p:=p)
      (pieces:=pieces) (depth:=depth) (b:=b) (α:=fun _=>B.supportExponent+2) (θ:=θ) s J 0 ≤
        C * (g^(D+1))⁻¹ ∧
    WilsonEmittedLongInvoice.gross w c (fun _=>0) B s 0 g p pieces depth b θ ≤
        C * (g^(D+d+2))⁻¹ := by
  let course:=R.family.path.levels
  let H(i:ℕ):=course.clock.hatBeta (i+1)
  let height(a:Bool):=p a+depth a+1
  have choose (a:Bool) : ∀ᶠi:ℕ in atTop,∀β:ℝ,H i/2≤β →
      jetConstant G J (ℓ a) (height a) (pieces a)*(1+Real.log (H i))^(13+J*height a)≤Real.sqrt β ∧
      wordConstant G (height a) (pieces a)*(1+Real.log (H i))^13≤Real.sqrt β := by
    filter_upwards [WilsonIndependentCollarClockRoom.original R simple
      (jetConstant G J (ℓ a) (height a) (pieces a)) (13+J*height a),
      WilsonIndependentCollarClockRoom.original R simple (wordConstant G (height a) (pieces a)) 13] with i jet word
    intro β thermal
    exact ⟨by simpa only [inv_inv] using jet β thermal,by simpa only [inv_inv] using word β thermal⟩
  have rise:Tendsto course.clock.hatBeta atTop atTop := tendsto_atTop_add_const_left _ _
    (course.S.divergent.const_mul_atTop (Gauge.slopeConstant_pos simple))
  filter_upwards [choose false,choose true,(rise.comp (tendsto_add_atTop_nat 1)).eventually_ge_atTop 2]
    with i off on late
  intro β B σ w s c b C Hi g θ thermal fence square pos reserve nonnegative income
  have late':2≤Hi:=late
  have good:1≤β:=by linarith
  have root:1≤Real.sqrt β:=by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt good
  have root_pos:0<Real.sqrt β:=zero_lt_one.trans_le root
  have gp:0<g:=inv_pos.mpr root_pos
  have small:g≤1:=(inv_le_one₀ root_pos).mpr root
  have paid(a:Bool):groupPrice tube 0*jetRate G B J (ℓ a) (p a) (pieces a) (depth a) (θ a)≤Real.sqrt β ∧
      wordRate B (p a) (pieces a) (depth a) (θ a)≤Real.sqrt β := by
    obtain ⟨js,ws⟩:=WilsonIndependentCollarPhysicalRates.original G B tube J (ℓ a) (p a) (pieces a) (depth a)
      (pos a) fence (reserve a) square
    cases a with
    | false => exact ⟨js.trans (off β thermal).1,ws.trans (off β thermal).2⟩
    | true => exact ⟨js.trans (on β thermal).1,ws.trans (on β thermal).2⟩
  obtain ⟨js,ws⟩:=both w s c b θ ℓ p pieces depth B J g tube d (C*(g^D)⁻¹) (Real.sqrt β)
    gp small root_pos.le nonnegative income cap (fun a=>(paid a).1) (fun a=>(paid a).2)
  have reverse:g⁻¹=Real.sqrt β:=inv_inv _
  constructor
  · convert js using 1
    rw [pow_succ,mul_inv_rev,←reverse]; ring
  · convert ws using 1
    rw [show D+d+2=D+1+(d+1) by omega,pow_add,pow_succ g D,mul_inv_rev,mul_inv_rev,←reverse];ring

end YM.Integration.WilsonIndependentCollarPhysicalCharges
