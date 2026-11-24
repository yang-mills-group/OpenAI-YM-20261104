import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Census.Coffer
import YM.LocalLTE.E6.Flare
import YM.LocalLTE.E6.Profit
/-! High rate tail control purchase (any size ℓ). Assemble later against
marker vouchers. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Height
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling
open Extra.Iteration Time Supply Input Testing
open ConnectedActivityE6.Blaze Blaze.March Captain PriceCompiler Silica
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge}
section thresholds
variable {P : Teller G} {Q : YM.ConnectedActivityE6.Target G P}
theorem byline (ℓ:ℕ) (_p : Q.Expense) (L:Side) {μ : ℝ} (hm : 0 < μ) : ∀ᶠ x in atTop,
    grow G L x ^ ℓ ≤ Real.exp (Q.mark L μ x) ∧ grow G L x ^ ℓ ≤ Real.exp (Q.ε*Pressure.Stores.till x) := by
  let t := -(ℓ:ℝ)-1
  have hf : Rate G L t (fun x=> Real.exp (-(Q.mark L μ x))) := by
    apply (Rate.monitor_cutoff (show 0<μ/4 by linarith) (show (0:ℝ)<2 by norm_num)).congr
    apply Eventually.of_forall; intro x
    dsimp only; rw [Real.rpow_two]
    change Real.exp (- Delay.hatWin G L _ _ x)=_; unfold Delay.hatWin; congr 1; ring
  have hD := (Rate.power (G:=G) (L:=L) (a:=3/8)).pow ℓ
  filter_upwards [(hD.mul hf).below (by unfold t; linarith) 1 zero_lt_one, (hD.mul (Rate.cutoff Q.usable (a:=t))).below (by unfold t; linarith) 1 zero_lt_one] with x he hh
  constructor
  · apply le_of_mul_le_mul_right _ (Real.exp_pos (-(Q.mark L μ x)))
    rw [← Real.exp_add, add_neg_cancel,Real.exp_zero]; exact (le_abs_self _).trans he
  apply le_of_mul_le_mul_right _ (Real.exp_pos (-Q.ε*Pressure.Stores.till x)); rw [← Real.exp_add, neg_mul, add_neg_cancel,Real.exp_zero]
  exact (le_abs_self _).trans (by simpa only [neg_mul,grow] using hh)

-- summarizing with membership in ANY stage with same symbol costs (we reuse
-- `Rich` to buy the preliminary grade, including low momentum components).
-- `Skill` analogue; includes support growth, cover budgets.
def Aerobics (p : Q.Expense) (L:Side) (W μ c : ℝ) (o: ConnectedActivityE6.Target.Order G W) (x e B₀: ℝ) (ℓ j n : ℕ) (χ:Chi): Prop:=
    let D:= grow G L x; let S:= Q; let y := asset p
    ∀ (c' f : Side) (K : StepData c' f) (T : Tube G K), Works P L x K T → Stamp T→
      ∀ (R:RG.Rep G f) (H:Cash W x μ L Q o c T R),
      (∀ i B k, Armada Q L μ p.earn x i B j k → 0 ≤ B →
        collars G i x j n*(salary Q L μ B x j k*(1-1/2)⁻¹) ≤ betaF G x L^p.wanting →
        Armada Q L μ p.earn x y B j k ∧ degreePrice (radiusB x) (D*salary Q L μ B x j k) y≤1/2 ∧
          (D^3)⁻¹*collars G y x j n*(D*salary Q L μ B x j k*(1-1/2)⁻¹) ≤ B₀ * δE x) →
      1 ≤ D → degreePrice (radiusB x) (D*(S.costs L μ 1 x 0).rootHit) S.δ ≤ 1/2 →
        ∃ (C' d v t A b r B q : ℝ) (k : ℕ) (N: Captain H j C' d v t A b r B q k χ),
          Ac.Hit (Captain.reachability (H:=H)) (radiusB x) (fun z=>if tiredN H ℓ z then N.markΦ z n else 0) p.earn (betaF G x L ^ e)
-- need pay D loss and cap with Rate. generous exponent
lemma aerodynamic (Q : YM.ConnectedActivityE6.Target G P) : ∃ m:ℕ, ∀ L:Side,m≤L.val → ∀ (X:Q.Expense) (W μ c:ℝ) (o:Target.Order G W), 0<W → 0<μ →
    ∀ e B₀:ℝ, ∀ ℓ j n χ, 3 ≤ ℓ → -(3/8:ℝ)*(ℓ-3:ℕ)< e →
      ∀ᶠ x:ℝ in atTop, Aerobics X L W μ c o x e B₀ ℓ j n χ := by
  obtain ⟨m,hm⟩:= adjudicateN P Q
  refine ⟨m,fun L hL X W μ c o hW hμ e B₀ ℓ j n χ hℓ he =>?_⟩
  by_cases hh : ∃ D : Patch,D.Branches P.bind G ∧ D.L=L ∧ D.J=P.j
  swap; · exact Eventually.of_forall fun x c' f S T h=> (hh ⟨S.patch,h.funds.kernel,h.length_eq,h.funds.atStep⟩).elim
  obtain ⟨D,hd,hF,hX⟩:=hh
  obtain ⟨A,a,C,d,v,t,r,B,q,k,hB,hq,H⟩:=hm L hL D hd j ℓ χ W hW μ hμ o
  obtain ⟨y,hg,hK⟩:= Armada.ensemble Q L hμ X.earn X.price (by linarith [X.worth,X.first,X.second]) j k hB
  let f x := ((grow G L x)^(ℓ-3))⁻¹
  have hu' : Rate G L (-(3/8:ℝ)*(ℓ-3:ℕ)) f := Rate.congr Rate.power (by
    filter_upwards [Delay.shift_pos G L] with x hx
    rw [neg_mul, Real.rpow_neg hx.le, Real.rpow_mul hx.le]; unfold f grow; norm_num)
  filter_upwards [byline ℓ X L hμ,H,hg n 0 X.wanting X.reach,hK,(hu'.mul_right |B₀|) _ he,eventually_ge_atTop (1:ℝ)] with x he' h hh hA hH hv
  intro U S i T hW hx R I hP hu hI
  simp only [pow_zero,mul_one] at hh
  obtain ⟨N,hN⟩:=h _ _ i T (hW.patch hF hX) hx _ _ I
  have htQ:=hP y _ _ hA N.balance ((le_abs_self _).trans hh)
  obtain ⟨hQ,hT,hq'⟩:=htQ
  refine ⟨_,_,_,_,_,_,_,_,_,_,N,fun t=> budget_loosen ((extensionN N hu hN n hQ he'.1 he'.2 hI hT) t) ?_⟩
  have hZ : 0 < grow G L x:= zero_lt_one.trans_le hu
  have hδ:0≤δE x:=Real.rpow_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) _; have hδ' : δE x≤1:= by
    have ht : Clock.gap x ≤1:= inv_le_one_of_one_le₀ (Real.one_le_sqrt.mpr hv); unfold δE; exact Real.rpow_le_one (inv_nonneg.mpr (Real.sqrt_nonneg _)) ht (by norm_num)
  refine le_trans ?_ ((le_abs_self _).trans hH); unfold f
  nth_rw 1 [show ℓ=3+(ℓ-3) by omega]
  rw [pow_add, mul_inv_rev]; change _ ≤ _* |B₀|
  -- use hq'
  rw [mul_assoc _ _ (collars ..),mul_assoc]; apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact hq'.trans ((mul_le_mul_of_nonneg_right (le_abs_self _) hδ).trans (mul_le_of_le_one_right (abs_nonneg _) hδ'))
end thresholds
end YM.PhysicalNext.Repeat.Height
