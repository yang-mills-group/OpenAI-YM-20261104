import YM.Integration.QLocalRequestedHeir
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Census.Coffer
import YM.Integration.QLocalInheritedLargeCover
import YM.RG12.Burst.Wardrobe

/-! The connected activity Cash, its nonlinear Captain and the signed inherited
    Brim price purchased together on the same two-ended physical tube. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QLocalRequestedSectorSale
open Filter Function Set Lattice Wilson RG Pressure Precision Marker
open PhysicalNext PhysicalNext.Repeat PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir
open PhysicalNext.JointLoad.Psalm ConnectedActivityE6 Push.SectorMeasure
open ConnectedActivityE6.Blaze ConnectedActivityE6.Blaze.March Push.AbsoluteSums
open QLocalRequestedHeirQuote FullQLocal FullQLocal.RenderedStep
open scoped Topology Classical

variable {G : Gauge} {V : Type} (J : Request V) {P : Teller G}

def target (Q : ConnectedActivityE6.Target G P) : ConnectedActivityE6.Target G (teller J P) where
  ε := min Q.ε (J.inputSupport/8)
  exp := max (J.outputSupport+5) (P.below.supportExponent+3)
  δ := Q.δ
  rate := -(15/32:ℝ)
  halo := 500
  buys := le_rfl
  table := Q.table
  table_exists := Q.table_exists
  usable := lt_min Q.usable (div_pos J.input_support_pos (by norm_num))
  pos := Q.pos
  bound := (show 0≤J.outputSupport+5 by linarith [J.output_support_pos]).trans (le_max_left _ _)
  start := by norm_num
  stop := by norm_num
  grants := by
    have e := min_le_left Q.ε (J.inputSupport/8)
    have s := min_le_right Q.ε (J.inputSupport/8)
    change 4*min _ _<J.inputSupport ∧ 8*min _ _<P.top.width ∧ 8*min _ _<P.below.width
    exact ⟨by linarith [J.input_support_pos],by linarith [Q.grants.2.1],by linarith [Q.grants.2.2]⟩

def expense (Q : ConnectedActivityE6.Target G P) : (target J Q).Expense where
  degrees := J.outputFieldOrder
  earn := QLocalRequestedHeirQuote.toll J
  one := 1
  two := 1
  wanting := -(9/20:ℝ)
  price := by dsimp [QLocalRequestedHeirQuote.toll]; linarith [J.output_support_pos]
  first := zero_lt_one
  second := zero_lt_one
  worth := (show QLocalRequestedHeirQuote.toll J+1+1≤J.outputSupport+5 by unfold QLocalRequestedHeirQuote.toll; linarith).trans (le_max_left _ _)
  reach := by norm_num [target]
  arrives := by norm_num

structure Booking (G : Gauge) where
  record : Heir.Record
  W : ℝ
  μ : ℝ
  c : ℝ
  order : Target.Order G W

/-- The stage-dependent extraction fee is known when this block is fixed.
    The original inverse coupling can then pay it for any power at least 1/80. -/
def Thermal (G : Gauge) (L : Side) (j : ℕ) (fee x : ℝ) : Prop :=
  1≤betaF G x L ∧ (1+|fee|)*(1+(j:ℝ))≤betaF G x L^((1/80):ℝ)

theorem thermal_after (G : Gauge) (L : Side) (j : ℕ) (fee : ℝ) : ∀ᶠ x : ℝ in atTop, Thermal G L j fee x :=
  ((Work.E09.betaF_growth G L).eventually_ge_atTop 1).and
    (((tendsto_rpow_atTop (show 0<(1/80:ℝ) by norm_num)).comp (Work.E09.betaF_growth G L)).eventually_ge_atTop _)

theorem weighted_power (G : Gauge) (L : Side) (j : ℕ) (fee x : ℝ) (h : Thermal G L j fee x)
    (d : ℝ) (hd : (1/80:ℝ)≤d) : (1+|fee|)*betaF G x L^(-d)≤(1+(j:ℝ))⁻¹ := by
  have pos : 0<betaF G x L := zero_lt_one.trans_le h.1
  rw [Real.rpow_neg pos.le,←div_eq_mul_inv,←one_div,div_le_div_iff₀ (Real.rpow_pos_of_pos pos d) (by positivity),one_mul]
  exact h.2.trans (Real.rpow_le_rpow_of_exponent_le h.1 hd)

def vacant (G : Gauge) : Booking G :=
  ⟨Heir.Suite.one,1,1,0,Classical.choice (Target.baseline G 1)⟩

def floor (Q : ConnectedActivityE6.Target G P) (Δ : Daisy.Charity.RG12.Decal G) : ℕ :=
  max (max (Target.quotesTogether (target J Q) (expense J Q)).choose (Height.sailing (target J Q)).choose)
    (Δ.good (teller J P) (target J Q) (expense J Q)).choose

def Outer (Q : ConnectedActivityE6.Target G P) (b : Booking G) (L : Side) (x : ℝ) : Prop :=
  ∀ {c f : Side} {S : StepData c f} (T : Tube G S), Works (teller J P) L x S T → SliceRows.Stamp T →
    ∀ (Y : Rep G f) (H : Cash b.W x b.μ L (target J Q) b.order b.c T Y),
      ∃ u d v t a w r B q : ℝ, ∃ k : ℕ,
      ∃ N : Captain H J.outputFieldOrder u d v t a w r B q k Chi.canonical,
        Ac.Hit (Captain.reachability (H:=H)) (radiusB x)
          (fun z => if Height.tired H z then N.markΦ z J.outputDistanceOrder else 0)
          (QLocalRequestedHeirQuote.toll J) (Real.exp 1 * betaF G x L^(-(19/16):ℝ))

theorem outer (Q : ConnectedActivityE6.Target G P) (b : Booking G) (L : Side) (hμ : 0<b.μ) :
    ∀ᶠ x : ℝ in atTop,
      Height.Skill (expense J Q) L b.W b.μ b.c b.order x J.outputFieldOrder J.outputDistanceOrder Chi.canonical →
        Outer J Q b L x := by
  have h := Height.cruising (target J Q) (expense J Q) L hμ J.outputFieldOrder J.outputDistanceOrder
    (by norm_num [expense]) 1 zero_lt_one
  have reserve := ((tendsto_rpow_atTop (show (0:ℝ)<1/80 by norm_num)).comp
    (Work.E09.betaF_growth G L)).eventually_ge_atTop (Real.exp (Height.asset (expense J Q)-1))
  filter_upwards [h,(Work.E09.betaF_growth G L).eventually_gt_atTop 0,reserve]
    with x hcr hb hs skill c f S T works stamp Y H
  obtain ⟨u,d,v,t,a,w,r,B,q,i,k,⟨N,heavy⟩,registered,fee⟩ := skill.2 c f S T works stamp Y H
  obtain ⟨grow,mark,small,final⟩ := hcr
  obtain ⟨army,localFee,_⟩ := final B i k registered N.balance fee
  have price : i≤Height.asset (expense J Q) := by
    have e := registered.little
    unfold Height.asset
    linarith
  have hit := QLocalInheritedLargeCover.hit N grow heavy army mark skill.1 small localFee hb
    registered.delta price fee
  change Real.exp (Height.asset (expense J Q)-1) ≤ betaF G x L^((1/80):ℝ) at hs
  rw [Real.exp_sub] at hs
  have pay : Real.exp (Height.asset (expense J Q)) ≤ Real.exp 1*betaF G x L^((1/80):ℝ) := by
    simpa only [mul_comm (Real.exp 1)] using (div_le_iff₀ (Real.exp_pos 1)).mp hs
  have price : Real.exp (Height.asset (expense J Q))*betaF G x L^((expense J Q).wanting-3/4) ≤
      Real.exp 1*betaF G x L^(-(19/16):ℝ) := calc
    _ ≤ (Real.exp 1*betaF G x L^((1/80):ℝ))*betaF G x L^((expense J Q).wanting-3/4) :=
      mul_le_mul_of_nonneg_right pay (Real.rpow_nonneg hb.le _)
    _ = _ := by rw [mul_assoc,←Real.rpow_add hb]; norm_num [expense]
  exact ⟨u,d,v,t,a,w,r,B,q,k,N,fun y => budget_loosen (hit y) price⟩

def Strong (Q : ConnectedActivityE6.Target G P) (b : Booking G) (L : Side) (x : ℝ) : Prop :=
  (∀ (c f : Side) (S : StepData c f) (T : Tube G S) (Y : Rep G f)
    (H : Cash b.W x b.μ L (target J Q) b.order b.c T Y),
      Cash.Renewed J.outputFieldOrder (P.below.supportExponent+1) 1 1 H) ∧
  Cash.armK (target J Q) L b.μ x 0 J.outputFieldOrder ≤ Real.exp (-(4:ℝ)*(Vac.Numbers.P x)^((1:ℝ)/5))

theorem hard_after (Q : ConnectedActivityE6.Target G P) (b : Booking G) (L : Side) (hμ : 0<b.μ) :
    ∀ᶠ x : ℝ in atTop, Strong J Q b L x := by
  have reserve : P.below.supportExponent+1+1+1≤(target J Q).exp :=
    (show P.below.supportExponent+1+1+1≤P.below.supportExponent+3 by linarith).trans (le_max_right _ _)
  have h := Cash.anew (target J Q) L b.order b.c hμ J.outputFieldOrder
    (show 0≤P.below.supportExponent+1 by linarith [P.below.price_pos]) zero_lt_one zero_lt_one reserve
  have bill := Cash.dictionary_fit (target J Q) L J.outputFieldOrder 0 hμ
    (show (0:ℝ)≤4 by norm_num) (show (0:ℝ)≤1/5 by norm_num) (by norm_num)
  exact h.and bill

structure Window (Δ : Daisy.Charity.RG12.Decal G) (Q : ConnectedActivityE6.Target G P) (C : Libretto G J.outputFieldOrder)
    (b : Booking G) (H : Patch) (x γ : ℝ) : Prop where
  heir : Ready J P H C b.record x
  ledger : Target.Ledgered (expense J Q) H.L b.W b.μ b.c b.order x
  captain : Height.Skill (expense J Q) H.L b.W b.μ b.c b.order x
    J.outputFieldOrder J.outputDistanceOrder Chi.canonical
  outer : Outer J Q b H.L x
  hard : Strong J Q b H.L x
  analytic : Δ.rub (teller J P) (target J Q) (expense J Q) H.L b.W b.μ b.order (teller J P).below H.J x
  glyph : QLocalInheritedGlyphPurchase.Chart (target J Q) b.order b.record C (toll J)
    (QLocalInheritedSourcePrice.fee J C 505) 505 J.outputDistanceOrder Chi.canonical H.L x γ

theorem sale (hG : G.Simple) (Δ : Daisy.Charity.RG12.Decal G) (Q : ConnectedActivityE6.Target G P) (H : Patch)
    (C : Libretto G J.outputFieldOrder) (branch : H.Branches P.bind G)
    (license : licensed C.δ C.N H.L) (cost : floor J Q Δ≤H.L.val)
    (stage : ∀ {c f : Side} (S : StepData c f) (T : Tube G S), (teller J P).Funds S T →
      ∀ F, Matins T F J.inputDistanceOrder (2*C.C) C.M)
    (γ : ℝ) (hγ : -(1/2:ℝ)<γ) :
    ∃ b : Booking G, ∀ᶠ x : ℝ in atTop, Window J Δ Q C b H x γ := by
  obtain ⟨D,hd,_,hready⟩ := songs J P H C branch license stage (show 0<(1/4:ℝ) by norm_num)
  have supply := Target.quotesTogether (target J Q) (expense J Q)
  obtain ⟨W,hW,μ,α,o,hμ,_,hs⟩ := (supply.choose_spec H.L
    ((le_max_left _ _).trans ((le_max_left _ _).trans cost))).exists
  have press := Height.sailing (target J Q)
  have hc := press.choose_spec H.L ((le_max_right _ _).trans ((le_max_left _ _).trans cost)) (expense J Q) W μ α o hW hμ
    J.outputFieldOrder J.outputDistanceOrder Chi.canonical
  have hg := QLocalInheritedGlyphPurchase.charts hG (target J Q) o D C (QLocalRequestedHeirQuote.toll J)
    (QLocalInheritedSourcePrice.fee J C 505) 505 J.outputDistanceOrder Chi.canonical H.L γ hγ hd
    ((by decide : 2≤6).trans J.field_minimum) (show 0≤QLocalRequestedHeirQuote.toll J by dsimp [QLocalRequestedHeirQuote.toll]; linarith [J.output_support_pos])
  refine ⟨⟨D,W,μ,α,o⟩,?_⟩
  have ho := outer J Q ⟨D,W,μ,α,o⟩ H.L hμ
  have hk := hard_after J Q ⟨D,W,μ,α,o⟩ H.L hμ
  have hΔ := (Δ.good (teller J P) (target J Q) (expense J Q)).choose_spec H.L ((le_max_right _ _).trans cost)
    W μ o (teller J P).below H.J (by norm_num [expense]) hW hμ
  filter_upwards [hready,hs,hc,ho,hk,hΔ,hg] with x h₁ h₂ h₃ h₄ h₅ h₆ h₇
  exact ⟨h₁,h₂,h₃,h₄ h₃,h₅,h₆,h₇⟩

end YM.Integration.QLocalRequestedSectorSale
end
