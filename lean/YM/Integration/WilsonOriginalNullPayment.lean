import YM.Integration.WilsonOriginalNullLeaf
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Blush.Parcel

/-! Payment for the complex singleton and its original rooted offspring. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalNullPayment
open Function Filter Set Lattice RG Pressure Tree Wilson Finset MeasureTheory
open PhysicalNext Repeat Legato Graces
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork Roof Daisy Charity Rain Roost Lotus Blush Mallow
open UVNext.CouplingReset Animals Marlin Progress.DirectedRecipe Ovens Ovens.Pipes
open Extra.Histories Next.Foundations Labels Peak Mercury
open AllOrder AllOrder.Transit WheelP AllOrder.Floe
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

section localSum
variable {G : Gauge} {c f ℓ : Side} {S : StepData c f} {T : Tube G S}
    {P : Teller G} {Q : ConnectedActivityE6.Target G P} {w x μ C : ℝ}
    {ord : Target.Order G w} {R : RG.Rep G f}
variable (H : Cash w x μ ℓ Q ord C T R) (M : Cloud R) (B : BudgetPoint)
    (a : Site c) (v : ℂ)
def Isolated (price : ℝ) : Prop :=
  ∃ s : H.fragrances → ℝ,
    SumBudget (fun z => Local.reservedMass B (locus M.live H a z) (s z)) price ∧
    ∀ z, prince M.live H z → B.supBounds a (locus M.live H a z) (pane H M v z) (s z)

theorem combine {key : ℕ} (turn : M.live.turn=.logKey key)
    (smoothR : B.Regular (plate H key).support (matin M.live H (icon H key) Chi.canonical))
    (smoothI : B.Regular (plate H key).support (matin M.pale H (icon H key) Chi.canonical))
    {t u fee : ℝ}
    (hR : B.supBounds a (plate H key).support (matin M.live H (icon H key) Chi.canonical) t)
    (hI : B.supBounds a (plate H key).support (matin M.pale H (icon H key) Chi.canonical) u)
    (pR : Local.reservedMass B (plate H key).support t ≤ fee)
    (pI : Local.reservedMass B (plate H key).support u ≤ fee) :
    Isolated H M B a v (‖v‖*(fee+fee)) := by
  let e := ‖v‖*(t+u)
  have pos : 0 ≤ e := mul_nonneg (norm_nonneg _) (add_nonneg hR.1 hI.1)
  refine ⟨fun b => if b = icon H key then e else 0, ?_, ?_⟩
  · let F (b : H.fragrances) := Local.reservedMass B (locus M.live H a b)
        (if b = icon H key then e else 0)
    have off b (hb : b ≠ icon H key) : F b = 0 := by unfold F; rw [if_neg hb,Local.reservedMass,mul_zero]
    have hs : Summable F := summable_of_ne_finset_zero (s:={icon H key}) (fun b hb => off b (by simpa using hb))
    change SumBudget F _
    refine ⟨fun b => ?_, hs, ?_⟩
    · unfold F
      split
      · exact mul_nonneg (Real.exp_pos _).le pos
      · rw [Local.reservedMass,mul_zero]
    rw [tsum_eq_single (icon H key) off]
    unfold F
    rw [if_pos rfl, grinchY H M.live key turn]
    calc
      _ = ‖v‖ * (Local.reservedMass B (plate H key).support t +
              Local.reservedMass B (plate H key).support u) := by unfold Local.reservedMass e; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add pR pI) (norm_nonneg _)
  · intro b hb
    have one : b = icon H key := (grinch H M.live key turn).2 _ hb
    subst b
    rw [grinchY H M.live key turn]
    simp only [if_true]
    have imag := bound_smul Complex.I (pricingG smoothI hI)
    rw [Complex.norm_I,one_mul] at imag
    exact bound_smul v (bound_add (ornate smoothR) (regular_smul _ (ornate smoothI)) (pricingG smoothR hR) imag)
end localSum

variable {G : Gauge} (R : Run G) {m N per k i d : ℕ}
    (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin)
    (Ψ : ∀ j, RG.Rep G (R.family.side j per))
    (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
    (start : m ≤ i) (live : i < N)
local notation "U" => Ψ (i+1)
local notation "B" => R.alloy.B.a.budget i
local notation "Ω" => R.alloy.B.a.clock.op i per
local notation "L" => R.rolls.L (R.alloy.B.a.clock.J (i+1))
local notation "p" => R.metals.p.profile (R.alloy.B.a.clock.J i)
local notation "room" => QuadraticLocal.Advent.spare R π Γ Ψ course (Nat.le_succ_of_le start) live
local notation "zeroI" => WilsonOriginalNullHouse.point

variable (S : Spring R.kit N i per 0 0 (fun _ => Ψ (i+1)))
    (o : Site (R.family.side (i+1) per)) (X : Support (R.family.side (i+1) per))
    (f : Config G (R.family.side (i+1) per) → ℂ)
    (hf : RegFit (Ψ (i+1)) o d (hol G) X f) (c : ℝ) (hc : (Ψ (i+1)).p.supBounds o X f c)
set_option quotPrecheck false
local notation "K0" => houseS S zeroI
local notation "cloud" => float (Ψ (i+1)) o X hf.anchor f c hf.smooth hc (QuadraticLocal.Advent.spare R π Γ Ψ course (Nat.le_succ_of_le start) live)
local notation "a0" => (Ω).ratio.parent o
local notation "scale" => ((L).val : ℂ)^d

include course start live hf hc
theorem isolated (hd : d+3 ≤ R.alloy.B.a.clock.J i) :
    Isolated K0 cloud B a0 scale (coinFee G p d L * (U).p.mass X c) := by
  let T : Cloud (Ψ (i+1)) := float (Ψ (i+1)) o X hf.anchor f c hf.smooth hc (QuadraticLocal.Advent.spare R π Γ Ψ course (Nat.le_succ_of_le start) live)
  let K := K0
  let row := found o X hf.anchor
  have hk : T.live.turn = .logKey row := rfl
  have hi : T.pale.turn = .logKey row := rfl
  obtain ⟨x, h₁, px⟩ := WilsonOriginalNullLeaf.component R π Γ Ψ course start live hd S o X f hf c hc Complex.reCLM juror
  obtain ⟨y, h₂, py⟩ := WilsonOriginalNullLeaf.component R π Γ Ψ course start live hd S o X f hf c hc Complex.imCLM jurorI
  have smooth (M : Lotus.Leaf U) (h : M.turn=.logKey row) :
      (B).Regular (plate K row).support (matin M K (icon K row) Chi.canonical) := by
    let step := step_paid R.alloy.B.a i
    let known := S.knows (0:ℝ) zeroI.2
    have main := R.b.r _ _ (R.alloy.B.valid.pays i) _ step |>.1.2
    let J := R.kit.pledging.conducts
    obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,N₀,hN⟩ :=
      main _ _ _ _ (Opera.protocol R.alloy.B live J.full (n:=per)) _ _ K
    have plays := (Psalm.Stage.directed J.hearing R.alloy.B live known.2 known.1
      (fun j hj => J.full _ _ _ (by simp at hj; omega))).1.enabled.make
    have budget : (U).p = R.alloy.B.a.budget (i+1) := known.1.point
    exact Mercury.cornice K M row h (R.kit.recordP _ _) Chi.canonical N₀
      (budget.symm ▸ plays : Heir.Plays _ _ (B) (U).p _ _ _) hN (Rain.jersey (A:=R.alloy) (m:=i)|>.1.le)
  let fee := winG G p d L * (U).p.mass X c
  have eqFee : ‖scale‖*(fee+fee) = coinFee G p d L * (U).p.mass X c := by
    simp only [norm_pow,Complex.norm_natCast]
    unfold fee winG
    field_simp
    ring
  rw [←eqFee]
  exact combine K T B a0 scale hk (smooth T.live hk) (smooth T.pale hi) h₁ h₂ px py

end YM.Integration.WilsonOriginalNullPayment
