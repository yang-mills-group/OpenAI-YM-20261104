import YM.Integration.WilsonNeutralPointForecast
import YM.Integration.WilsonOlderFreshGraphFixedFigure

/-! A stage-only spatial width and its cash are booked on the same original
kernel register before the block lengths, cutoffs, marked courses or tests.
Every fixed horizon is admitted when its stage comes into use. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalSmallStrip
open Function Filter Finset Lattice RG RG.Shoot RG.Supply Wilson Precision Input Org
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato ThroughLaunch Next.Foundations Push.PriceCompiler
open FormalBulk08 FormalBulk08.Flat WilsonLimitConstruction.FundedCompanySelection
open QuadraticLocal QuadraticLocal.Advent
open scoped Topology Classical
variable {G:Gauge}

structure Menu (G:Gauge) where
  cap : KernelChoices → ℕ → ℕ → ℝ
  positive : ∀ K j H,0<cap K j H
  threshold : KernelChoices → ℕ → ℕ
  bill : KernelChoices → ℕ → ℕ → ℝ

def width (V:Menu G)(K:KernelChoices)(j H:ℕ):ℝ:=min 1 (V.cap K j H)

theorem width_pos (V:Menu G)(K:KernelChoices)(j H:ℕ):0<width V K j H:=
  lt_min zero_lt_one (V.positive K j H)

def Enrolled (V:Menu G)(K:KernelChoices)(A:Levels G):Prop:=
  (∀ j,V.threshold K j≤(A.clock.factor j).val) ∧
  ∀ i H,H≤A.clock.J i →
    Real.exp ((width V K (A.clock.J i) H)⁻¹^2)≤A.clock.hatBeta i ∧
    V.bill K (A.clock.J i) H ≤ min (Beaming.spray (A.clock.hatBeta (i+1)))
      (A.clock.hatBeta (i+1)^Beaming.grain (A.clock.J i))

def Filed (V:Menu G):Prediction G:=fun {M} {_} {A} _=>Enrolled V M.p.kernel A.B.a

private theorem spray (c:ℝ):∀ᶠ x:ℝ in atTop,c≤Beaming.spray x:=by
  have grow:Tendsto (fun x:ℝ=>Real.log (Real.log x)) atTop atTop:=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  filter_upwards [grow.eventually_ge_atTop 1,(Real.tendsto_exp_atTop.comp grow).eventually_ge_atTop c] with x hx hc
  apply hc.trans (Real.exp_le_exp.mpr ?_)
  rw [max_eq_right (zero_le_one.trans hx)]
  nlinarith [sq_nonneg (Real.log (Real.log x)),mul_nonneg (sq_nonneg (Real.log (Real.log x))) (zero_le_one.trans hx)]

private def Fees (V:Menu G)(K:KernelChoices)(j:ℕ)(t:ℝ):Prop:=
  ∀ k:Fin (j+1),∀ h:Fin (k.val+1),
    Real.exp ((width V K k.val h.val)⁻¹^2)≤t ∧
    V.bill K k.val h.val≤Beaming.spray t ∧ V.bill K k.val h.val≤t^Beaming.grain k.val

private theorem enough (V:Menu G)(K:KernelChoices)(j:ℕ):∀ᶠ t:ℝ in atTop,Fees V K j t:=by
  apply eventually_all.2
  intro k
  apply eventually_all.2
  intro h
  have rank:0<Beaming.grain k.val:=by unfold Beaming.grain; positivity
  exact (eventually_ge_atTop _).and ((spray _).and ((tendsto_rpow_atTop rank).eventually_ge_atTop _))

theorem prepaid (simple:G.Simple)(V:Menu G)(s:Sheet G)(price:MapPrices):
    WilsonFundedWindowMenu.Prepared (@Filed G V) s price:=by
  intro C E flags programs wages baton
  let K:=s.kernel
  refine ⟨V.threshold K,?_⟩
  intro l hl D w u Z post scouts pocket θ stages P menu bank quarter
  obtain ⟨raised,other,_,pay⟩:=delay_extra bank (Fees V K) (fun _ _ _=>True)
    (enough V K) (fun _ _=>Eventually.of_forall fun _=>trivial)
  refine ⟨raised,other,?_⟩
  intro Y hY bar wait priced B archive origins rank
  dsimp only
  intro η q exchange aux rider booth sheltered works divides
  constructor
  · intro j
    rw [B.valid.lengths]
    exact (hl j).trans (D.large j).need
  · intro i H hi
    let k:Fin (B.a.clock.J (i+1)+1):=⟨B.a.clock.J i,Nat.lt_succ_of_le (B.a.fits.mono (Nat.le_succ i))⟩
    let h:Fin (k.val+1):=⟨H,Nat.lt_succ_of_le hi⟩
    have now:=(pay Y hY).1 _ _ (B.valid.pays i) k h
    have later:=(pay Y hY).1 _ _ ((B.valid.pays i).trans (Push.Corrected.Last.band_le B.a simple (Nat.le_succ i))) k h
    exact ⟨now.1,le_min later.2.1 later.2.2⟩

theorem on_run (V:Menu G)(R:Run G)(paid:Filed V R.kit)(i H:ℕ)(fit:H≤R.alloy.B.a.clock.J i):
    let σ:=width V R.metals.p.kernel (R.alloy.B.a.clock.J i) H
    0<σ ∧ σ≤1 ∧ σ≤V.cap R.metals.p.kernel (R.alloy.B.a.clock.J i) H ∧
    Real.exp (σ⁻¹^2)≤R.alloy.B.a.clock.hatBeta i ∧
    V.bill R.metals.p.kernel (R.alloy.B.a.clock.J i) H≤budgetR R i:=by
  exact ⟨width_pos ..,min_le_left ..,min_le_right ..,(paid.2 i H fit).1,(paid.2 i H fit).2⟩

end YM.Integration.WilsonOriginalSmallStrip
