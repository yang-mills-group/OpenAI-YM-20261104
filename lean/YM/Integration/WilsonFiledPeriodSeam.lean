import YM.Integration.WilsonIndependentVacuumDirection
import YM.Integration.WilsonVacuumPreResetDatedDeposit
import YM.Integration.FundedMarkedCoverRows

set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonFiledPeriodSeam
open Function Filter Gauge Pressure Precision Tree Stationary
open Primitives.TwoWave Primitives.TwoWave.RealSlice
open AllOrder AllOrder.Ker AllOrder.Haiku AllOrder.Floe.Step
open WilsonCoeffUV.Bank.Mosaic PertExtension.Series PowerSeries
open Finset Lattice RG WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Mer
open WilsonCoeffUV.Blue WilsonCoeffUV.Cosmos WilsonCoeffUV.Bank.Realm WilsonCoeffUV.Winding
open Next.Foundations PhysicalNext.Repeat.Legato ActualRunAdmissionScales
open WilsonVacuumPreResetFiniteHeatCourse WilsonVacuumPreResetDatedDeposit WilsonVacuumPreResetTorusDeposit
open WilsonVacuumPreResetTorusGrade WilsonCoeffUV.Wheel WilsonCoeffUV.Soil WilsonCoeffUV.Bank.Ticket
open AllOrder.Floe AllOrder.Ker Primitives.TwoWave.RealSlice
open scoped BigOperators Classical
variable {G:Gauge}

/-- One before-period forecast pays the true finite pre-reset seam at every
positive angular rank contributing to the submitted coupling coefficient. -/
theorem enrolled (G:Gauge)(i:ℕ):∃v:ℕ→Gear G→ℝ,∃D:ℕ,∀(R:Run G) (_simple:G.Simple)
    (_reading:RG05Preconstruction.ReadoutPurchase R.b),FundedMarkedCoverRows.prices v R.kit→
    ∀ᶠj:ℕ in atTop,∀N p,j<N→∀ r < i+2,∀x,
      |RootedVacuumWinding.ground R.family.path.levels R.metals.O N j (R.family.side j p) i r x|≤
      (admittedCost R.family.path.levels j)^D*Real.exp (-((R.family.side j p).val:ℝ)/(4*zz R.family.path.levels j)):=by
  classical
  choose f d grant using (fun r:Fin (i+2)=>WilsonVacuumPreResetFiniteHeatCourse.fresh
    G i i (r:ℕ) le_rfl)
  let v:ℕ→Gear G→ℝ:=fun k g=>∑r,|f r k g|
  refine ⟨v,∑r,d r,?_⟩
  intro R simple reading paid
  have dates:∀ᶠj:ℕ in atTop,∀r:Fin (i+2),_:=
    (Filter.eventually_all).mpr fun r=>grant r R simple reading
  filter_upwards [dates,FundedMarkedCoverRows.realm R simple v paid 0 (fun _=>0) (fun _=>1)
    (fun _=>by decide) i 0 0] with j banks realm
  obtain ⟨Q,draws,coupling,clock,anchor,_,_,_,budget⟩:=realm
  have hj:Q.anchor≤j:=anchor.le
  obtain ⟨_,_,cash⟩:=budget j le_rfl hj
  intro N p later r hr x
  let s:Fin (i+2):=⟨r,hr⟩
  have hs:f s (R.family.path.levels.clock.J (j+1)) (Q.mint j hj).gear≤Q.cash Credit.leanC j:=
    ((le_abs_self _).trans (Finset.single_le_sum (fun b _=>abs_nonneg (f b _ _))
      (Finset.mem_univ s))).trans cash
  have h:=(banks s) Q hj draws coupling clock hs N p later x
  rw [clock] at h
  exact h.trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (admittedCost_one R.family.path.levels j)
    (Finset.single_le_sum (fun b _=>Nat.zero_le (d b)) (Finset.mem_univ s))) (Real.exp_nonneg _))

def filed (R:Run G)(N j:ℕ)(n:Side)(Z:SeriesA G)
    (i cap:ℕ)(x:Woods G n→ℝ):ℝ:=
  Pace.grouping (Tested.term (pitch R.family.path.levels R.metals.O N j-1))
    (bank Z) (Step.tape cap) (R.family.path.levels.params j).clip (R.alloy.B.kin.path N j) i n x

def Angular (R:Run G)(i D j:ℕ):Prop:=
    ∀N p,j<N→∀ r < i+2,∀x,
      |RootedVacuumWinding.ground R.family.path.levels R.metals.O N j (R.family.side j p) i r x|≤
      (admittedCost R.family.path.levels j)^D*Real.exp (-((R.family.side j p).val:ℝ)/(4*zz R.family.path.levels j))

def Direction (R:Run G)(i D j:ℕ):Prop:=
    ∀N p,j<N→∀e Z σ C,Issued R N j e Z σ C→i≤e+2→
    let n:=R.family.side j p
    ∀x y:Woods G n→ℝ,∀w:ℝ,1≤w→(∀u,|x u|≤w)→(∀u,|y u|≤w)→
    |(evaluated (coil0 R.family.path.levels R.metals.O j N n) i x-evaluated (coil0 R.family.path.levels R.metals.O j N n) i y)-
      (filed R N j n Z i (e+2) x-filed R N j n Z i (e+2) y)|≤
      2*((i+2:ℕ):ℝ)*((1+(Fintype.card (Woods G n):ℝ))*w)^(i+2)*
        ((admittedCost R.family.path.levels j)^D*Real.exp (-(n.val:ℝ)/(4*zz R.family.path.levels j))) 

theorem at_date (R:Run G)(i D j:ℕ)(simple:G.Simple)(prices:Angular R i D j):
    Direction R i D j:=by
  intro N p later e Z σ C income hi n x y w w1 cx cy
  let base:=front (R.alloy.B.kin.path N j) (R.family.path.levels.params j).clip n+sands Z n
  let a:=pitch R.family.path.levels R.metals.O N j
  let H:=Blue.mix (pace a) base
  let F:=coil0 R.family.path.levels R.metals.O j N n
  have hf:shellK 2 F:=winter_band _ _ _ _ _ (RunFormalChain.fromRun R).receipt
    (emera_far R.family.path.levels simple (RunFormalChain.fromRun R).receipt (Nat.succ_le_of_lt later) _).1
  have hh:shellK 2 H:=mix_length (WilsonLimitConstruction.FundedSpringPeriodGerm.grade n
    (R.family.path.levels.params j).clip (R.alloy.B.kin.path N j) Z)
  have hfresh(r:ℕ):H i (r+1)=lagoon (freshet R.family.path.levels R.metals.O N j i (r+1)) n:=
    WilsonLimitConstruction.FundedSpringPeriodRows.regraded R simple N j later n base i r
      (fun t ht=>income.periodic t (by omega) n r)
  have level(r)(hr:r < i+2)(u):|F i (r+1) u-H i (r+1) u|≤(admittedCost R.family.path.levels j)^D*Real.exp (-(n.val:ℝ)/(4*zz R.family.path.levels j)):=by
    rw [hfresh,abs_sub_comm]
    exact prices N p later r hr u
  have entered(z:Woods G n→ℝ):filed R N j n Z i (e+2) z=evaluated H i z:=
    WilsonVacuumPreResetTorusRegradedAction.original (K:=R.alloy.B.kin.path N j) (B:=(R.family.path.levels.params j).clip)
      (cap:=e+2) (t:=i) (p:=a) (Bank.angle_tilt (A:=R.family.path.levels) simple (RunFormalChain.fromRun R).receipt later)
      Z income.positive income.purchase income.lower hi z
  rw [entered,entered]
  exact WilsonIndependentVacuumDirection.difference i F H hf hh (mul_nonneg (pow_nonneg (zero_le_one.trans (admittedCost_one R.family.path.levels j)) D) (Real.exp_nonneg _)) w1 x y cx cy level

/-- Field-dependent value of the original finite quiet output on two directions,
compared to the complete elected lower action in its own kinetic units. -/
theorem original (G:Gauge)(i:ℕ):∃v:ℕ→Gear G→ℝ,∃D:ℕ,∀(R:Run G)(_simple:G.Simple)
    (_reading:RG05Preconstruction.ReadoutPurchase R.b),FundedMarkedCoverRows.prices v R.kit→
    ∀ᶠj:ℕ in atTop,∀N p,j<N→∀e Z σ C,Issued R N j e Z σ C→i≤e+2→
    let n:=R.family.side j p
    ∀x y:Woods G n→ℝ,∀w:ℝ,1≤w→(∀u,|x u|≤w)→(∀u,|y u|≤w)→
    |(evaluated (coil0 R.family.path.levels R.metals.O j N n) i x-evaluated (coil0 R.family.path.levels R.metals.O j N n) i y)-
      (filed R N j n Z i (e+2) x-filed R N j n Z i (e+2) y)|≤
      2*((i+2:ℕ):ℝ)*((1+(Fintype.card (Woods G n):ℝ))*w)^(i+2)*
        ((admittedCost R.family.path.levels j)^D*Real.exp (-(n.val:ℝ)/(4*zz R.family.path.levels j))) :=by
  obtain ⟨v,D,quote⟩:=enrolled G i
  refine ⟨v,D,?_⟩
  intro R simple reading paid
  filter_upwards [quote R simple reading paid] with j prices
  exact at_date R i D j simple prices

end YM.Integration.WilsonFiledPeriodSeam
end
