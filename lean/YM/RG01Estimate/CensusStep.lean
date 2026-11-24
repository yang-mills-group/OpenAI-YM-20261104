import YM.RG01Estimate.StepRate
import YM.RG01Estimate.VacuumPrices
import YM.RG01Estimate.VacuumListing
import YM.UVExtension.Dales.Pry

/-!
# Vacuum log truncation by (absolute) cluster radius

Uniform in cutoff N and period index, on the *single* purchased calendar of the UV
construction. All derivatives at the actual varying BudgetPoint. Holds on true torus
geometry. Includes arbitrary-winding and seed overlaps in these components. Export the
+3/+1 reserves before last reformatting. This is a truncation by incidence/overlap/depth.
It is not the formal Fk comparison yet (the retained low-degree labels are not Fk
coefficients). The catalogue and fates of those labels are fixed on the full exact density;
use before any further reformatting -- don't reuse it on unaligned differences.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG01Estimate.CensusStep

open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Control Window Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Extra.Iteration
open PriceCompiler Org Input Supply Pressure.Testing Time
open PhysicalNext PhysicalNext.Repeat Roost Opera
open Repeat.Height Beam Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} (hG : G.Simple)
variable {M : Metals G} {D : Rolls M.p} {A : Alloy M D} (R : Factor A)

local notation "T" => A.B.a
local notation "ham" => A.B.kin.alpha
-- hG here only for the eventual strength claims (Schedule ratio).

/-- Keep the two-tree price, rather than rebudgeting K solely on the path after reset. -/
def hardCost (m : ℕ) :=
    let J := A.B.a.clock.J (m+1)
    let i := A.B.a.clock.J m
    Cash.armK (R.target J i) (D.L J) (R.shape.μ J i) (A.B.a.clock.hatBeta m) 0 (R.expense J i).degrees

variable (m : ℕ)
lemma hardCost_allowance : hardCost R m ≤ A.B.a.clock.forcedAllowance m := by
  -- apply with calendar hat coupling -- hardCost itself does not refer to the incoming actual Rep beta
  -- backing statement wants in-band; prove directly from the receiving gate.
  let β := A.B.a.clock.hatBeta (m+1)
  have hp : β∈ Shoot.band T (m+1) := by
    have hr : 1<β:=A.B.a.fits.delayed _
    refine ⟨?_,?_⟩
    · change β/2 ≤ β; linarith
    change β ≤ 2*β; linarith
  let j:= A.B.a.clock.J (m+1)
  let i:= A.B.a.clock.J m
  let y:= betaF G (A.B.a.clock.hatBeta m) (D.L j)
  have heq : β=y:= PriceCompiler.beta_eq A.B.valid m
  have h := R.pledging.conducts.income.earns j i (step_paid T m) (A.B.a.clock.hatBeta m) (A.B.valid.pays m) β
    (show inBand y β from heq ▸ trial_in hp)
  have hx:=VacuumPrices.forecast_allowance R (Nat.lt_succ_self m) hp
  change hardCost R m ≤ (1/8:ℝ)* (R.scout j i).pair.strong y β at h
  rw [← heq] at h
  have hm: (1/8:ℝ)* Time.forecastK T m R.scout β ≤ A.B.a.clock.forcedAllowance m :=
    (mul_le_mul_of_nonneg_left hx (by norm_num)).trans
      (mul_le_of_le_one_left (StepRate.step_nonneg T m).le (by norm_num))
  exact h.trans hm

include hG in
/-- Arbitrary-order payment for seeds, even with the moving support, derivative and
expense parameters. The early authorization with hard-coverage reserve pays it. -/
lemma enough_seed (p : ℕ) : ∀ᶠ m in atTop,
    let j:= A.B.a.clock.J (m+1)
    let i:= A.B.a.clock.J m
    let x:= A.B.a.clock.hatBeta m
    grow G (D.L j) x^p ≤ Real.exp ((R.target j i).mark (D.L j) (R.shape.μ j i) x) := by
  filter_upwards [StepRate.exponent_pays T hG p] with m hm
  intro j i x
  let y:=A.B.a.clock.hatBeta (m+1)
  let Q:=R.target j i
  have h : y = betaF G x (D.L j):= PriceCompiler.beta_eq A.B.valid m
  have hp:= hardCost_allowance R m
  refine hm _ h _ (le_trans ?_ hp)
  apply VacuumPrices.buys_seed (L:=D.L j) Q _ x _ _
  · rw [← h]; exact (A.B.a.fits.delayed _).le
  change (Real.sqrt y)⁻¹ ≤ _
  rw [h]

-- short names stable from Roost coordinate plans.
variable {m N n : ℕ} {I U : RG.Rep G (A.B.a.S.side (m+1) n)}
variable (H : Opera.Guide A.B R.shape N m n I) (J : Opera.Guide A.B R.shape N m n U)
   (X : Alliance H J 1 0) (r : ℕ)

/-- Kept components have only finitely many overlapping vertices at a time. -/
def length (r : ℕ) := 3 + 2*(r+1)

def lit (z : H.fragrances) := VacuumCensus.tail J (length r) (X.furrow z)

local notation "p" => A.B.a.budget m
abbrev ledger := Beam.marquee H p
abbrev vacuum := Song.plusone H X Chi.canonical (A.B.kin.alpha N m)
abbrev discarded := Height.serve H X Chi.canonical (lit R H J X r)
abbrev kept := Height.sleeping H X Chi.canonical (lit R H J X r) (A.B.kin.alpha N m)

private lemma pays_radius (hh : m < N) (hs : grow G (D.L (A.B.a.clock.J (m+1))) (A.B.a.clock.hatBeta m) ^ length r ≤
       Real.exp ((R.target (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)).mark (D.L (A.B.a.clock.J (m+1)))
       (R.shape.μ (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)) (A.B.a.clock.hatBeta m)))
    (hβ : U.beta ∈ Shoot.band T (m+1)) (he : Opera.Price A.B R.shape N m n U J) :
    Collection.Local (ledger R H) (A.B.a.budget m) (discarded R H J X r) ((2 * (Real.sqrt U.beta)⁻¹)^(r+1))
      (hardCost R m) := by
  let x := A.B.a.clock.hatBeta m
  let C := A.B.a.clock.J m
  let u := A.B.a.clock.J (m+1)
  let K := M.p.profile C
  let d := grow G (D.L u) x
  let hi : StepStages u C := step_paid T m
  have hk := A.B.valid.pays m
  have hz:= R.pledging.jewels u x hk C hi
  let Tu:= ships A.B N m n
  obtain ⟨Y',d',v,t',Av,b',r',B,q',i',z,⟨N',hg'⟩,hC,h₂⟩:= hz.2 _ _ _ Tu J.laws.data.funds (protocol A.B hh R.pledging.conducts.full) _ J
  have hR : A.B.a.params m=K:= params_eq A.B.valid m
  have hΨ := R.pledging.peak.large u C hi x hk
  obtain ⟨hH,hKz,hV',hZ⟩:=hΨ; obtain ⟨he',hv',hv⟩:= hZ B i' z hC N'.balance h₂
  have hp : (A.B.a.budget m).power=K.power :=congr_arg RG.Stage.power hR
  have hj : (A.B.a.budget m).order=K.order :=congr_arg RG.Stage.order hR
  have h' : preExponent (A.B.a.budget m) ≤ (R.expense u C).earn := (show preExponent p = K.supportExponent+3 from
    congr_arg (fun s:RG.Stage=>s.supportExponent+3) hR).trans_le (R.pledging.agenda u C hi).1
  have hb:= VacuumListing.filtered H p Chi.canonical X N' rfl hj.le hp.le rfl h' _ he
    (VacuumCensus.charged N' he' hH hg' hV' hv' (length r) hs hz.1)
  refine VacuumListing.relax p hb ?_ (le_refl _)
  -- numerical conversion with no leftover stage cost
  let y := asset (R.expense u C)
  let g := (Real.sqrt U.beta)⁻¹
  let cst:=turnFee p
  let b:= collars G y x K.order K.power
  let f:= (d*salary (R.target u C) (D.L u) (R.shape.μ u C) B x K.order z*(1-1/2)⁻¹)
  change cst*((d^length r)⁻¹*(b*f)) ≤ _
  change (d^3)⁻¹*b*f ≤ heap G K (1/16) * δE x at hv
  have hA : 0 ≤ d := zero_le_one.trans hH
  have hB := Time.authorized G K
  have hy : cst*(heap G K (1/16)*δE x) ≤ 1 := by
    have hv: away K=cst:= by unfold away cst turnFee; rw [hp,hj]
    dsimp only [heap]
    rw [hv]
    calc
      _ = (1/16)*Time.credit G K * δE x := by field_simp [show cst ≠ 0 from (turnFee_pos p).ne']
      _ ≤ 1 := by
        have ht : 0 ≤ δE x := by
          unfold δE Clock.gap; exact Real.rpow_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) _
        have hi : δE x ≤ 1 := StepRate.allowance_le T m
        nlinarith only [hB.1, ht,hi]
  have hvv : (d^(2*(r+1)))⁻¹ ≤ (2*g)^(r+1) :=
    StepRate.length_power T (L:=D.L u) (PriceCompiler.beta_eq A.B.valid m) _ hβ
  calc
    _ = (d^(2*(r+1)))⁻¹*(cst*((d^3)⁻¹*b*f)) := by unfold length; rw [pow_add,mul_inv_rev]; ring
    _ ≤ _ := (mul_le_of_le_one_right (inv_nonneg.mpr (pow_nonneg hA _))
      ((mul_le_mul_of_nonneg_left hv (turnFee_pos _).le).trans hy)).trans hvv

lemma eharmony (hh : m < N) (he : Opera.Price A.B R.shape N m n U J) :
    ∀ O : Tree.Forest (A.B.a.clock.op m n).ratio,
    ∀ V, earlyValue (ledger R H) (A.B.kin.path N m) (A.B.a.params m).clip (A.B.a.budget m)
            (vacuum R H J X) U.beta (Song.weighty J Chi.canonical O) (ham N m) V =
      (A.B.a.clock.op m n).push U.beta U.eval V := by
  intro O V
  let x:=A.B.a.clock.J m
  let u:=A.B.a.clock.J (m+1)
  have hz:= R.pledging.jewels u (A.B.a.clock.hatBeta m) (A.B.valid.pays m) x (step_paid T m)
  obtain ⟨Y',d',v,t',Av,b',r',B,q',i',z,⟨N',_⟩,_,_⟩:= hz.2 _ _ _ _ J.laws.data.funds (protocol A.B hh R.pledging.conducts.full) _ J
  have hR := params_eq A.B.valid m
  have hj : (A.B.a.budget m).order=(M.p.profile x).order :=congr_arg RG.Stage.order hR
  exact (Beam.travels H p _ _ _ _ V).trans (Song.forward p H X Chi.canonical _ N' O rfl hj.le
    («T»:=ships A.B N m n) (A.B.support.cap N m hh.le) he V)

lemma still_full (hh : m < N) (he : Opera.Price A.B R.shape N m n U J) (hd : WilsonStartup.Decent (A.B.a.params m).clip (A.B.a.budget m)) :
    Collection.Local (ledger R H) p (vacuum R H J X)
      (Opera.earlyFee («p»:=R.expense) A.B N m U.beta) (hardCost R m) := by
  let x := A.B.a.clock.hatBeta m
  let C := A.B.a.clock.J m
  let u := A.B.a.clock.J (m+1)
  let K := M.p.profile C
  let hi : StepStages u C := step_paid T m
  have hk := A.B.valid.pays m
  have hz:= R.pledging.jewels u x hk C hi
  let Tu:= ships A.B N m n
  obtain ⟨Y',d',v,t',Av,b',r',B,q',i',z,⟨N',hg'⟩,hC,h₂⟩:= hz.2 _ _ _ Tu J.laws.data.funds (protocol A.B hh R.pledging.conducts.full) _ J
  have hR : A.B.a.params m=K:= params_eq A.B.valid m
  have hp : (A.B.a.budget m).power=K.power :=congr_arg RG.Stage.power hR
  have hj : (A.B.a.budget m).order=K.order :=congr_arg RG.Stage.order hR
  have h' : preExponent p ≤ (R.expense u C).earn := (show preExponent p = K.supportExponent+3 from
    congr_arg (fun s:RG.Stage=>s.supportExponent+3) hR).trans_le (R.pledging.agenda u C hi).1
  have hσ : preExponent p/ ((p).B:ℝ) ≤ (A.B.a.params m).width/2 := by
    change ((A.B.a.params m).supportExponent+3)/radiusB x ≤ _; rw [hR]; exact R.pledging.range u x hk C hi
  have ha: Tu.down.Bounds Tu.low (A.B.a.params m).width (A.B.a.params m).paths (A.B.a.clock.loopCap m) := A.B.support.cap N m hh.le
  have hb:= VacuumListing.full H p Chi.canonical X N' rfl hj.le hp.le rfl h' he hC (ham N m) ha hd hσ
  exact VacuumListing.relax p hb (mul_le_mul_of_nonneg_left (add_le_add_left h₂ _) (turnFee_pos _).le) (le_refl _)


/-- The full log ledger (prior to extracting scalar/affine pricing) exactly evaluated,
and its simultaneous decomposition. The kept part is *not* a truncated polynomial in g.
There are still low-degree components with nonanalytic profiles; this theorem leaves them
and quantifies which tail was controlled. -/
structure Account : Prop where
  fullSize : Collection.Local (ledger R H) p (vacuum R H J X)
      (Opera.earlyFee («p»:=R.expense) A.B N m U.beta) (hardCost R m)
  low : Collection.Local (ledger R H) p (kept R H J X r)
      (Opera.earlyFee («p»:=R.expense) A.B N m U.beta) (hardCost R m)
  high : Collection.Local (ledger R H) p (discarded R H J X r)
      ((2*(Real.sqrt U.beta)⁻¹)^(r+1)) (hardCost R m)
  reserve : hardCost R m ≤ Real.sqrt (A.B.a.clock.forcedAllowance m) * ((2*(Real.sqrt U.beta)⁻¹)^(r+1))
  recorded : (vacuum R H J X).logRead = (kept R H J X r).logRead + (discarded R H J X r).logRead
  integral (O : Tree.Forest (A.B.a.clock.op m n).ratio) (V) :
    (A.B.a.clock.op m n).push U.beta U.eval V =
      earlyValue (ledger R H) (A.B.kin.path N m) (A.B.a.params m).clip p (vacuum R H J X)
        U.beta (Song.weighty J Chi.canonical O) (ham N m) V
  assembled (O : Tree.Forest (A.B.a.clock.op m n).ratio) (V) :
    earlyValue (ledger R H) (A.B.kin.path N m) (A.B.a.params m).clip p (vacuum R H J X)
        U.beta (Song.weighty J Chi.canonical O) (ham N m) V =
      earlyValue (ledger R H) (A.B.kin.path N m) (A.B.a.params m).clip p (kept R H J X r)
        U.beta (Song.weighty J Chi.canonical O) (ham N m) V *
        Real.exp (-((ledger R H).read (discarded R H J X r)).additive p V)

include R in
lemma decent (hh : m < N) : WilsonStartup.Decent (A.B.a.params m).clip (A.B.a.budget m) := by
  let a:= A.B.a; let x:=a.clock.J m; let y:=a.clock.J (m+1)
  have hr : a.params m=M.p.profile x:= params_eq A.B.valid m
  have hp := (A.B.support.cap N m hh.le).metric
  have hc : a.clock.threshold m= Instrument.plain.t (a.clock.hatBeta m):= (Deployment.clock_eqns a.clock m).2.2.2.2.2.2
  have ht := R.machine.shops y (a.clock.hatBeta m) (A.B.valid.pays m) x (step_paid a m)
  have hP : Time.Same (a.params m) p:= ⟨rfl,rfl,rfl⟩
  have hu := (ht p (hr ▸ hP) rfl hc).1
  rw [← hr] at hu
  exact hu (Canonical.direct_le_one hp)

include hG in
theorem cluster_tail : ∀ᶠ m in atTop, ∀ (N n : ℕ), m < N →
    ∀ (I U : RG.Rep G (A.B.a.S.side (m+1) n)) (H : Guide A.B R.shape N m n I)
      (J : Guide A.B R.shape N m n U) (X : Alliance H J 1 0), Opera.Price A.B R.shape N m n U J →
      U.beta ∈ Shoot.band T (m+1) → Account R H J X r := by
  filter_upwards [enough_seed hG R (length r), StepRate.threshold_fine_divisor T hG (r+1)] with m hm hp N n hN I U H J X he hβ
  have hr := pays_radius R H J X r hN hm hβ he
  have hz := still_full R H J X hN he (decent R hN)
  have hv : Collection.Local (ledger R H) (A.B.a.budget m) (kept R H J X r) _ _ := VacuumListing.unfiltered H (A.B.a.budget m) Chi.canonical X (lit R H J X r) hz
  have h := VacuumListing.filter_identity H Chi.canonical X (VacuumCensus.tail J (length r)) (ham N m)
  exact ⟨hz,hv,hr,(hardCost_allowance R m).trans (hp _ hβ),h, fun O V=> (eharmony R H J X hN he O V).symm,
    fun O V=> VacuumListing.reassemble (A.B.a.budget m) hv hr h rfl _ _ _ _ V⟩

end YM.RG01Estimate.CensusStep
