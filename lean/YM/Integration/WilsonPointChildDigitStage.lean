import YM.Integration.WilsonPointChildFiniteTier
import YM.Integration.WilsonPointChildFiniteRestamp
import YM.Integration.WilsonPointChildWindingIncome
import YM.Integration.WilsonMarkedIndependentNormalizedStep
import YM.Integration.WilsonPointChildDigitTier
import YM.Integration.WilsonPointChildDigitIncome
import YM.Integration.WilsonPointChildDigitRoot
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPointChildDigitStage
open Filter Function Finset YM FormalBulk08 Lattice RG Laurent Next.Foundations PhysicalNext.Repeat.Legato
open Reef Flat Stationary Dawn Pose Kemp Palm Shore Mesa Wine Quire Roof Lotus Sierra Gorge Dove Rial Rift Lava
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Blue WilsonCoeffUV.Wheel
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider WilsonCoeffUV.Embroider.Canvas
open WilsonPointChildTestCoordinates WilsonNeutralPointCourse WilsonPointChildCoverStep WilsonPointChildFiledPress
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open scoped ContDiff BigOperators Topology Classical ENNReal
open Function Filter Finset Matrix Lattice Wilson RG Laurent PowerSeries Work.F08
open FormalBulk08 Flat Reef Jets Orb Wick Stationary Series Shore Gorge Lotus Mesa Rift Lava Dawn Kemp Roof Sierra Rial
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Blue WilsonCoeffUV.Power
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer WilsonCoeffUV.Soil WilsonCoeffUV.Winding
open YM Next.Foundations PhysicalNext.Repeat.Legato Pose Palm Quire Wine Dove WilsonCoeffUV.Embroider
open WilsonPointChildTestCoordinates WilsonNeutralPointCourse WilsonPointChildCoverStep
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open scoped Classical Topology BigOperators ContDiff
open WilsonCoeffUV.Bank.Carp WilsonPointChildDigitLedger
open WilsonPointChildCoveredRead (directions)
open Function Filter Finset Lattice RG Wilson Laurent Precision PowerSeries
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos WilsonCoeffUV.Blue
open WilsonCoeffUV.Mer WilsonCoeffUV.Soil WilsonCoeffUV.Bank.Realm WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Winding WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Bank.Ticket
open WilsonVacuumPreResetFiniteHeatFinance (gross)
open WilsonVacuumPreResetFiniteHeatTable (table)
open WilsonMarkedIndependentNormalizedWallet (gap)
open WilsonMarkedIndependentNormalizedScale (rate)
open Next.Foundations PhysicalNext.Repeat.Legato
open scoped Classical BigOperators Topology
open Borough
open WilsonPointChildFiledSalary (inverseCost)
open WilsonPointChildFiniteRestamp (difference)
open WilsonPointChildCoverStep (routes)
open WilsonVacuumPreResetFiniteHeatFinance (gross)
open WilsonVacuumPreResetFiniteHeatTable (table)
open WilsonMarkedIndependentNormalizedScale (rate)
open WilsonCoeffUV.Bank.Carp
variable {G:Gauge}{d D:ℕ}

def Gap (R:Run G)(u:G.ColorIndex)(h:d<D)(digit:∀i,Site (R.family.S.block i))(N j per E:ℕ)(C:ℝ):Prop:=
  ∀v:Letter (R.family.labels.level d),∀p:Scroll D,∀i ≤ E,∀r x,
    |difference (ledger R u h digit N (N-j) j v p) (R.family.side j per) i r x| ≤ 
      (1+‖physical p‖)*C

private theorem entered (R:Run G){e:ℕ}{E:Credit}(Q:Realm G e E)(same:Q.draws=R.family.path.levels)
    (j:ℕ)(paying:R.family.path.levels.clock.J (j+1) ≤ (R.family.path.levels.S.block j).val)(h:Q.anchor ≤ j):
    WilsonPointChildQuoteWidth.quote (Q.mint j h).gear ≤ WilsonPointChildFiledPress.width R (j+1):=by
  let I:=(Q.mint j h).gear
  have kernel:I.kernel=R.family.path.levels.clock.kernel:=congrArg (fun A=>Levels.clock A |>.kernel) same
  have L:I.patch.L=R.family.S.block j:=congrArg (fun A=>(loose A j).L) same
  unfold WilsonPointChildQuoteWidth.quote
  have use:=Finset.inf'_le ((windowBasis G I.kernel).width)
    (show R.family.path.levels.clock.J (j+1)∈Finset.range (I.patch.L.val+1) from Finset.mem_range.mpr (by rw [L];exact Nat.lt_succ_of_le paying))
  exact use.trans_eq (congrArg (fun K=>(windowBasis G K).width (R.family.path.levels.clock.J (j+1))) kernel)

private theorem collect {B c t target U eng:ℝ}{w d k:ℕ}(b:0≤B)(ch:0≤c)(th:0≤t)
    (inv:U≤B^(w+1))(column:|eng|≤B^d)(upper:B^(w+1+d+(k+2))*t≤target):
    U*(|eng| *(B^(k+2)*(c*t)))≤c*target:=by
  calc _ ≤ B^(w+1)*(B^d*(B^(k+2)*(c*t))):=
           mul_le_mul inv (mul_le_mul_of_nonneg_right column (by positivity)) (by positivity) (by positivity)
       _=c*(B^(w+1+d+(k+2))*t):=by rw [pow_add,pow_add];ring
       _ ≤ _:=mul_le_mul_of_nonneg_left upper ch

theorem original (G:Gauge)(E d:ℕ):∃v:Gear G → ℝ,∀(R:Run G)(_simple:G.Simple)
    (_file:WilsonPointChildFiledTest.Filed R)(u:G.ColorIndex){D:ℕ}(depth:d<D)(o:Loc G 1)
    (price:ℕ → Gear G → ℝ)(_funded:FundedMarkedCoverRows.prices price R.kit)
    (_tags:∀i n,(Flat.primary (R.family.path.levels.clock.op i 0).patch R.family.path.levels.clock.kernel n).Choices),
    WilsonPointChildWidthHistory.Income R (routes R) u depth o E → 
    ∀ᶠj:ℕ in atTop,∀(Q:Realm G (E+1) Credit.leanC)(a:Q.anchor ≤ j),
    Q.draws=R.family.path.levels → Q.paid=R.metals.O → Q.y=zz R.family.path.levels → 
    v (Q.mint j a).gear ≤ Q.cash Credit.leanC j → ∀(digit:∀i,Site (R.family.S.block i))(N per:ℕ),j<N → 
    table R.family.path.levels R.metals.O E N (j+1) (R.family.side (j+1) per)
      (WilsonVacuumPreResetFiniteHeatScale.rate R.family.path.levels (j+1) per) → 
    Gap R u depth digit N (j+1) per E (rate R.family.path.levels (j+1) per) → 
    Gap R u depth digit N j per E (rate R.family.path.levels j per):=by
  obtain ⟨v,k,earned⟩:=WilsonPointChildDigitTier.original G E d
  refine ⟨v,?_⟩
  intro R simple file u D depth o price funded tags item
  let A:=R.family.path.levels
  let F:=R.family.labels.level d
  obtain ⟨M,w,M1,matrix⟩:=item
  obtain ⟨k₁,card⟩:=eventually_atTop.1 (OriginalPeriodWindingPrice.period_power A 1)
  obtain ⟨k₂,row⟩:=eventually_atTop.1 (WilsonPointChildDigitIncome.original R simple file u depth o tags price funded E (show 0<(1:ℝ) by norm_num))
  let total:=w+1+d+(k+2)
  filter_upwards [eventually_ge_atTop (max k₁ k₂),matrix,(WardBin.bell A simple).eventually_ge_atTop M,
    WilsonPointChildQuoteWidth.index A,WilsonVacuumPreResetFiniteHeatScale.clock A simple,
    WilsonMarkedIndependentNormalizedScale.original A simple total] with j ready inverse big fitted clock scale
  intro Q a level scheme stated wallet digit N per live quiet incoming v₀ p i hi r x
  let n:=R.family.side j per
  let f:=R.family.side (j+1) per
  let P:=loose A j
  let y:=Q.y j
  let B:=gross y f
  let τ:=rate A (j+1) per
  let tail:=Real.exp (-(n.val:ℝ)/(512*y))
  let κ:=1+‖physical p‖
  let child:=growWord P (digit j) D p
  let old(s:Letter F):=ledger R u depth digit N (N-(j+1)) (j+1) s child
  let X(s:Letter F):=shifted (old s) (lift (digit j))
  let T:=WilsonNeutralPointCourse.transfer R (routes R) u depth digit N j
  let μ:=(P.L.val:ℝ)^d
  have side:f=n*P.L:=Subtype.ext (A.clock.op j per).sizes
  have same:f=n*(loose Q.draws j).L:=by rw [level];exact side
  have yn:1 ≤ y:=Q.depth j a
  have fn:(1:ℝ) ≤ f.val:=by exact_mod_cast f.pos
  have fb:1+(f.val:ℝ) ≤ B:=calc
    _=(1+(f.val:ℝ))^1:=(pow_one _).symm
    _ ≤ (1+(f.val:ℝ))^4:=pow_le_pow_right₀ (by linarith) (by decide)
    _ ≤ _:=le_mul_of_one_le_left (by positivity) yn
  have B2:2 ≤ B:=by linarith
  have B1:1 ≤ B:=by linarith
  have narrow:WilsonPointChildQuoteWidth.quote (Q.mint j a).gear ≤ WilsonPointChildFiledPress.width R (j+1):=
    entered R Q level j fitted a
  have tpos:0<τ:=Real.exp_pos _
  have w0:0<zz A (j+1):=clock.2.1
  have ts:τ ≤ 1:=by apply Real.exp_le_one_iff.mpr;exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg _)) (by positivity)
  have tq:WilsonVacuumPreResetFiniteHeatScale.rate A (j+1) per ≤ τ:=by
    apply Real.exp_le_exp.mpr
    change -(f.val:ℝ)/(16*zz A (j+1)) ≤  -(f.val:ℝ)/(4096*zz A (j+1))
    apply (le_div_iff₀ (by positivity:0<4096*zz A (j+1))).2
    field_simp [w0.ne'];linarith
  have bank:table Q.draws Q.paid E N (j+1) (n*(loose Q.draws j).L) τ:=by
    rw [←same,level,scheme];exact fun b hb h w=>(quiet b hb h w).trans tq
  have bpay:A.clock.hatBeta (j+1) ≤ f.val:=by simpa using card (j+1) (by omega) per
  have curr:A.clock.hatBeta j ≤ n.val:=by simpa using card j (by omega) per
  have nf:(n.val:ℝ) ≤ f.val:=by rw [side];exact_mod_cast Nat.le_mul_of_pos_right _ P.L.pos
  have nice:‖physical child‖ ≤ ‖physical p‖:=by
    have large:2 ≤ P.L.val:=by have h:=A.S.block_large j;change 2 ≤ (A.S.block j).val;omega
    rw [←WilsonPointChildCoverStep.pulled P (digit j) large p]
    exact Dawn.through_le (digit j) large _
  have kp:0<κ:=by dsimp [κ];positivity
  have hit:∀s:Letter F,Auth d (old s) ∧ ∀b ≤ E,∀t,
    Wig terrain (fun _:Unit=>0) (WilsonPointChildFiledPress.width R (j+1))
      ((A.clock.hatBeta (j+1))*‖physical child‖) {()} ((old s).2 b t) ∧
    ∀t' w,|plume ((old s).2 b t) t' w| ≤ (A.clock.hatBeta (j+1))*‖physical child‖:=by
    intro s
    simpa only [Real.rpow_one] using row (j+1) (by omega) N (by omega) digit s child
  have unew:(A.clock.hatBeta (j+1))*‖physical child‖ ≤ B*κ:=
    mul_le_mul (by linarith) (nice.trans (le_add_of_nonneg_left zero_le_one)) (norm_nonneg _) (by linarith)
  let S(s:Letter F):=verseI A R.metals.O j N d (X s)
  have shot(s:Letter F)(b:ℕ)(hb:b ≤ i):|difference (S s) n b r x| ≤ B^(k+2)*(κ*(τ+tail)):=by
    let eqL: (loose A j).L=(loose Q.draws j).L:=congrArg (fun V=>(loose V j).L) level.symm
    let z:Site (loose Q.draws j).L:=eqL ▸ digit j
    have rz:lift z=lift (digit j):=by
      have general {a c:Side}(h:a=c)(w:Site a):lift (h ▸ w)=lift w:=by subst c;rfl
      exact general eqL _
    have root(g:ℕ)(hg:g≤E)(l:ℕ):Wig terrain (fun _:Unit=>lift (digit j)) (WilsonPointChildFiledPress.width R (j+1))
        ((A.clock.hatBeta (j+1))*‖physical child‖) {()} ((X s).2 g l) ∧
      (∀t',|plume ((X s).2 g l) f t'|≤(A.clock.hatBeta (j+1))*‖physical child‖) ∧
      ∀t',|(X s).1 f g l t'-plume ((X s).2 g l) f t'|≤κ*τ:=by
      apply WilsonPointChildDigitRoot.priced (old s) (lift (digit j)) f g l ((Primer.FamilyWindow R.family).pos _)
        ((hit s).2 g hg l).1 (((hit s).2 g hg l).2 f)
      intro t'
      exact (incoming s child g hg l t').trans (mul_le_mul_of_nonneg_right (add_le_add (le_refl 1) nice) tpos.le)
    have previous:∀g ≤ E,∀l y',|(X s).1 (n*(loose Q.draws j).L) g l y'-plume ((X s).2 g l) (n*(loose Q.draws j).L) y'| ≤ κ*τ:=by
      rw [←same];exact fun g hg l=>(root g hg l).2.2
    have hi₀:∀g ≤ E,∀l y',|plume ((X s).2 g l) (n*(loose Q.draws j).L) y'| ≤ B*κ:=by
      rw [←same];exact fun g hg l y'=>((root g hg l).2.1 y').trans unew
    have support:∀g ≤ E,∀l,Wig terrain (fun _:Unit=>lift z) (WilsonPointChildQuoteWidth.quote (Q.mint j a).gear)
        (B*κ) {()} ((X s).2 g l):=by rw [rz];exact fun g hg l=>(((root g hg l).1).shave narrow).more unew
    have taken:=earned Q j N a wallet live z n (X s) ((hit s).1.shifted _) τ (κ*τ) (B*κ) tpos ts
      (mul_pos kp tpos) (mul_pos (by linarith) kp) bank previous hi₀ support b (hb.trans hi) r x
    have coef:gross (Q.y j) (n*(loose Q.draws j).L)=B:=by rw [←same]
    rw [coef,level,scheme] at taken
    change ‖(S s).1 n b r x-plume ((S s).2 b r) n x‖ ≤ B^k*(κ*τ+B*κ*τ+B*κ*tail) at taken
    rw [Real.norm_eq_abs] at taken
    apply taken.trans
    have tail0:0 ≤ tail:=(Real.exp_pos _).le
    have A0:0 ≤ κ*τ:=by positivity
    have left:κ*τ+B*κ*τ+B*κ*tail ≤ B^2*(κ*(τ+tail)):=calc
      _ ≤ 2*B*(κ*(τ+tail)):=by nlinarith [mul_nonneg (sub_nonneg.mpr B1) A0,mul_nonneg (by linarith:0 ≤ B) (mul_nonneg kp.le tail0)]
      _ ≤ _:=mul_le_mul_of_nonneg_right (by nlinarith [mul_nonneg (sub_nonneg.mpr B2) (by linarith:0 ≤ B)]) (by positivity)
    calc _ ≤ B^k*(B^2*(κ*(τ+tail))):=mul_le_mul_of_nonneg_left left (by positivity)
         _=B^(k+2)*(κ*(τ+tail)):=by rw [pow_add];ring
  have invpay:inverseCost F T⁻¹ v₀ i ≤ B^(w+1):=by
    have budget:WilsonPointChildWidthPortfolio.invoice F T⁻¹ E ≤ M*(RG16.Lambda A j)^w:=inverse.2 N live digit
    have lambda:RG16.Lambda A j ≤ B:=by
      change 2+Real.log (A.clock.hatBeta j) ≤ B
      linarith [Real.log_le_sub_one_of_pos (show 0<A.clock.hatBeta j from zero_lt_one.trans_le (M1.trans big))]
    have lp:0 ≤ RG16.Lambda A j:=by
      have bet:1 ≤ A.clock.hatBeta j:=M1.trans big
      change 0 ≤ 2+Real.log _;linarith [Real.log_nonneg bet]
    apply ((WilsonPointChildWidthPortfolio.invoice_pays F T⁻¹ hi v₀).trans budget).trans
    calc _ ≤ B*B^w:=mul_le_mul (by linarith) (pow_le_pow_left₀ lp lambda _) (pow_nonneg lp _) (by linarith)
         _=B^(w+1):=by rw [pow_succ,mul_comm]
  have mu:|μ| ≤ B^d:=by
    rw [abs_of_nonneg (by dsimp [μ];positivity)]
    have m:P.L.val ≤ f.val:=by rw [side];exact Nat.le_mul_of_pos_left _ n.pos
    have real:(P.L.val:ℝ) ≤ (f.val:ℝ):=by exact_mod_cast m
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) (real.trans (by linarith)) _

  have receipt:=WilsonPointChildFiniteRestamp.original F T⁻¹ v₀ S (fun s=>((hit s).1.shifted _).verse A live simple R.alloy.B.ratio)
    n i r x μ (B^(k+2)*(κ*(τ+tail))) shot
  have reindex:N-j=(N-(j+1))+1:=by omega
  rw [reindex]
  apply receipt.trans
  have numerical:=scale per
  have yz:zz A j=y:=(congrFun stated j).symm
  change (zz A j*(1+(f.val:ℝ))^4)^total*(τ+Real.exp (-(n.val:ℝ)/(512*zz A j))) ≤ rate A j per at numerical
  rw [yz] at numerical
  change B^total*(τ+tail) ≤ rate A j per at numerical
  exact collect (zero_le_one.trans B1) kp.le (add_nonneg tpos.le (Real.exp_pos _).le) invpay mu numerical

end YM.Integration.WilsonPointChildDigitStage
