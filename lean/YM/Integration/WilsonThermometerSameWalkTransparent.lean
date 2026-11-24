import YM.Integration.WilsonThermometerSameWalkHistory
import YM.Integration.WilsonThermometerSameWalkCircuit
import YM.Integration.WilsonThermometerSameWalkBareField

/-! The cutoff-independent gross physical single-column income on an original
marked Wilson course. Each positive-rank datum is the actual filed field on
every original configuration and is propagated on its own sequence of children. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerSameWalkTransparent
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source RG.Shoot
open Extra.Histories Relay PhysicalNext Repeat Legato Graces Roost
open Pressure Testing Input Precision Org Supply Push SectorMeasure PriceCompiler
open ConnectedActivityE6 Progress.DirectedRecipe AllOrder AllOrder.Transit WheelP AllOrder.Floe QuadraticLocal.Advent
open RG05Readout Native Address Many Records Harvest Push.GridApprox Push.Local MergeProof Accent
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph RG16.Guarding
open WilsonThermometerOffsetTrajectory WilsonThermometerOwnOffsetField WilsonThermometerOffsetResidue
open WilsonThermometerSameWalkMotion WilsonThermometerSameWalkCircuit
open scoped Classical Topology BigOperators
variable {G:Gauge} (R:Run G) (d:ℕ)
local notation "C₀" =>R.family
local notation "F₀" =>R.family.labels.level d
local notation "S₀" =>R.family.localSection d
local notation "A₀" =>R.family.params
local notation "s" => R.family.S.scale
local notation "L" => GermGraph.factor R.family
local notation "κ" i:max => LocalComparison.forcedDivisor R.family i
local notation "fee" => WilsonThermometerSameWalkIncome.fee R

private def wages (N:ℕ) (atTop:ℝ) (a b:ℕ→ℝ) (i:ℕ):ℝ:=
  if h:i ≤ N then Nat.decreasingInduction (motive:=fun _ _=>ℝ) (fun j _ w=>a j*w+b j) atTop h else 0

private theorem start (N:ℕ) (z:ℝ) (a b:ℕ→ℝ) : wages N z a b N=z:=by
  unfold wages;rw [dif_pos le_rfl,Nat.decreasingInduction_self]

private theorem next (N i:ℕ) (z:ℝ) (a b:ℕ→ℝ) (lt:i<N) :
    wages N z a b i=a i*wages N z a b (i+1)+b i:=by
  unfold wages;rw [dif_pos lt.le,dif_pos (show i+1 ≤ N from lt)];exact Nat.decreasingInduction_succ_left ..

theorem original (simple:G.Simple) (shop:RG05Preconstruction.ReadoutPurchase R.b)
    (M:WilsonMeasuredRankedMenu.Menu R d) {ε:ℝ} (ep:0 < ε) (small:ε < 1/8):
    let A:ℝ:=4^(d+1)*(4*M.cost+1)*M.cost
    ∀ᶠ base:ℕ in atTop, ∀ {m k N per:ℕ}, m ≤ base → base ≤ N →
      (∀ h ≤ d,R.family.ref h ≤ base) →
      ∀ (π:ℕ→Layout G)(Γ:ℕ→Pace.Coin)(Ψ:∀ i,Rep G (R.family.side i per)),
      Concourse R.alloy R.kit R.T π Γ m N per k Ψ →
      Topline (Ψ N) (R.family.path.levels.clock.forcedAllowance N) →
      ∀ {D:Rail (C₀)} {B:ℕ→ℕ→ℝ} {V:Sight (C₀) d per} {r:Emblems (C₀) d}
        (z:Site ((C₀).side N per)),
      Enrolled R.makes D B base N per d (digits R N per z) V r →
      (∀ j,base ≤ j → ∀ jn:j<N,
        Registered (N:=N) R Ψ (((C₀).S.toDepth jn per).parent z) d M) →
      ∀ (y:Palette (C₀) d) (i:ℕ) (bi:base ≤ i) (live:i ≤ N),
      let o:=((C₀).S.toDepth live per).parent z
      ∃ W:Coefficient (F₀) ((C₀).side i per), W.Format o (A₀) (Ψ i) ∧
        W.remBound o (Ψ i) (κ i) (2*A*fee base (d+3) ε (1+size y) i) ∧
        W.density o S₀ (Ψ i)=WilsonThermometerSameWalkArm.enteredField R z r live (finer r bi y) ∧
        projection (F₀) (A₀) (Ψ i).p.threshold o W=finer r bi y (primaryLetter d):=by
  intro A
  have Apos:0 < 2*A:=by dsimp [A];have:=M.positive;positivity
  obtain ⟨onset,bare⟩:=eventually_atTop.mp (WilsonThermometerSameWalkBareField.original R d simple M 0 Apos)
  filter_upwards [eventually_ge_atTop onset,string_paid (C:=(C₀)) ep,
    WilsonThermometerSameWalkHistory.original R simple shop d M small] with base paidBase route geometry
  intro m k N per mb bn starts π Γ Ψ course roof D B V r z arm edge y
  let term (j:ℕ):ℝ:=if h:base ≤ j then (F₀).coeffSize (finer r h y (primaryLetter d)) else 0
  let launch:=finer r bn y (primaryLetter d)
  let site (i:ℕ) (hi:i ≤ N):=((C₀).S.toDepth hi per).parent z
  let mass:=1+size y
  have sz:0 ≤ size y:=size_ge _
  have mass0:0 ≤ mass:=by dsimp [mass];positivity
  have limit (j:ℕ) (hj:base ≤ j) (jn:j ≤ N):
      term j ≤ Real.exp (ε*(s j-s base))*size y:=by
    unfold term
    rw [dif_pos hj]
    have bill:(F₀).coeffSize (finer r hj y (primaryLetter d)) ≤ size (finer r hj y):=by
      rw [bill_group]
      exact Finset.single_le_sum (f:=fun l=>((C₀).labels.level (kept l)).coeffSize (finer r hj y l))
        (fun l _=>Finset.sum_nonneg fun _ _=>norm_nonneg _) (Finset.mem_univ (primaryLetter d))
    exact bill.trans ((arm.inverse le_rfl hj jn y).trans (mul_le_mul_of_nonneg_right (route j hj) sz))
  let a (j:ℕ):=L j^(-(1/8:ℝ))
  let b (j:ℕ):=WilsonThermometerSameWalkTariff.charge R d M j*term (j+1)
  let first:=2*A*(1+(F₀).coeffSize launch)
  let rent:=wages N first a b
  obtain ⟨seed,initial,debt,origin⟩:=bare N (paidBase.trans bn) per m k π Γ Ψ course (mb.trans bn) roof z launch
  have rentAt:rent N=first:=start N first a b
  have contract (j:ℕ) (lt:j<N):rent j=a j*rent (j+1)+b j:=next N j first a b lt
  have issue:rent N ≤ 2*A*fee base (d+3) ε mass N:=by
    rw [rentAt]
    apply mul_le_mul_of_nonneg_left _ Apos.le
    have initialPrice: (F₀).coeffSize launch ≤ Real.exp (ε*(s N-s base))*size y:=by
      simpa only [term,dif_pos bn,launch] using limit N bn le_rfl
    have positive:1 ≤ Real.exp (ε*(s N-s base)):=Real.one_le_exp
      (mul_nonneg ep.le (sub_nonneg.mpr ((OPE.scale_mono (C₀).S).monotone bn)))
    have clock:1 ≤ (((C₀).path.levels.clock.hatBeta (N+1))^(d+3)):=one_le_pow₀ (((C₀).path.levels.fits.delayed (N+1)).le)
    unfold WilsonThermometerSameWalkIncome.fee mass
    calc
      _ ≤ Real.exp (ε*(s N-s base))*(1+size y):=by linarith only [initialPrice,positive]
      _ ≤ _:=le_mul_of_one_le_left (by positivity) clock
  have prices:=geometry N mass mass0 rent term issue (fun j hj jn=>(limit (j+1) (hj.trans j.le_succ) jn).trans
    (mul_le_mul_of_nonneg_left (by dsimp [mass];linarith) (Real.exp_pos _).le)) (fun j _ lt=>(contract j lt).le)
  have register (i:ℕ) (live:i ≤ N):base ≤ i → ∃ W:Coefficient (F₀) ((C₀).side i per),
      W.Format (site i live) (A₀) (Ψ i) ∧ W.remBound (site i live) (Ψ i) (κ i) (rent i) ∧
      W.density (site i live) S₀ (Ψ i)=field R z live launch:=by
    induction live using Nat.decreasingInduction with
    | self =>
      intro _
      let g:=(C₀).S.toDepth (le_refl N) per
      have home:site N le_rfl=z:= (congrArg g.parent (like_embed (C:=(C₀)) (N:=N) (p:=per) z).symm).trans (g.embed_parent z)
      rw [home,rentAt]
      exact ⟨seed,initial,by simpa only [first,pow_zero,inv_one,mul_one] using debt,origin⟩
    | of_succ j lt ih =>
      intro bj
      obtain ⟨h,form,funded,same⟩:=ih (bj.trans j.le_succ)
      have fitted:∃ (v:(C₀).label d),v=projection (F₀) (A₀) (Ψ (j+1)).p.threshold (site _ lt) h ∧
        v=finer r (bj.trans j.le_succ) y (primaryLetter d):=by
        refine ⟨_,rfl,?_⟩
        apply (WilsonThermometerSameWalkArm.original R π Γ Ψ course (mb.trans (bj.trans j.le_succ)) (bj.trans j.le_succ) lt
          ((starts d le_rfl).trans (bj.trans j.le_succ)) (fun t ht=>(starts t ht).trans bn) z arm y h form funded ?_).1
        exact Filter.EventuallyEq.of_eq (same.trans (enrolled R z r (bj.trans j.le_succ) lt y).symm)
      obtain ⟨v,equal,tracked⟩:=fitted
      obtain ⟨q,formatted,billed,acted⟩:=edge j bj lt h (rent (j+1)) form funded
      have located:((C₀).path.levels.clock.op j per).ratio.parent (site (j+1) lt)=site j lt.le:=
        (Next.Rank.Station.parent_nested _ ((C₀).S.toDepth lt per) _ ((C₀).S.block_odd _) ((C₀).S.toDepth_odd lt per) z).symm
      dsimp only [site] at located
      rw [located] at formatted billed acted
      refine ⟨q,formatted,?_,?_⟩
      · rw [contract j lt];unfold b term;rw [dif_pos (bj.trans j.le_succ),←tracked,equal];exact billed
      · rw [acted,same];exact WilsonThermometerSameWalkMotion.next R z lt launch
  intro i bi live o
  obtain ⟨W,fit,money,physical⟩:=register i live bi
  have real:W.density o S₀ (Ψ i)=WilsonThermometerSameWalkArm.enteredField R z r live (finer r bi y):=
    physical.trans (enrolled R z r bi live y).symm
  have germ:=WilsonThermometerSameWalkArm.original R π Γ Ψ course (mb.trans bi) bi live ((starts d le_rfl).trans bi)
    (fun h hh=>(starts h hh).trans bn) z arm y W fit money (Filter.EventuallyEq.of_eq real)
  exact ⟨W,fit,rem_mono money (prices i bi live),real,germ.1⟩

end YM.Integration.WilsonThermometerSameWalkTransparent
end
