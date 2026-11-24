import YM.Integration.ConditionalAffineAcceptedMean
import YM.Integration.ConditionalAffineIdealMean
import YM.Integration.FullQLocalNumericLogarithmicCost
import YM.Integration.ManuscriptQLocalWindowPurchase
import YM.Integration.WilsonLimitConstruction.FundedNeutralCostRun

/-! Independent rooted ordinary and one-tree tensors at the originally selected Wilson stage. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
universe u
namespace YM.Integration.ConditionalAffineMeanPurchase
open Function Filter Lattice Wilson RG Tree Precision Pressure Supply Testing Stores
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir
open Org Input Push Push.PriceCompiler Push.SectorMeasure Next.SectorChange Next.SectorChange.Rows
open AnalyticBridge AnalyticBridge.GaussianFieldAlignment AnalyticBridge.SectorAffine
open Progress.DirectedRecipe RG.Shoot Next.SectorChange.Gaussian FreeResolvent FreeResolvent.Affine
open WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open FullQLocal FullQLocal.RenderedStep FullQLocal.PreRun
open PhysicalNext.Repeat.Daisy.Charity.RG12 ConditionalCovarianceCutoff PhysicalAffineScalarAperture
open scoped Classical Topology ContDiff Matrix.Norms.Frobenius
variable {G : Gauge}

structure Prices where
  spatial : ℝ
  coefficient : ℝ
  decay : ℝ
  positive : 0<spatial
  coeff_pos : 0<coefficient
  decay_pos : 0<decay

def Prices.cost (r : Prices) := max r.coefficient (max r.spatial⁻¹ r.decay⁻¹)

def powers (γ : ℝ) (n : ℕ) := 1+∑ k : Fin (n+1), |ConditionalPhysicalSpan.momentFee γ k|

theorem one_le_powers (γ : ℝ) (n : ℕ) : 1≤powers γ n :=
  le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => abs_nonneg _)

theorem power_covered (γ : ℝ) {n k : ℕ} (hk : k≤n) : ConditionalPhysicalSpan.momentFee γ k≤powers γ n := by
  have h := Finset.single_le_sum (s:=Finset.univ) (f:=fun k : Fin (n+1) => |ConditionalPhysicalSpan.momentFee γ k|)
    (fun _ _ => abs_nonneg _) (Finset.mem_univ (⟨k,Nat.lt_succ_of_le hk⟩ : Fin (n+1)))
  exact (le_abs_self _).trans (h.trans (le_add_of_nonneg_left zero_le_one))

def Prices.expense (p : Prices) (n : ℕ) := p.cost*powers p.spatial n

theorem Prices.cover (p : Prices) (n : ℕ) : p.cost≤p.expense n :=
  le_mul_of_one_le_right (p.coeff_pos.le.trans (le_max_left ..)) (one_le_powers ..)

theorem Prices.power (p : Prices) {n k : ℕ} (hk : k≤n) :
    ConditionalPhysicalSpan.momentFee p.spatial k*p.coefficient ≤ p.expense n := by
  rw [mul_comm]
  exact mul_le_mul (le_max_left ..) (power_covered p.spatial hk) (ConditionalPhysicalSpan.momentFee_nonneg p.positive k)
    (p.coeff_pos.le.trans (le_max_left ..))

def Bought {c f : Side} (S : StepData c f) (T : Tube G S) (n : ℕ) (x : ℝ) (t : Prices) :=
  ∀ (k : S.Choices) (r s : Site c→Greenbelt.Reserve S), (∀ z w, w≠z → r z w=s z w) →
    ∀ (q : Chi) (ε : ℝ)
    (Y : ∀ z, LinkArray G (Frozen (noHole S) x (Greenbelt.allot (r z))))
    (Z : ∀ z, LinkArray G (Frozen (noHole S) x (Greenbelt.allot (s z)))),
    ∀ j : ℕ, j≤n → ∀ y : Site c,
    Stars.NearStar j (taxi c) (home S) id hearth y (ConditionalAffineMeanPrice.visitors S y) t.spatial
      (t.coefficient*Real.exp (-t.decay*(radiusB x:ℝ)))
      (ConditionalAffineAcceptedMean.kernel T x k r s q ε Y Z) ∧
    (∀ h : ℕ, h+1≤n → Stars.NearStar h (taxi c) (home S) hearth hearth y (ConditionalAffineRegularMean.visit S y) t.spatial
      (t.coefficient*Real.exp (-t.decay*(radiusB x:ℝ))) (fun i a l => iteratedFDeriv ℝ (h+1)
        (ConditionalAffineLoadPrices.column (ConditionalAffineMeanDifference.error T x k (r y) q ε (Y y)))
        0 (ray G c ∘ Fin.cons a l) i ())) ∧
    ConditionalAffineMeanDifference.error T x k (r y) q ε (Y y) 0=0

section physical
variable {c f : Side} {S : StepData c f} (T : Tube G S) {n : ℕ} {x : ℝ} {price : Prices}
    (buy : Bought S T n x price) (k : S.Choices) (r s : Site c→Greenbelt.Reserve S)
    (hc : ∀ z w, w≠z → r z w=s z w) (q : Chi) (ε : ℝ)
    (Y : ∀ z, LinkArray G (Frozen (noHole S) x (Greenbelt.allot (r z))))
    (Z : ∀ z, LinkArray G (Frozen (noHole S) x (Greenbelt.allot (s z))))

include buy hc Z

/-- Literal shortest connected torus link span on the genuine one-parent variation. -/
theorem changed_span (j : ℕ) (hj : j≤n) (o : Site c) :
    ConditionalPhysicalSpan.Rooted j (home S) id hearth o (ConditionalAffineMeanPrice.visitors S o) price.spatial
      (price.coefficient*Real.exp (-price.decay*(radiusB x:ℝ)))
      (ConditionalAffineAcceptedMean.kernel T x k r s q ε Y Z) :=
  ConditionalPhysicalSpan.original price.positive.le (buy k r s hc q ε Y Z j hj o).1

/-- Ordinary rooted-flat-position field bound in the same true shortest link norm.
The full no-field coefficient vanishes at each physical retained free key. -/
theorem ordinary_span (j : ℕ) (hj : j+1≤n) (o : Site c) :
    ConditionalPhysicalSpan.Rooted j (home S) hearth hearth o (ConditionalAffineRegularMean.visit S o) price.spatial
      (price.coefficient*Real.exp (-price.decay*(radiusB x:ℝ))) (fun i a l => iteratedFDeriv ℝ (j+1)
        (ConditionalAffineLoadPrices.column (ConditionalAffineMeanDifference.error T x k (r o) q ε (Y o)))
        0 (ray G c ∘ Fin.cons a l) i ()) ∧ ConditionalAffineMeanDifference.error T x k (r o) q ε (Y o) 0=0 := by
  have h := buy k r s hc q ε Y Z 0 (Nat.zero_le _) o
  exact ⟨ConditionalPhysicalSpan.original price.positive.le (h.2.1 j hj),h.2.2⟩

end physical

def panelFee (G : Gauge) (P : Patch) (Pt : Teller G) (n j : ℕ) :=
  let fee := ConditionalTreeCovarianceJets.windowPrice G P Pt.bind Pt.top.clip (n+1) Pt.top.paths Pt.top.width 0 0 +
    diminish G P Pt.bind Pt.top.clip (n+1) 0 Pt.top.paths Pt.top.width 0
  Stars.crowd j fee (totalFoot G P Pt.bind Pt.top.clip (n+1) Pt.top.paths Pt.top.width)

def fullFee (G : Gauge) (P : Patch) (Pt : Teller G) (n j : ℕ) :=
  Stars.crowd j (|earnings G P Pt.bind Pt.top.clip (n+1) Pt.top.paths Pt.top.width|+1)
    (totalFoot G P Pt.bind Pt.top.clip (n+1) Pt.top.paths Pt.top.width)

def halfLogFee (G : Gauge) (P : Patch) (Pt : Teller G) (n j : ℕ) :=
  ConditionalAffineIdealLog.price G P Pt.bind Pt.top.clip (n+1) j Pt.top.paths Pt.top.width

def matrixBase (G : Gauge) (P : Patch) (Pt : Teller G) (n : ℕ) :=
  |(together G P Pt.bind Pt.top.clip (n+1) Pt.top.paths Pt.top.width/4)⁻¹| +
    |(ConditionalAffineMeanTariff.panelRate G P Pt n)⁻¹| +
    ∑ j : Fin (n+1), (|panelFee G P Pt n j|+|fullFee G P Pt n j|+|halfLogFee G P Pt n j|)

def matrixRate (G : Gauge) (P : Patch) (Pt : Teller G) (n : ℕ) :=
  together G P Pt.bind Pt.top.clip (n+1) Pt.top.paths Pt.top.width/4

/-- True arbitrary-forest linear prediction with the coarse identity component included. -/
def forecast (P : Patch) (Pt : Teller G) :=
  max 1 (Progress.StationaryScenes.Response.total P.J Pt.η Pt.C+Real.exp Pt.η)

def matrixCost (G : Gauge) (P : Patch) (Pt : Teller G) (n : ℕ) :=
  max (matrixBase G P Pt n*powers (matrixRate G P Pt n) n) (forecast P Pt)

theorem forecast_covered (G : Gauge) (P : Patch) (Pt : Teller G) (n : ℕ) :
    forecast P Pt≤ matrixCost G P Pt n := le_max_right ..

private theorem matrixBase_nn (G : Gauge) (P : Patch) (Pt : Teller G) (n : ℕ) : 0≤ matrixBase G P Pt n := by
  unfold matrixBase; positivity

private theorem index_base (G : Gauge) (P : Patch) (Pt : Teller G) {n j : ℕ} (hj : j≤n) :
    |panelFee G P Pt n j|+|fullFee G P Pt n j|+|halfLogFee G P Pt n j|≤ matrixBase G P Pt n := by
  have h := Finset.single_le_sum (s:=Finset.univ)
    (f:=fun i : Fin (n+1) => |panelFee G P Pt n i|+|fullFee G P Pt n i|+|halfLogFee G P Pt n i|)
    (fun _ _ => add_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _))
    (Finset.mem_univ (⟨j,Nat.lt_succ_of_le hj⟩ : Fin (n+1)))
  exact h.trans (le_add_of_nonneg_left (add_nonneg (abs_nonneg _) (abs_nonneg _)))

private theorem index_covered (G : Gauge) (P : Patch) (Pt : Teller G) {n j : ℕ} (hj : j≤n) :
    |panelFee G P Pt n j|+|fullFee G P Pt n j|+|halfLogFee G P Pt n j|≤ matrixCost G P Pt n :=
  ((index_base G P Pt hj).trans (le_mul_of_one_le_right (matrixBase_nn ..) (one_le_powers ..))).trans (le_max_left ..)

theorem matrix_moments (G : Gauge) (P : Patch) (Pt : Teller G) {n j k : ℕ} (hj : j≤n) (hk : k≤n) :
    (|panelFee G P Pt n j|+|fullFee G P Pt n j|+|halfLogFee G P Pt n j|)*
      ConditionalPhysicalSpan.momentFee (matrixRate G P Pt n) k≤ matrixCost G P Pt n := by
  have hg : 0< matrixRate G P Pt n := div_pos (div_pos (gauged G P Pt.bind Pt.top.clip (n+1) Pt.top.width_pos Pt.top.paths_pos.le).pos (by positivity)) (by norm_num)
  exact (mul_le_mul (index_base G P Pt hj) (power_covered _ hk) (ConditionalPhysicalSpan.momentFee_nonneg hg k) (matrixBase_nn ..)).trans (le_max_left ..)

private theorem covariance_covered (G : Gauge) (P : Patch) (Pt : Teller G) {n j : ℕ} (hj : j≤n) :
    |panelFee G P Pt n j|+|fullFee G P Pt n j|≤ matrixCost G P Pt n :=
  (le_add_of_nonneg_right (abs_nonneg _)).trans (index_covered G P Pt hj)

theorem halfLog_covered (G : Gauge) (P : Patch) (Pt : Teller G) {n j : ℕ} (hj : j≤n) :
    |halfLogFee G P Pt n j|≤ matrixCost G P Pt n :=
  (le_add_of_nonneg_left (add_nonneg (abs_nonneg _) (abs_nonneg _))).trans (index_covered G P Pt hj)

theorem panel_covered (G : Gauge) (P : Patch) (Pt : Teller G) {n j : ℕ} (hj : j≤n) :
    |panelFee G P Pt n j|≤ matrixCost G P Pt n :=
  (le_add_of_nonneg_right (abs_nonneg _)).trans (covariance_covered G P Pt hj)

theorem full_covered (G : Gauge) (P : Patch) (Pt : Teller G) {n j : ℕ} (hj : j≤n) :
    |fullFee G P Pt n j|≤ matrixCost G P Pt n :=
  (le_add_of_nonneg_left (abs_nonneg _)).trans (covariance_covered G P Pt hj)

def Smooth {c f : Side} (S : StepData c f) (T : Tube G S) (n : ℕ) (x : ℝ) :=
  ∀ (k : S.Choices) (r : Greenbelt.Reserve S) (q : Chi) (ε : ℝ)
    (Y : LinkArray G (Frozen (noHole S) x (Greenbelt.allot r))),
  ContDiffAt ℝ n (ConditionalAffineLoadPrices.column (ConditionalAffineMeanDifference.error T x k r q ε Y)) 0

def Offer (P : Patch) (Pt : Teller G) (n : ℕ) (x : ℝ) (t : Prices) :=
  1≤Real.log (Real.log x) ∧ t.expense n≤1+Real.log (Real.log x) ∧
  matrixCost G P Pt n≤1+Real.log (Real.log x) ∧ max 100000 (macroR P)≤ radiusB x ∧
  ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch=P → Pt.Funds S T →
     100*(1+radiusB x)≤c.val → Bought S T n x t ∧ Smooth S T n x

def Selected {A : Type} (F : Patch→Teller G→ℕ→ℝ→A→Prop) (n : ℕ→ℕ→ℕ) : Prediction G := fun {M} {D} {W} _ =>
  ∃ t : ℕ→ℕ→A, ∀ j x, W.delay.betaEntry j≤x → ∀ i (st : StepStages j i) (fr : M.p.first≤ i),
    F (Clockwork.patch D st fr) (query M.p M.K j i) (n j i) x (t j i)

def Paid (n : ℕ→ℕ→ℕ) : Prediction G := Selected (G:=G) Offer n

/-- All periodic copies draw their quote from the same pre-period funded row. -/
theorem select {A : Type} (fallback : A) (F : Patch→Teller G→ℕ→ℝ→A→Prop) (n : ℕ→ℕ→ℕ)
    (h : ∀ (P : Patch) (Pt : Teller G), P.Branches Pt.bind G → ∀ d, ∃ t, ∀ᶠ x : ℝ in atTop, F P Pt d x t)
    (s : Sheet G) (K : MapPrices) : Prepaid (Selected F n) s K := by
  intro _ _ _ _ _ _ _
  refine ⟨fun _ => 0,fun l _ D _ _ _ _ _ θ _ _ V _ => ?_⟩
  let s' := ThroughLaunch.raise s l
  have rows (j i : ℕ) : ∃ t : A, ∀ᶠ x : ℝ in atTop, ∀ (st : StepStages j i) (fr : s'.first≤ i),
      F (Clockwork.patch D st fr) (query s' K j i) (n j i) x t := by
    by_cases hi : StepStages j i ∧ s'.first≤ i
    · obtain ⟨t,H⟩ := h (Clockwork.patch D hi.1 hi.2) (query s' K j i) (s'.has _) (n j i)
      exact ⟨t,H.mono fun _ hx _ _ => hx⟩
    · exact ⟨fallback,Eventually.of_forall fun _ st fr => False.elim (hi ⟨st,fr⟩)⟩
  choose t ht using rows
  obtain ⟨β,_,hβ,ready⟩ := collect_upper V.betaEntry (fun j x => ∀ i (st : StepStages j i) (fr : s'.first≤ i),
    F (Clockwork.patch D st fr) (query s' K j i) (n j i) x (t j i))
    (fun j => (eventually_transitions j atTop (fun i x => ∀ (st : StepStages j i) (fr : s'.first ≤ i),
      F (Clockwork.patch D st fr) (query s' K j i) (n j i) x (t j i)) (fun i _ => ht j i)).mono
      fun _ hx i st => hx i st st)
  let W : Delays θ := {V with betaEntry:=β}
  refine ⟨W,⟨hβ,le_rfl,le_rfl,le_rfl⟩,fun W' hW _ _ _ _ => ?_⟩
  intros
  exact ⟨t,fun j x hx => ready j x ((hW.beta j).trans hx)⟩

theorem prepaid (n : ℕ→ℕ→ℕ) (s : Sheet G) (K : MapPrices) : Prepaid (Paid n) s K := by
  refine select ⟨1,1,1,zero_lt_one,zero_lt_one,zero_lt_one⟩ Offer n ?_ s K
  intro P Pt hp d
  obtain ⟨γ,C,κ,hγ,hC,hκ,H⟩ := ConditionalAffineAcceptedMean.joint_smooth G P Pt hp d
  let t : Prices := ⟨γ,C,κ,hγ,hC,hκ⟩
  refine ⟨t,?_⟩
  let L := max (t.expense d) (matrixCost G P Pt d)
  filter_upwards [H,(Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop (max 1 L),
        Work.E01.radiusB_tendsto.eventually_ge_atTop (max 100000 (macroR P))] with x hx hL hr
  change max 1 L ≤ Real.log (Real.log x) at hL
  have hh : L≤1+Real.log (Real.log x) := ((le_max_right ..).trans hL).trans (by linarith)
  refine ⟨(le_max_left ..).trans hL,(le_max_left ..).trans hh,(le_max_right ..).trans hh,hr,?_⟩
  intro c f S T hS hT hs
  let H := hx S T hS hT hs
  constructor
  · intro k r u hu q ε Y Z j hj o
    have h := H k r u hu q ε Y Z j hj o
    exact ⟨h.1,h.2.1,h.2.2.1⟩
  intro k r q ε Y
  exact (H k (fun _ => r) (fun _ => r) (fun _ _ _ => rfl) q ε (fun _ => Y) (fun _ => Y)
    0 (Nat.zero_le _) (0 : Site c)).2.2.2

theorem allPrices (n : ℕ→ℕ→ℕ) : FundedPredictionSupply.AllPrices (@Paid G n) := fun s _ => prepaid n s _

theorem selected_receipt {A : Type} {F : Patch→Teller G→ℕ→ℝ→A→Prop} (R : Run G) {n : ℕ→ℕ→ℕ} (paid : Selected F n R.kit) (N m p : ℕ) (hm : m<N) :
    let S := R.alloy.B.a.clock.op m p
    let x := R.alloy.B.a.clock.hatBeta m
    let j := R.alloy.B.a.clock.J (m+1)
    let i := R.alloy.B.a.clock.J m
    let Pt := query R.metals.p R.metals.K j i
    let T := ships R.alloy.B N m p
    F S.patch Pt (n j i) x (paid.choose j i) ∧ Pt.Funds S T ∧ 100*(1+radiusB x)≤(R.alloy.B.a.S.side m p).val := by
  intro S x j i Pt T
  let B := R.alloy.B
  have st := step_paid B.a m
  have fr := first_le B.valid m
  have hL : S.patch.L=R.rolls.L j := block_eq B.valid m
  have hJ : S.patch.J=j := (Testing.proceeds B N m p hm).atStep
  have hP : S.patch=Clockwork.patch R.rolls st fr := by
    cases hh : S.patch
    rw [hh] at hL hJ
    unfold Clockwork.patch
    congr
  have hs : 100*(1+radiusB x)≤(B.a.S.side m p).val := by rw [add_comm 1]; exact B.a.fits.sizeT m p
  refine ⟨?_,Testing.proceeds B N m p hm,hs⟩
  rw [hP]
  exact paid.choose_spec j x (B.valid.pays m) i st fr

theorem receipt (R : Run G) {n : ℕ→ℕ→ℕ} (paid : Paid n R.kit) (N m p : ℕ) (hm : m<N) :
    let S := R.alloy.B.a.clock.op m p
    let x := R.alloy.B.a.clock.hatBeta m
    let j := R.alloy.B.a.clock.J (m+1)
    let i := R.alloy.B.a.clock.J m
    let Pt := query R.metals.p R.metals.K j i
    let T := ships R.alloy.B N m p
    Offer S.patch Pt (n j i) x (paid.choose j i) ∧ Pt.Funds S T ∧ 100*(1+radiusB x)≤(R.alloy.B.a.S.side m p).val :=
  selected_receipt R paid N m p hm

theorem admitted (R : Run G) (m : ℕ) {F : ℝ}
    (hq : 1≤Real.log (Real.log (R.alloy.B.a.clock.hatBeta m)))
    (hf : F≤1+Real.log (Real.log (R.alloy.B.a.clock.hatBeta m))) :
    ∀ {V : Type} {J : Request V} (T : NumericSchedule R.family J), F≤T.admittedCost m := by
  intro V J T
  let Q := Real.log (Real.log (R.alloy.B.a.clock.hatBeta m))
  have hmon : 1+Q≤R.family.path.levels.clock.monitor m := by
    change 1+Q≤Real.exp (Q^2)
    have hsq : Q≤Q^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hq) (zero_le_one.trans hq)]
    linarith [Real.add_one_le_exp (Q^2)]
  have hnext : 0≤R.family.path.levels.clock.monitor (m+1) := (Real.exp_pos _).le
  exact hf.trans (hmon.trans ((le_add_of_nonneg_right hnext).trans (T.monitor_cost m)))

/-- Actual physical source at the no-hole interior stage, on the same run
and all of its admitted periods. Its three constants are bought numerically. -/
theorem realized (R : Run G) {n : ℕ→ℕ→ℕ} (paid : Paid n R.kit) (N m p : ℕ) (hm : m<N) :
    let S := R.alloy.B.a.clock.op m p
    let x := R.alloy.B.a.clock.hatBeta m
    let j := R.alloy.B.a.clock.J (m+1)
    let i := R.alloy.B.a.clock.J m
    let t := paid.choose j i
    Bought S (ships R.alloy.B N m p) (n j i) x t ∧
    t.cost≤1+Real.log (Real.log x) ∧
    ∀ {V : Type} {J : Request V} (T : NumericSchedule R.family J), t.cost≤T.admittedCost m := by
  intro S x j i t
  obtain ⟨⟨hQ,hfee,_,_,h⟩,hT,hp⟩ := receipt R paid N m p hm
  have hbase : t.cost≤1+Real.log (Real.log x) := (t.cover _).trans hfee
  exact ⟨(h S (ships R.alloy.B N m p) rfl hT hp).1,hbase,admitted R m hQ hbase⟩

theorem smooth (R : Run G) {n : ℕ→ℕ→ℕ} (paid : Paid n R.kit) (N m p : ℕ) (hm : m<N) :
    let S := R.alloy.B.a.clock.op m p
    Smooth S (ships R.alloy.B N m p) (n (R.alloy.B.a.clock.J (m+1)) (R.alloy.B.a.clock.J m))
      (R.alloy.B.a.clock.hatBeta m) := by
  intro S
  obtain ⟨⟨_,_,_,_,H⟩,hfund,hw⟩ := receipt R paid N m p hm
  exact (H S (ships R.alloy.B N m p) rfl hfund hw).2

/-- The original absolute two-end covariance prices through every current order
are covered by the same choice; the actual patch is large enough for all the
physical cut matrices and ordered panels. -/
theorem matrix_ready (R : Run G) {n : ℕ→ℕ→ℕ} (paid : Paid n R.kit) (N m p : ℕ) (hm : m<N) :
    let S := R.alloy.B.a.clock.op m p
    let x := R.alloy.B.a.clock.hatBeta m
    let j := R.alloy.B.a.clock.J (m+1)
    let i := R.alloy.B.a.clock.J m
    let Pt := query R.metals.p R.metals.K j i
    100000≤ radiusB x ∧ Bid.Larger (G:=G) S ∧ Pt.Funds S (ships R.alloy.B N m p) ∧
      ∀ {V : Type} {J : Request V} (T : NumericSchedule R.family J),
        matrixCost G S.patch Pt (n j i)≤T.admittedCost m := by
  intro S x j i Pt
  obtain ⟨⟨hQ,_,hc,hr,_⟩,hT,hs⟩ := receipt R paid N m p hm
  change max 100000 (macroR S.patch) ≤ radiusB x at hr
  change 100*(1+radiusB x) ≤ (R.alloy.B.a.clock.schedule.side m p).val at hs
  refine ⟨(le_max_left ..).trans hr,⟨hT.knobs.symm ▸ hT.kernel,?_,by omega⟩,hT,admitted R m hQ hc⟩
  rw [S.ratio.exact_size]
  apply le_trans _ (Nat.le_mul_of_pos_right _ S.ratio.count.property)
  have hR := (le_max_right 100000 (macroR S.patch)).trans hr
  omega

/-- The same physical stock, plateau and other prepaid comparisons can be
selected together with the genuine affine position estimates. -/
theorem available (hG : G.Simple) {ε : ℝ} (hε : 0<ε) (I : FundedNeutralCostRun.Inventory G)
    (n : ℕ→ℕ→ℕ) (pred : Prediction G) (hpred : FundedPredictionSupply.AllPrices (@pred)) :
    ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T), Paid n R.kit ∧ pred R.kit ∧
      NativeFVAPlateau.Correlations R ∧ FundedOriginalProperties.{u} hG ε W ∧
      Nonempty (FundedNeutralCostRun.Purchase I R) := by
  let both : Prediction G := FundedPredictionSupply.Both (@Paid G n) (@pred)
  have hp : FundedPredictionSupply.AllPrices (@both) := fun s p => FundedPredictionSupply.both (allPrices n s p) (hpred s p)
  obtain ⟨R,T,W,pr,hc,hf,hp⟩ := FundedNeutralCostRun.original.{u} hG hε I (@both) hp
  exact ⟨R,T,W,pr.1,pr.2,hc,hf,hp⟩

/-- Numerical sale of the absolute paired half-log. The sum is over one
retained coarse output and every actual field site, including all zero jets. -/
def FullLog {c f : Side} (S : StepData c f) (T : Tube G S) (Pt : Teller G) (d : ℕ) (C : ℝ) :=
  let γ := together G S.patch S.kernel T.high (d+1) Pt.top.paths Pt.top.width/4
  ∀ (k : S.Choices) (j : ℕ), j≤d →
    let K (r : PhysicalNext.Repeat.Greenbelt.Reserve S) (a : Site c) (q : Fin j→ raw G c) :=
      TestD.jet (ray G c) (ConditionalAffineIdealLog.root r k T.high T.up a) (List.ofFn q) 0
    (∀ r o (v : Site c→(Fin j→ raw G c)→Bool),
      (∀ a l, v a l=true → o=a ∨ ∃ z, o=hearth (l z)) → ConditionalAffineIdealLog.Scalar o v γ C (K r)) ∧
    ∀ r s o, (∀ z, z≠o → r z=s z) →
      ConditionalAffineIdealLog.Scalar o (fun _ _ => true) γ C (fun a l => K s a l-K r a l)

theorem full_log (R : Run G) {n : ℕ→ℕ→ℕ} (paid : Paid n R.kit) {V : Type} {Q : Request V}
    (sale : NumericSchedule R.family Q) (N m p : ℕ) (hm : m<N) :
    let S := R.alloy.B.a.clock.op m p
    let j := R.alloy.B.a.clock.J (m+1)
    let i := R.alloy.B.a.clock.J m
    FullLog S (ships R.alloy.B N m p) (query R.metals.p R.metals.K j i) (n j i) (sale.admittedCost m) := by
  intro S j i
  let d := n j i
  let Pt := query R.metals.p R.metals.K j i
  let T := ships R.alloy.B N m p
  obtain ⟨_,he,hT,hpay⟩ := matrix_ready R paid N m p hm
  obtain ⟨Λ,_,hW,_⟩ := hT.feeds
  have hW₀ : T.up.Bounds T.high Pt.top.width Pt.top.paths Λ := by rw [hT.high]; exact hW
  intro k t ht
  have H := ConditionalAffineIdealLog.positions (t:=k) (p:=T.high) (n:=d+1) Pt.top.width_pos Pt.top.paths_pos.le
    (path_sheet T hW₀) he t (by omega)
  have cap : ConditionalAffineIdealLog.price G S.patch S.kernel T.high (d+1) t Pt.top.paths Pt.top.width≤ sale.admittedCost m := by
    rw [hT.knobs,hT.high]
    exact (le_abs_self _).trans ((halfLog_covered G S.patch Pt ht).trans (hpay sale))
  exact ⟨fun r o v h => (H.1 r o v h).trans cap,fun r s o h => (H.2 r s o h).trans cap⟩


structure IdealRates where
  spatial : ℝ
  coefficient : ℝ
  spatial_pos : 0<spatial
  coefficient_pos : 0<coefficient

def IdealRates.cost (p : IdealRates) := max p.coefficient p.spatial⁻¹

def IdealRates.expense (p : IdealRates) (n : ℕ) := p.cost*powers p.spatial n

theorem IdealRates.cover (p : IdealRates) (n : ℕ) : p.cost≤p.expense n :=
  le_mul_of_one_le_right (p.coefficient_pos.le.trans (le_max_left ..)) (one_le_powers ..)

theorem IdealRates.power (p : IdealRates) {n k : ℕ} (hk : k≤n) :
    ConditionalPhysicalSpan.momentFee p.spatial k*p.coefficient ≤ p.expense n := by
  rw [mul_comm]
  exact mul_le_mul (le_max_left ..) (power_covered p.spatial hk) (ConditionalPhysicalSpan.momentFee_nonneg p.spatial_pos k)
    (p.coefficient_pos.le.trans (le_max_left ..))

def IdealOffer (P : Patch) (Pt : Teller G) (n : ℕ) (x : ℝ) (t : IdealRates) :=
  1≤Real.log (Real.log x) ∧ t.expense n≤1+Real.log (Real.log x) ∧
    ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch=P → Pt.Funds S T →
    100*(1+radiusB x)≤c.val → ConditionalAffineIdealMean.Positions S T n x t.spatial t.coefficient

def IdealPaid (n : ℕ→ℕ→ℕ) : Prediction G := Selected (G:=G) IdealOffer n

theorem ideal_prices (n : ℕ→ℕ→ℕ) : FundedPredictionSupply.AllPrices (@IdealPaid G n) := by
  intro s K
  refine select ⟨1,1,zero_lt_one,zero_lt_one⟩ IdealOffer n ?_ s (ThroughLaunch.raging s K)
  intro P Pt hp d
  obtain ⟨γ,C,R,hγ,hC,H⟩ := ConditionalAffineIdealMean.purchased G P Pt hp d
  let t : IdealRates := ⟨γ,C,hγ,hC⟩
  refine ⟨t,?_⟩
  filter_upwards [(Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop (max 1 (t.expense d)),
    Work.E01.radiusB_tendsto.eventually_ge_atTop R] with x hL hr
  change max 1 (t.expense d) ≤ Real.log (Real.log x) at hL
  refine ⟨(le_max_left ..).trans hL,((le_max_right ..).trans hL).trans (le_add_of_nonneg_left zero_le_one),?_⟩
  intro c f S T hS hT hsize
  exact H S T hS hT (le_trans (by gcongr) hsize) x

theorem ideal_realized (R : Run G) {n : ℕ→ℕ→ℕ} (paid : IdealPaid n R.kit) (N m p : ℕ) (hm : m<N) :
    let S := R.alloy.B.a.clock.op m p
    let x := R.alloy.B.a.clock.hatBeta m
    let j := R.alloy.B.a.clock.J (m+1)
    let i := R.alloy.B.a.clock.J m
    let T := ships R.alloy.B N m p
    let q := paid.choose j i
    ConditionalAffineIdealMean.Positions S T (n j i) x q.spatial q.coefficient ∧
      ∀ {V : Type} {J : Request V} (U : NumericSchedule R.family J), q.cost≤U.admittedCost m := by
  intro S x j i T q
  obtain ⟨H,hfund,hsize⟩ := selected_receipt R paid N m p hm
  exact ⟨H.2.2 S T rfl hfund hsize,admitted R m H.1 ((q.cover _).trans H.2.1)⟩

/-- Any prescribed fixed span power is funded together with the original
coefficient, for both full and replaced means and all actual covariance/log
tensors, on the single physical run and its entire collection of tori. -/
theorem moments (R : Run G) {n : ℕ→ℕ→ℕ} (buy : Paid n R.kit) (ideal : IdealPaid n R.kit)
    {V : Type} {Q : Request V} (sale : NumericSchedule R.family Q) (N m p : ℕ) (hm : m<N) :
    let S := R.alloy.B.a.clock.op m p
    let j := R.alloy.B.a.clock.J (m+1)
    let i := R.alloy.B.a.clock.J m
    let Pt := query R.metals.p R.metals.K j i
    let d := n j i
    let b := buy.choose j i
    let u := ideal.choose j i
    ∀ k, k≤d → ConditionalPhysicalSpan.momentFee b.spatial k*b.coefficient≤ sale.admittedCost m ∧
      ConditionalPhysicalSpan.momentFee u.spatial k*u.coefficient≤ sale.admittedCost m ∧ ∀ t, t≤d →
      (|panelFee G S.patch Pt d t|+|fullFee G S.patch Pt d t|+|halfLogFee G S.patch Pt d t|)*
        ConditionalPhysicalSpan.momentFee (matrixRate G S.patch Pt d) k≤ sale.admittedCost m := by
  intro S j i Pt d b u k hk
  obtain ⟨B,_,_⟩ := receipt R buy N m p hm
  obtain ⟨I,_,_⟩ := selected_receipt R ideal N m p hm
  exact ⟨(b.power hk).trans (admitted R m B.1 B.2.1 sale),(u.power hk).trans (admitted R m I.1 I.2.1 sale),
    fun t ht => (matrix_moments G S.patch Pt ht hk).trans (admitted R m B.1 B.2.2.1 sale)⟩

/-- The original full and cutoff affine tensors, the genuine marked-packet
inventory and every additional prediction are all bought by precisely one run. -/
theorem available_with_ideal (hG : G.Simple) {ε : ℝ} (hε : 0<ε)
    (I : FundedNeutralCostRun.Inventory G) (n : ℕ→ℕ→ℕ)
    (pred : Prediction G) (hpred : FundedPredictionSupply.AllPrices (@pred)) :
    ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T), Paid n R.kit ∧ IdealPaid n R.kit ∧ pred R.kit ∧
      NativeFVAPlateau.Correlations R ∧ FundedOriginalProperties.{u} hG ε W ∧
      Nonempty (FundedNeutralCostRun.Purchase I R) := by
  let both : Prediction G := FundedPredictionSupply.Both (@IdealPaid G n) (@pred)
  have hp : FundedPredictionSupply.AllPrices (@both) := fun s p => FundedPredictionSupply.both (ideal_prices n s p) (hpred s p)
  obtain ⟨R,T,W,hR,H,hc,hf,hi⟩ := available.{u} hG hε I n (@both) hp
  exact ⟨R,T,W,hR,H.1,H.2,hc,hf,hi⟩

end YM.Integration.ConditionalAffineMeanPurchase
