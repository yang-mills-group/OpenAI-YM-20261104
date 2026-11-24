import YM.Integration.ManuscriptQLocalGaussianScalar
import YM.Integration.ManuscriptQLocalMeasuredAffineRows

/-! The actual held aperture scalar in the measured Gaussian coordinate,
with its paid absolute reference and exponentially small physical error. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.ManuscriptQLocalStoredGaussianScalar
open Marker Function Filter Matrix Lattice Wilson RG RG.Shoot Tree Precision Exterior
open Pressure Supply Pressure.Testing Pressure.Tube Pressure.Stores Push.SectorMeasure Push.SectorMeasure.Oriented
open Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Gaussian Next.Fluctuations.Sector
open AnalyticBridge.GaussianFieldAlignment FreeResolvent FreeResolvent.Affine FreeResolvent.TestD FreeResolvent.Mark
open Push.PriceCompiler PhysicalNext.JointLoad PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt PhysicalNext.Repeat.Legato Progress.DirectedRecipe
open WilsonLimitConstruction
open PhysicalAffineScalarFieldContraction PhysicalAffineScalarRootContraction
open PhysicalAffineScalarAperture (noHole)
open FullQLocal.RenderedStep
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

section Combine
variable {G : Gauge} {c : Side} {ι : Type*} [Fintype ι]

/-- Reinsert the measured coupling in a smooth genuine error before
combining it with a second full scalar estimate of possibly different width. -/
theorem assemble {n : ℕ} {s t A B g : ℝ} {o : Site c} {w : ι→Site c} {f h : ι→Vec G c 1→ℝ}
    (F : Root n s o w f A) (H : Root n t o w h B) (hf : ∀ a, ContDiffAt ℝ n (f a) 0)
    (hh : ∀ a, ContDiffAt ℝ n (h a) 0) (hg : 0≤g) (hg₁ : g≤1) :
    Root n (min s t) o w (fun a b => f a (g • b)+h a b) (A+B) := by
  let J (f : ι→Vec G c 1→ℝ) (a : ι) (l : Fin n → raw G c) := iteratedFDeriv ℝ n (f a) 0 (ray G c ∘ l)
  let W (r : ℝ) (a : ι) (l : Fin n → raw G c) := Real.exp (r*distance (native c) o hearth w a l)
  have line (a : ι) (l : Fin n → raw G c) : J (fun a b => f a (g • b)+h a b) a l=g^n*J f a l+J h a l := by
    let v := ray G c; let L := List.ofFn l
    have hlen : L.length=n := List.length_ofFn
    have fx : ContDiffAt ℝ L.length (f a) 0 := hlen.symm ▸ hf a
    have h₀ : ContDiffAt ℝ L.length (f a) (g • (0:Vec G c 1)) := by simpa only [smul_zero] using fx
    let scale : Vec G c 1 →L[ℝ] Vec G c 1 := g • ContinuousLinearMap.id ℝ _
    have hc : ContDiffAt ℝ L.length (fun B : Vec G c 1 => f a (g • B)) 0 :=
      h₀.comp 0 scale.contDiff.contDiffAt
    have px := jet_add v L hc (hlen.symm ▸ hh a)
    rw [PhysicalAffineScalarIdealGrading.pulled_jet g v (f a) L fx] at px
    simpa only [L,List.length_ofFn,Stars.list_result,J,v] using px
  have we (a : ι) (l : Fin n → raw G c) {s' s : ℝ} (h : s' ≤ s) : W s' a l≤W s a l :=
    Real.exp_le_exp.mpr <| mul_le_mul_of_nonneg_right h
      (add_nonneg ((native c).nonneg ..) (Stars.rays_nn (native c) ..))
  have hpow : |g^n|≤1 := by rw [abs_of_nonneg (pow_nonneg hg _)]; exact pow_le_one₀ hg hg₁
  apply contract G c
  change ∑ a,∑ l,W (min s t) a l*|J (fun a b => f a (g • b)+h a b) a l|≤A+B
  calc
    _ ≤ ∑ a,∑ l,(W s a l*|J f a l|+W t a l*|J h a l|) := by
      apply Finset.sum_le_sum;intro a _; apply Finset.sum_le_sum; intro l _
      rw [line]
      have hsmall : |g^n*J f a l|≤|J f a l| := by rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) hpow
      calc _ ≤ W (min s t) a l*(|J f a l|+|J h a l|) := mul_le_mul_of_nonneg_left
                 ((abs_add_le ..).trans (add_le_add hsmall le_rfl)) (Real.exp_pos _).le
           _ ≤ _ := by rw [mul_add]; exact add_le_add
                         (mul_le_mul_of_nonneg_right (we a l (min_le_left ..)) (abs_nonneg _))
                         (mul_le_mul_of_nonneg_right (we a l (min_le_right ..)) (abs_nonneg _))
    _ = (∑ a,∑ l,W s a l*|J f a l|)+(∑ a,∑ l,W t a l*|J h a l|) := by simp only [Finset.sum_add_distrib]
    _ ≤ _ := add_le_add F.coefficients H.coefficients

end Combine

variable {G : Gauge} {I : Type} [DecidableEq I] {Γ : Census I}
    (R : Run G) (d : LocalFormal.Datum R.family Γ)
local notation "S" => R.family.path.levels.clock.op d.level d.period
local notation "θ" => R.alloy.B.a.clock.hatBeta d.level
local notation "T" => ships R.alloy.B d.cutoff d.level d.period
local notation "c₀" => R.family.side d.level d.period
local notation "E" => Vec G c₀ 1
local notation "j₁" => R.alloy.B.a.clock.J (d.level+1)
local notation "j₀" => R.alloy.B.a.clock.J d.level
local notation "Pt" => query R.metals.p R.metals.K j₁ j₀
local notation "P₀" => Clockwork.patch R.rolls (step_paid R.alloy.B.a d.level) (first_le R.alloy.B.valid d.level)
local notation "A₀" => noHole S
local notation "β" => (R.family.path.rep d.cutoff d.period (d.level+1)).beta
local notation "g₀" => Next.SectorChange.coupling β

def stored (k : (S).Choices) (F : Forest (S).ratio) (q : Chi) (a : ℝ)
    (Y : LinkArray G (Frozen A₀ θ F)) (o : Site c₀) (B : E) :=
  PhysicalAffineScalarJets.actualRoot T θ k A₀ F q a Y g₀ o (g₀ • B)

theorem regular_smooth {n : ℕ→ℕ→ℕ} (p : ManuscriptQLocalScalarSourcePurchase.Paid n R.kit)
    (k : (S).Choices) (q : Chi) (a : ℝ) (Y : LinkArray G (Frozen A₀ θ d.forest)) (o : Site c₀) :
    ContDiffAt ℝ (n j₁ j₀) (ManuscriptQLocalScalarFields.regular R d k q a Y o) 0 := by
  let F := d.forest
  have H := (ManuscriptQLocalGaussianRootPrice.original R d p).2.2.2 k q a o
    (⟨F,fun _ _ => Iff.rfl⟩ : {U : Forest (S).ratio // changed S F U o}) Y Y g₀ o [] (Nat.zero_le _)
  have hf := Testing.proceeds R.alloy.B d.cutoff d.level d.period d.below
  obtain ⟨_,_,hW,_⟩ := hf.feeds
  obtain ⟨_,_,_,hb,hT⟩ := ManuscriptQLocalRootWeights.purchased R d
  have hQ := ManuscriptQLocalRootWeights.positive R d k F
  have hL : ContDiffAt ℝ (n j₁ j₀) (PhysicalAffineScalarCutResidual.logGap T θ k F o) 0 :=
    PhysicalAffineScalarGlobalLog.regular T θ k F o (Pt).top.width_pos (Pt).top.paths_pos.le hW.rows
      (ManuscriptQLocalStationaryGeometry.larger R d.cutoff d.level d.period d.below) hb hT hQ
  apply (H.2.1.add hL).congr_of_eventuallyEq
  filter_upwards [hQ] with B hB
  change PhysicalAffineScalarJets.actualRoot T θ k A₀ F q a Y g₀ o B-PhysicalAffineScalarSpectralRoot.stationaryScalar T k F g₀ o B=_
  rw [←PhysicalAffineScalarSpectralRoot.original T θ k F g₀ o B hQ.self_of_nhds.2 hB.2]
  exact (PhysicalAffineScalarCutResidual.root T θ k F q a Y g₀ o B).trans (add_comm _ _)

theorem ideal_smooth {n : ℕ→ℕ→ℕ} (p : ManuscriptQLocalIdealSquare.Paid n R.kit)
    (k : (S).Choices) (F : Forest (S).ratio) (o : Site c₀) :
    ContDiffAt ℝ (n j₁ j₀) (ManuscriptQLocalGaussianScalar.scalar R d k F o) 0 := by
  have hu : changed S F F o := fun _ _ => Iff.rfl
  have H := ManuscriptQLocalIdealSquare.realized R d p k F F o hu
  have hf := Testing.proceeds R.alloy.B d.cutoff d.level d.period d.below
  obtain ⟨_,_,hw,_⟩ := hf.feeds
  have L := (ManuscriptQLocalGaussianScalar.logarithm T k (n:=n j₁ j₀) (Pt).top.width_pos (Pt).top.paths_pos.le hw.rows
    (ManuscriptQLocalStationaryGeometry.larger R d.cutoff d.level d.period d.below) F F o o hu [] (Nat.zero_le _)).1
  have h₀ : ContDiffAt ℝ (n j₁ j₀) (PhysicalAffineScalarSpectralRoot.halfLog T k F o) (g₀ • (0:E)) := by rw [smul_zero]; exact L
  have B := smooth_of_le (ManuscriptQLocalIdealSquare.graded_smooth R d k F g₀ o H.left) (le_max_right ..)
  have e : ManuscriptQLocalGaussianScalar.scalar R d k F o=fun b =>
      PhysicalAffineScalarSpectralRoot.halfLog T k F o (g₀ • b)+ManuscriptQLocalIdealSquare.graded R d k F g₀ o b := by
    funext b
    change ManuscriptQLocalGaussianScalar.scalar R d k F o b =
      PhysicalAffineScalarSpectralRoot.halfLog T k F o (g₀ • b) +
        (ManuscriptQLocalGaussianScalar.scalar R d k F o b -
          PhysicalAffineScalarSpectralRoot.halfLog T k F o (g₀ • b))
    rw [add_comm,sub_add_cancel]
  have hscale : ContDiffAt ℝ (n j₁ j₀) (fun b : E => g₀ • b) 0 :=
    (g₀ • ContinuousLinearMap.id ℝ E).contDiff.contDiffAt
  rw [e]; exact (h₀.comp 0 hscale).add B

def Paid {G : Gauge} (n : ℕ→ℕ→ℕ) := @FundedPredictionSupply.Both G (@ManuscriptQLocalIdealSquare.Paid G n)
  (@FundedPredictionSupply.Both G (@ManuscriptQLocalScalarSourcePurchase.Paid G n) (@ManuscriptQLocalScalarClockPurchase.Paid G n))

theorem allPrices {G : Gauge} (n : ℕ→ℕ→ℕ) : FundedPredictionSupply.AllPrices (@Paid G n) :=
  fun s K => FundedPredictionSupply.both (ManuscriptQLocalIdealSquare.prices n s K) (ManuscriptQLocalScalarClockPurchase.both n s K)

def cutWidth (G : Gauge) (P : Patch) (stage : Teller G) (n : ℕ) (r : ManuscriptQLocalScalarSourcePurchase.Prices) :=
  let δ := ManuscriptQLocalGaussianRootPrice.fixedWidth G P stage.bind stage.top.clip stage n r.spatial
  min δ (width G P stage.bind stage.top.clip (n+1) stage.top.paths stage.top.width)/2

def cutAllowance (G : Gauge) (P : Patch) (stage : Teller G) (n : ℕ) (r : ManuscriptQLocalScalarSourcePurchase.Prices) :=
  let δ := ManuscriptQLocalGaussianRootPrice.fixedWidth G P stage.bind stage.top.clip stage n r.spatial
  let M := ManuscriptQLocalGaussianRootPrice.sourcePrice G stage P.L n
  PhysicalAffineScalarClockCost.allowance G P stage.bind stage.top.clip n stage.top.paths stage.top.width δ r.ordinary r.discarded M

/-- The scalar actually stored on the selected aperture, in the original
fine coordinate. Its full prescribed part uses the actual numeric schedule;
its regular and one-tree changes retain the actual exponential remainder. -/
theorem original {n : ℕ→ℕ→ℕ} (p : Paid n R.kit) {V : Type} {Q : Request V}
    (sale : NumericSchedule R.family Q) (k : (S).Choices) (q : Chi) (a : ℝ)
    (U : ∀ z : Site c₀, {U : Forest (S).ratio // changed S d.forest U z})
    (Y : LinkArray G (Frozen A₀ θ d.forest)) (Z : ∀ z, LinkArray G (Frozen A₀ θ (U z).val))
    (o : Site c₀) (j : ℕ) (hj : j≤n j₁ j₀) :
    let N := n j₁ j₀
    let r := p.2.1.choose j₁ j₀
    let s := cutWidth G (P₀) (Pt) N r
    let u := ManuscriptQLocalGaussianScalar.spatial G (S).patch (Pt) N (p.1.choose j₁ j₀)/2
    let α := ManuscriptQLocalScalarClockPurchase.cutoff (Pt) (P₀).L/2
    let ε := cutAllowance G (P₀) (Pt) N r*Real.exp (-α*(till θ:ℝ))
    let X := torusPay (PAC G 1) s
    0 < min s u ∧ 0<α ∧
    Root j (min s u) o (fun _ : PUnit => o) (fun _ => stored R d k d.forest q a Y o)
      (X^j*ε+sale.admittedCost d.level) ∧
    Root j (min s u) o id (fun z b => stored R d k (U z).val q a (Z z) o b-stored R d k d.forest q a Y o b)
      ((torusPay PUnit s*X^j)*ε+sale.admittedCost d.level) := by
  intro N r s u α ε X
  have full := ManuscriptQLocalGaussianScalar.financed R d p.1 sale k d.forest U o j hj
  obtain ⟨hs,hα,he⟩ := ManuscriptQLocalScalarFields.original R d p.2
  have G₀ := he k q a U Y Z o j hj
  have hg := ManuscriptQLocalIdealSquare.fine R d p.1
  have hu := (ManuscriptQLocalGaussianScalar.rooted R d p.1 k d.forest (U o).val o o (U o).prop [] (Nat.zero_le _)).1
  have hraw := smooth_of_le (regular_smooth R d p.2.1 k q a Y o) hj
  have hideal := smooth_of_le (ideal_smooth R d p.1 k d.forest o) hj
  let f (z : Site c₀) := ManuscriptQLocalScalarFields.changedRoot R d k q a z (U z) Y (Z z) o
  let h (z : Site c₀) := fun b => ManuscriptQLocalGaussianScalar.scalar R d k (U z).val o b-
    ManuscriptQLocalGaussianScalar.scalar R d k d.forest o b
  have dF (z : Site c₀) : ContDiffAt ℝ j (f z) 0 := by
    let d' : LocalFormal.Datum R.family Γ := {d with forest := (U z).val}
    have e : f z = fun B => ManuscriptQLocalScalarFields.regular R d' k q a (Z z) o B-
        ManuscriptQLocalScalarFields.regular R d k q a Y o B := by
      funext B; unfold f ManuscriptQLocalScalarFields.changedRoot ManuscriptQLocalScalarFields.regular; ring
    rw [e]; exact (smooth_of_le (regular_smooth R d' p.2.1 k q a (Z z) o) hj).sub hraw
  have dH (z : Site c₀) : ContDiffAt ℝ j (h z) 0 := (smooth_of_le (ideal_smooth R d p.1 k (U z).val o) hj).sub hideal
  have eb : (fun (_ : PUnit) b => ManuscriptQLocalScalarFields.regular R d k q a Y o (g₀ • b)+
      ManuscriptQLocalGaussianScalar.scalar R d k d.forest o b) = fun _ => stored R d k d.forest q a Y o := by
    funext _ b; unfold ManuscriptQLocalScalarFields.regular ManuscriptQLocalGaussianScalar.scalar stored; ring
  have ef : (fun z b => f z (g₀ • b)+h z b) =
      fun z b => stored R d k (U z).val q a (Z z) o b-stored R d k d.forest q a Y o b := by
    funext z b; unfold f h ManuscriptQLocalScalarFields.changedRoot ManuscriptQLocalGaussianScalar.scalar stored; ring
  refine ⟨lt_min hs (half_pos hu),hα,?_,?_⟩
  · rw [←eb]; exact assemble G₀.1 full.1 (fun _ => hraw) (fun _ => hideal) hg.1.le hg.2
  · rw [←ef]; exact assemble G₀.2 full.2 dF dH hg.1.le hg.2

end YM.Integration.ManuscriptQLocalStoredGaussianScalar
end

