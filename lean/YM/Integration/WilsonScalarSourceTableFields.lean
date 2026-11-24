import YM.Integration.ManuscriptQLocalScalarEstimate
import YM.Integration.ManuscriptQLocalScalarFields
import YM.Integration.WilsonScalarSourceTableRootPrice

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.ManuscriptQLocalScalarEstimate
open Marker Function Filter Matrix Lattice Wilson RG RG.Shoot Tree Precision Exterior
open Pressure Supply Pressure.Testing Pressure.Tube Pressure.Stores Push.SectorMeasure Push.SectorMeasure.Oriented
open Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Gaussian Next.Fluctuations.Sector
open AnalyticBridge.GaussianFieldAlignment FreeResolvent FreeResolvent.Affine FreeResolvent.TestD FreeResolvent.Mark
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Progress.DirectedRecipe
open WilsonLimitConstruction PhysicalAffineScalarClockCost ConditionalCovarianceCutoff
open PhysicalAffineScalarAperture (noHole)
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {I : Type} [DecidableEq I] [Fintype I] {Γ : Census I}
    (R : Run G) (d : LocalFormal.Datum R.family Γ)
local notation "S" => R.family.path.levels.clock.op d.level d.period
local notation "θ" => R.alloy.B.a.clock.hatBeta d.level
local notation "T" => ships R.alloy.B d.cutoff d.level d.period
local notation "A" => noHole S
local notation "c₀" => R.family.side d.level d.period
local notation "j₁" => R.alloy.B.a.clock.J (d.level+1)
local notation "j₀" => R.alloy.B.a.clock.J d.level
local notation "Pt" => query R.metals.p R.metals.K (j₁) (j₀)
local notation "ρ" => ConditionalAffineSourcePrices.rate (Pt) (S).patch.L
local notation "a₀" => (Pt).top.paths
local notation "b₀" => (Pt).top.width
local notation "β₀" => (R.family.path.rep d.cutoff d.period (d.level+1)).beta
local notation "g₀" => coupling β₀

omit [Fintype I] in
/-- Two genuine no-hole root prices, regular and one changed tree, with all
external independent coarse components. The coefficient is a purely
geometric stage number; the original fine temperature has been absorbed
by its prospective clock receipt at the same cutoff. -/
theorem priced {order power : ℕ→ℕ→ℕ} (paid : WilsonScalarSourceTableForecast.Paid order power R.kit)
    (thermal : ManuscriptQLocalScalarClockPurchase.Paid order R.kit) :
    let n := order (j₁) (j₀)
    let r := paid.choose (j₁) (j₀)
    let κ := ManuscriptQLocalScalarClockPurchase.cutoff (Pt) (S).patch.L
    let w := width G (S).patch (S).kernel (T).high (n+1) a₀ b₀
    let δ := ManuscriptQLocalGaussianRootPrice.fixedWidth G (S).patch (S).kernel (T).high (Pt) n r.spatial
    let M := ManuscriptQLocalGaussianRootPrice.sourcePrice G (Pt) (S).patch.L n
    0<δ ∧ 0<M ∧ 0 < min δ w ∧ 0<κ/2 ∧ ∀ (k : (S).Choices) (q : Chi) (b : ℝ)
    (tag : Site c₀) (F' : {U : Forest (S).ratio // changed S d.forest U tag})
    (Y : LinkArray G (Frozen A θ d.forest)) (Z : LinkArray G (Frozen A θ F'.val)) (o : Site c₀)
    (l : List (raw G c₀)), l.length≤n →
    let fee := allowance G (S).patch (S).kernel (T).high n a₀ b₀ δ r.ordinary r.discarded M
    ((marks G c₀ (min δ w)).pay l o * |jet (ray G c₀) (ManuscriptQLocalCompleteScalar.regular R d k q b Y g₀ o) l 0| ≤
      fee*Real.exp (-(κ/2)*(till θ:ℝ))) ∧
    ((marks G c₀ (min δ w)).pay l o * ((native c₀).weight (min δ w) o tag *
      |jet (ray G c₀) (ManuscriptQLocalCompleteScalar.error R d k q b tag F' Y Z g₀ o) l 0|) ≤
      fee*Real.exp (-(κ/2)*(till θ:ℝ))) := by
  intro n r κ w δ M
  have hHot := ManuscriptQLocalScalarClockPurchase.realized R thermal d.cutoff d.level d.period d.below
  have hBand := ManuscriptQLocalScalarClockPurchase.band R d.cutoff d.level d.period d.below
  obtain ⟨hδ,hM,hτ,hκ,h⟩ := ManuscriptQLocalCompleteScalar.priced R d paid
  have hρ := ConditionalAffineSourcePrices.rate_pos (Pt) (S).patch.L
  have hLg : 0≤ManuscriptQLocalCompleteScalar.logFee G (S).patch (S).kernel (T).high n a₀ b₀ :=
    mul_nonneg (Nat.cast_nonneg _) (div_nonneg (cut_nonneg (Pt).top.width_pos (Pt).top.paths_pos.le (by norm_num : 0≤(0:ℝ)) 0) (by norm_num))
  have acquired := PhysicalAffineScalarClockCost.priced G (S).patch (S).kernel (T).high n a₀ b₀ δ
    r.ordinary r.discarded M ρ κ θ β₀ hδ r.ordinary_pos.le r.discarded_pos.le hM.le hρ.le hLg hBand.1 hBand.2 hHot
  refine ⟨hδ,hM,hτ,half_pos hκ,?_⟩
  intro k q b tag F' Y Z o l hl fee
  have step := h k q b tag F' Y Z g₀ o l hl
  exact ⟨step.2.trans acquired,step.1.trans acquired⟩

end YM.Integration.ManuscriptQLocalScalarEstimate

end


set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.ManuscriptQLocalScalarFields
open Marker Function Filter Lattice Wilson RG RG.Shoot Tree Pressure Pressure.Testing Pressure.Tube Pressure.Stores
open Push.SectorMeasure Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Gaussian Next.Fluctuations.Sector
open FreeResolvent FreeResolvent.Affine FreeResolvent.TestD FreeResolvent.Mark PhysicalAffineScalarFieldContraction
open PhysicalNext.JointLoad PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Progress.DirectedRecipe WilsonLimitConstruction
open PhysicalAffineScalarClockCost ConditionalCovarianceCutoff Push.PriceCompiler
open PhysicalAffineScalarAperture (noHole)
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {I : Type} [DecidableEq I] [Fintype I] {Γ : Census I}
    (R : Run G) (d : LocalFormal.Datum R.family Γ)
local notation "S" => R.family.path.levels.clock.op d.level d.period
local notation "θ" => R.alloy.B.a.clock.hatBeta d.level
local notation "T" => ships R.alloy.B d.cutoff d.level d.period
local notation "A" => noHole S
local notation "c₀" => R.family.side d.level d.period
local notation "j₁" => R.alloy.B.a.clock.J (d.level+1)
local notation "j₀" => R.alloy.B.a.clock.J d.level
local notation "Pt" => query R.metals.p R.metals.K (j₁) (j₀)
local notation "P₀" => Clockwork.patch R.rolls (step_paid R.alloy.B.a d.level) (first_le R.alloy.B.valid d.level)
local notation "g₀" => coupling (R.family.path.rep d.cutoff d.period (d.level+1)).beta

omit [Fintype I] in
private theorem prescribed (k : (S).Choices) (F : Forest (S).ratio) (o : Site c₀) :
    PhysicalAffineScalarUncut.scalarAt T θ k F g₀ o =ᶠ[𝓝 (0 : Vec G c₀ 1)] PhysicalAffineScalarSpectralRoot.stationaryScalar T k F g₀ o := by
  have H := ManuscriptQLocalRootWeights.positive R d k F
  have flat := H.self_of_nhds
  filter_upwards [H] with B hB
  exact PhysicalAffineScalarSpectralRoot.original T θ k F g₀ o B flat.2 hB.2

omit [Fintype I] in
private theorem catalogue : (S).patch=(P₀) ∧ (S).kernel=(Pt).bind ∧ (T).high=(Pt).top.clip := by
  have F := Testing.proceeds R.alloy.B d.cutoff d.level d.period d.below
  refine ⟨?_,F.knobs,F.high⟩
  have hL : (S).patch.L=R.rolls.L (j₁) := block_eq R.alloy.B.valid d.level
  have hJ : (S).patch.J=(j₁) := F.atStep
  cases h : (S).patch; rw [h] at hL hJ; unfold Clockwork.patch; congr

omit [Fintype I] in
/-- No period-dependent selection occurs in the geometric allowance, rate
or marked decay. The regular field form and the one-tree field form are
contracted simultaneously. The external field vectors can differ in every slot. -/
theorem priced {order power : ℕ→ℕ→ℕ} (paid : WilsonScalarSourceTableForecast.Paid order power R.kit)
    (thermal : ManuscriptQLocalScalarClockPurchase.Paid order R.kit) :
    let n := order (j₁) (j₀)
    let r := paid.choose (j₁) (j₀)
    let K := (Pt).bind
    let p := (Pt).top.clip
    let a := (Pt).top.paths
    let b := (Pt).top.width
    let P := (P₀)
    let κ := ManuscriptQLocalScalarClockPurchase.cutoff (Pt) P.L
    let δ := ManuscriptQLocalGaussianRootPrice.fixedWidth G P K p (Pt) n r.spatial
    let M := ManuscriptQLocalGaussianRootPrice.sourcePrice G (Pt) P.L n
    let s := min δ (width G P K p (n+1) a b)/2
    let geo := allowance G P K p n a b δ r.ordinary r.discarded M
    let ε := geo*Real.exp (-(κ/2)*(till θ:ℝ))
    0<s ∧ 0<κ/2 ∧ ∀ (k : (S).Choices) (q : Chi) (b : ℝ)
    (F' : ∀ tag : Site c₀, {U : Forest (S).ratio // changed S d.forest U tag})
    (Y : LinkArray G (Frozen A θ d.forest)) (Z : ∀ tag, LinkArray G (Frozen A θ (F' tag).val)) (o : Site c₀)
    (j : ℕ), j≤n →
    Root j s o (fun _ : PUnit => o) (fun _ => regular R d k q b Y o)
      ((torusPay (PAC G 1) s)^j*ε) ∧
    Root j s o id (fun tag => changedRoot R d k q b tag (F' tag) Y (Z tag) o)
      ((torusPay PUnit s*(torusPay (PAC G 1) s)^j)*ε) := by
  intro n r K p a b P κ δ M s geo ε
  have e := catalogue R d
  have H := ManuscriptQLocalScalarEstimate.priced R d paid thermal
  simp only [e.1,e.2.1,e.2.2] at H
  obtain ⟨_,_,hτ,hκ,all⟩ := H
  refine ⟨half_pos hτ,hκ,?_⟩
  intro k q b₁ F' Y Z o j hj
  have hε : 0≤ε := by
    have z := (all k q b₁ o (F' o) Y (Z o) o [] (Nat.zero_le _)).1
    exact (abs_nonneg _).trans (by simpa only [Mark.pay,one_mul] using z)
  have h₁ := PhysicalAffineScalarFieldContraction.regular G c₀ _ ε hτ hε o
    (ManuscriptQLocalCompleteScalar.regular R d k q b₁ Y g₀ o) (n:=j)
    (fun l => (all k q b₁ o (F' o) Y (Z o) o (List.ofFn l) (by simpa using hj)).1)
  have h₂ := PhysicalAffineScalarFieldContraction.tagged G c₀ _ ε hτ hε o
    (fun v => ManuscriptQLocalCompleteScalar.error R d k q b₁ v (F' v) Y (Z v) g₀ o) (n:=j)
    (fun v l => (all k q b₁ v (F' v) Y (Z v) o (List.ofFn l) (by simpa using hj)).2)
  refine ⟨h₁.congr (fun _ => ?_),h₂.congr (fun v => ?_)⟩
  · filter_upwards [prescribed R d k d.forest o] with B hB
    exact congrArg (PhysicalAffineScalarJets.actualRoot T θ k A d.forest q b₁ Y g₀ o B - ·) hB
  · filter_upwards [prescribed R d k d.forest o,prescribed R d k (F' v).val o] with B hB hU
    exact congrArg (fun z : ℝ =>
      (PhysicalAffineScalarJets.actualRoot T θ k A (F' v).val q b₁ (Z v) g₀ o B -
        PhysicalAffineScalarJets.actualRoot T θ k A d.forest q b₁ Y g₀ o B) - z)
      (congrArg₂ (fun x y : ℝ => x-y) hU hB)

end YM.Integration.ManuscriptQLocalScalarFields

end

