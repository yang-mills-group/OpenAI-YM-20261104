import YM.Integration.ManuscriptQLocalScalarDirections
import YM.Integration.WilsonScalarSourceTableFields

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.ManuscriptQLocalScalarDirections
open Function Filter Lattice Wilson RG RG.Shoot Tree Pressure Pressure.Testing Pressure.Tube Pressure.Stores
open Push.SectorMeasure Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Gaussian Next.Fluctuations.Sector
open FreeResolvent FreeResolvent.Affine FreeResolvent.TestD FreeResolvent.Mark PhysicalAffineScalarFieldContraction
open Push.PriceCompiler WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open Marker PhysicalNext.JointLoad PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Progress.DirectedRecipe
open PhysicalAffineScalarAperture (noHole)
open AnalyticBridge.SectorAffine.Offset (Through)
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

section Calculus
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {j : ℕ} {g C : ℝ}


private theorem measured {f : E→ℝ} (h : Through j f 0 C) (hg : 0≤g) (hg₁ : g≤1) :
    Through j (fun x => f (g • x)) 0 C := by
  have h₀ : ‖f 0‖≤C*1 := by simpa only [norm_iteratedFDeriv_zero,mul_one] using h.pay 0 (Nat.zero_le _)
  have hc : C*g≤C*1 := by simpa only [mul_one] using mul_le_of_le_one_right h.nonneg hg₁
  simpa only [mul_one] using h.contract hg hg₁ h₀ hc

end Calculus

/-- Convert the original two rooted tensor bills to operator estimates, retaining the changed root. -/
private theorem operatorCosts {G : Gauge} {side : Side} (N : ℕ) (o : Site side) {s ε : ℝ} (hs : 0 < s)
    (f : Vec G side 1 → ℝ) (bad : Site side → Vec G side 1 → ℝ)
    (hf : ContDiffAt ℝ N f 0) (hbad : ∀ z, ContDiffAt ℝ N (bad z) 0)
    (H : ∀ j, j ≤ N →
      Root j s o (fun _ : PUnit.{1} => o) (fun _ => f) ((torusPay (PAC G 1) s)^j * ε) ∧
      Root j s o id bad ((torusPay PUnit.{1} s*(torusPay (PAC G 1) s)^j)*ε)) :
    let C := (max 1 (torusPay (PAC G 1) s))^N*ε
    Through N f 0 C ∧ ∀ z, Through N (bad z) 0 ((torusPay PUnit.{1} s*C)*Real.exp (-s*(separation o z:ℝ))) := by
  intro C
  have hε : 0≤ε := by
    have e := (H 0 (Nat.zero_le _)).1.operators hs.le
    have e₀ : ‖iteratedFDeriv ℝ 0 (f) 0‖≤ε := by
      simpa only [Fintype.sum_unique,Cost.weight_self,one_mul,pow_zero] using e
    exact (norm_nonneg _).trans e₀
  have grow (j : ℕ) (hj : j≤N) : (torusPay (PAC G 1) s)^j≤(max 1 (torusPay (PAC G 1) s))^N :=
    (pow_le_pow_left₀ (torusPay_nn _ _ hs) (le_max_right ..) j).trans (pow_le_pow_right₀ (le_max_left ..) hj)
  refine ⟨⟨hf,?_⟩,?_⟩
  · intro j hj
    have w := (H j hj).1.operators hs.le
    have e : ‖iteratedFDeriv ℝ j (f) 0‖≤(torusPay (PAC G 1) s)^j*ε := by
      simpa only [Fintype.sum_unique,Cost.weight_self,one_mul] using w
    exact e.trans (mul_le_mul_of_nonneg_right (grow j hj) hε)
  · intro z
    refine ⟨hbad z,?_⟩
    intro j hj
    let dU w := ‖iteratedFDeriv ℝ j (bad w) 0‖
    have e : (native side).weight s o z*dU z ≤ (torusPay PUnit.{1} s*(torusPay (PAC G 1) s)^j)*ε :=
      (Finset.single_le_sum (s:=Finset.univ) (f:=fun w => (native side).weight s o w*dU w)
        (fun w _ => mul_nonneg ((native side).weight_nn ..) (norm_nonneg _)) (Finset.mem_univ z)).trans ((H j hj).2.operators hs.le)
    have h₁ : (native side).weight s o z*dU z ≤ torusPay PUnit.{1} s*C := by
      exact e.trans (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (grow j hj) hε) (torusPay_nn _ _ hs))
    have ew : Real.exp (-s*(separation o z:ℝ))=((native side).weight s o z)⁻¹ := by rw [neg_mul,Real.exp_neg]; rfl
    rw [ew,←div_eq_mul_inv]
    apply (le_div_iff₀ (Real.exp_pos _)).2
    simpa only [dU, Cost.weight, mul_comm] using h₁

variable {G : Gauge} {I : Type} [DecidableEq I] [Fintype I] {Γ : Census I}
    (R : Run G) (d : LocalFormal.Datum R.family Γ)
local notation "S" => R.family.path.levels.clock.op d.level d.period
local notation "θ" => R.alloy.B.a.clock.hatBeta d.level
local notation "c₀" => R.family.side d.level d.period
local notation "E" => Vec G c₀ 1
local notation "hole" => noHole S
local notation "j₁" => R.alloy.B.a.clock.J (d.level+1)
local notation "j₀" => R.alloy.B.a.clock.J d.level
local notation "Pt" => query R.metals.p R.metals.K j₁ j₀
local notation "P₀" => Clockwork.patch R.rolls (step_paid R.alloy.B.a d.level) (first_le R.alloy.B.valid d.level)
local notation "g₀" => coupling (R.family.path.rep d.cutoff d.period (d.level+1)).beta

omit [Fintype I] in
private theorem changed_smooth {n : ℕ→ℕ→ℕ} (p : ManuscriptQLocalScalarSourcePurchase.Paid n R.kit)
    (k : (S).Choices) (q : Chi) (a : ℝ) (z : Site c₀) (U : {U : Forest (S).ratio // changed S d.forest U z})
    (Y : LinkArray G (Frozen hole θ d.forest)) (Z : LinkArray G (Frozen hole θ U.val)) (o : Site c₀) :
    ContDiffAt ℝ (n j₁ j₀) (ManuscriptQLocalScalarFields.changedRoot R d k q a z U Y Z o) 0 := by
  let d' : LocalFormal.Datum R.family Γ := {d with forest := U.val}
  have e : ManuscriptQLocalScalarFields.changedRoot R d k q a z U Y Z o=fun B =>
      ManuscriptQLocalScalarFields.regular R d' k q a Z o B-ManuscriptQLocalScalarFields.regular R d k q a Y o B := by
    funext B; unfold ManuscriptQLocalScalarFields.changedRoot ManuscriptQLocalScalarFields.regular; ring
  rw [e]
  exact (ManuscriptQLocalStoredGaussianScalar.regular_smooth R d' p k q a Z o).sub
    (ManuscriptQLocalStoredGaussianScalar.regular_smooth R d p k q a Y o)

omit [Fintype I] in
/-- Unscaled genuine half-log plus square, as a native finite derivative
quote. The tag is kept fixed before taking a supremum over field vectors. -/
theorem pricedThrough [Fintype I] {n power : ℕ→ℕ→ℕ} (p : WilsonScalarSourceTableForecast.Paid n power R.kit)
    (thermal : ManuscriptQLocalScalarClockPurchase.Paid n R.kit) (k : (S).Choices) (q : Chi) (a : ℝ)
    (U : ∀ z : Site c₀, {U : Forest (S).ratio // changed S d.forest U z})
    (Y : LinkArray G (Frozen hole θ d.forest)) (Z : ∀ z,LinkArray G (Frozen hole θ (U z).val)) (o : Site c₀) :
    let N := n j₁ j₀
    let r := p.choose j₁ j₀
    let s := ManuscriptQLocalStoredGaussianScalar.cutWidth G P₀ Pt N r
    let α := ManuscriptQLocalScalarClockPurchase.cutoff Pt (P₀).L/2
    let ε := ManuscriptQLocalStoredGaussianScalar.cutAllowance G P₀ Pt N r*Real.exp (-α*(till θ:ℝ))
    let C := (max 1 (torusPay (PAC G 1) s))^N*ε
    0<s ∧ 0<α ∧ Through N (ManuscriptQLocalScalarFields.regular R d k q a Y o) 0 C ∧
    ∀ z,Through N (ManuscriptQLocalScalarFields.changedRoot R d k q a z (U z) Y (Z z) o) 0
      ((torusPay PUnit.{1} s*C)*Real.exp (-s*(separation o z:ℝ))) := by
  intro N r s α ε C
  obtain ⟨hs,hα,all⟩ := ManuscriptQLocalScalarFields.priced.{0,0} R d p thermal
  let H := all k q a U Y Z o
  exact ⟨hs,hα,operatorCosts (G:=G) (side:=c₀) (ε:=ε) N o (s:=s) hs _ _ (ManuscriptQLocalStoredGaussianScalar.regular_smooth R d (WilsonScalarSourceTableForecast.source R p) k q a Y o)
    (fun z => changed_smooth R d (WilsonScalarSourceTableForecast.source R p) k q a z (U z) Y (Z z) o) H⟩

/-- In the measured variable, the very same two original errors carry
the true fine coupling in each slot and retain the complete uniform quote. -/
theorem pricedPhysical {n power : ℕ→ℕ→ℕ} (p : WilsonScalarSourceTableForecast.Paid n power R.kit)
    (thermal : ManuscriptQLocalScalarClockPurchase.Paid n R.kit)
    (ideal : ManuscriptQLocalIdealSquare.Paid n R.kit)
    (k : (S).Choices) (q : Chi) (a : ℝ) (U : ∀ z : Site c₀, {U : Forest (S).ratio // changed S d.forest U z})
    (Y : LinkArray G (Frozen hole θ d.forest)) (Z : ∀ z,LinkArray G (Frozen hole θ (U z).val)) (o : Site c₀) :
    let N := n j₁ j₀
    let r := p.choose j₁ j₀
    let s := ManuscriptQLocalStoredGaussianScalar.cutWidth G P₀ Pt N r
    let α := ManuscriptQLocalScalarClockPurchase.cutoff Pt (P₀).L/2
    let ε := ManuscriptQLocalStoredGaussianScalar.cutAllowance G P₀ Pt N r*Real.exp (-α*(till θ:ℝ))
    let C := (max 1 (torusPay (PAC G 1) s))^N*ε
    0<s ∧ 0<α ∧ Through N (error R d k d.forest q a Y o) 0 C ∧
    ∀ z,Through N (fun B => error R d k (U z).val q a (Z z) o B-error R d k d.forest q a Y o B) 0
      ((torusPay PUnit.{1} s*C)*Real.exp (-s*(separation o z:ℝ))) := by
  intro N r s α ε C
  obtain ⟨hs,hα,H,J⟩ := pricedThrough R d p thermal k q a U Y Z o
  have hg₀ := ManuscriptQLocalIdealSquare.fine R d ideal
  have baseline : error R d k d.forest q a Y o =
      fun B => ManuscriptQLocalScalarFields.regular R d k q a Y o (g₀ • B) := by
    funext B
    unfold error ManuscriptQLocalStoredGaussianScalar.stored
      ManuscriptQLocalGaussianScalar.scalar ManuscriptQLocalScalarFields.regular
    ring
  refine ⟨hs,hα,?_,?_⟩
  · rw [baseline]
    exact measured H hg₀.1.le hg₀.2
  intro z
  have changedField : (fun B => error R d k (U z).val q a (Z z) o B - error R d k d.forest q a Y o B) =
      fun B => ManuscriptQLocalScalarFields.changedRoot R d k q a z (U z) Y (Z z) o (g₀ • B) := by
    funext B
    unfold error ManuscriptQLocalScalarFields.changedRoot
      ManuscriptQLocalStoredGaussianScalar.stored ManuscriptQLocalGaussianScalar.scalar
    ring
  rw [changedField]
  exact measured (J z) hg₀.1.le hg₀.2



end YM.Integration.ManuscriptQLocalScalarDirections
end

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.ManuscriptQLocalScalarDirections
open Function Filter Lattice Wilson RG RG.Shoot Tree Pressure Pressure.Testing Pressure.Tube Pressure.Stores
open Push.SectorMeasure Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Gaussian Next.Fluctuations.Sector
open FreeResolvent FreeResolvent.Affine FreeResolvent.TestD FreeResolvent.Mark PhysicalAffineScalarFieldContraction
open Push.PriceCompiler WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open Marker PhysicalNext.JointLoad PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Progress.DirectedRecipe
open PhysicalAffineScalarAperture (noHole)
open AnalyticBridge.SectorAffine.Offset (Through)
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {I : Type} [DecidableEq I] [Fintype I] {Γ : Census I}
    (R : Run G) (d : LocalFormal.Datum R.family Γ)
local notation "S" => R.family.path.levels.clock.op d.level d.period
local notation "θ" => R.alloy.B.a.clock.hatBeta d.level
local notation "c₀" => R.family.side d.level d.period
local notation "E" => Vec G c₀ 1
local notation "hole" => noHole S
local notation "j₁" => R.alloy.B.a.clock.J (d.level+1)
local notation "j₀" => R.alloy.B.a.clock.J d.level
local notation "Pt" => query R.metals.p R.metals.K j₁ j₀
local notation "P₀" => Clockwork.patch R.rolls (step_paid R.alloy.B.a d.level) (first_le R.alloy.B.valid d.level)
local notation "g₀" => coupling (R.family.path.rep d.cutoff d.period (d.level+1)).beta

private theorem selectedSite {ι : Type*} [DecidableEq ι] {A : ι → Type*}
    (P : Prop) (M : (w : ι) → A w → Prop) (base : (w : ι) → A w) (z : ι) (v : A z)
    (H : ∀ f : (w : ι) → A w, P ∧ ∀ w, M w (f w)) : P ∧ M z v := by
  obtain ⟨h,m⟩ := H (Function.update base z v)
  exact ⟨h, by simpa only [Function.update_self] using m z⟩

/-- A single actual changed forest and its own frozen field suffice. Extend
this one supplied datum by the original forest at every other site. -/
theorem pricedFixed {n power : ℕ→ℕ→ℕ} (p : WilsonScalarSourceTableForecast.Paid n power R.kit)
    (thermal : ManuscriptQLocalScalarClockPurchase.Paid n R.kit)
    (ideal : ManuscriptQLocalIdealSquare.Paid n R.kit)
    (k : (S).Choices) (q : Chi) (a : ℝ) (z : Site c₀) (U : {U : Forest (S).ratio // changed S d.forest U z})
    (Y : LinkArray G (Frozen hole θ d.forest)) (Z : LinkArray G (Frozen hole θ U.val)) (o : Site c₀) :
    let N := n j₁ j₀
    let r := p.choose j₁ j₀
    let s := ManuscriptQLocalStoredGaussianScalar.cutWidth G P₀ Pt N r
    let α := ManuscriptQLocalScalarClockPurchase.cutoff Pt (P₀).L/2
    let ε := ManuscriptQLocalStoredGaussianScalar.cutAllowance G P₀ Pt N r*Real.exp (-α*(till θ:ℝ))
    let C := (max 1 (torusPay (PAC G 1) s))^N*ε
    let K := (torusPay PUnit.{1} s*C)*Real.exp (-s*(separation o z:ℝ))
    0<s ∧ 0<α ∧ Through N (ManuscriptQLocalScalarFields.regular R d k q a Y o) 0 C ∧
    Through N (ManuscriptQLocalScalarFields.changedRoot R d k q a z U Y Z o) 0 K ∧
    Through N (error R d k d.forest q a Y o) 0 C ∧
    Through N (fun B => error R d k U.val q a Z o B-error R d k d.forest q a Y o B) 0 K := by
  intro N r s α ε C K
  let family (w : Site c₀) := Σ F : {U : Forest (S).ratio // changed S d.forest U w},LinkArray G (Frozen hole θ F.val)
  let base (w : Site c₀) : family w := ⟨⟨d.forest,fun _ _ => Iff.rfl⟩,Y⟩
  let stationary : Prop := 0<s ∧ 0<α ∧
    Through N (ManuscriptQLocalScalarFields.regular R d k q a Y o) 0 C ∧
    Through N (error R d k d.forest q a Y o) 0 C
  let moving (w : Site c₀) (v : family w) : Prop :=
    Through N (ManuscriptQLocalScalarFields.changedRoot R d k q a w v.1 Y v.2 o) 0
        ((torusPay PUnit.{1} s*C)*Real.exp (-s*(separation o w:ℝ))) ∧
    Through N (fun B => error R d k v.1.val q a v.2 o B - error R d k d.forest q a Y o B) 0
        ((torusPay PUnit.{1} s*C)*Real.exp (-s*(separation o w:ℝ)))
  have all (familyAt : (w : Site c₀) → family w) : stationary ∧ ∀ w, moving w (familyAt w) := by
    obtain ⟨hs,hα,H,H'⟩ := pricedThrough R d p thermal k q a (fun w => (familyAt w).1) Y (fun w => (familyAt w).2) o
    obtain ⟨_,_,L,L'⟩ := pricedPhysical R d p thermal ideal k q a (fun w => (familyAt w).1) Y (fun w => (familyAt w).2) o
    constructor
    · dsimp only [stationary]
      refine ⟨hs,hα,?_,?_⟩
      · exact H
      · exact L
    · intro w
      dsimp only [moving]
      constructor
      · exact H' w
      · exact L' w
  obtain ⟨⟨hs,hα,H,L⟩,HU,LU⟩ := selectedSite stationary moving base z ⟨U,Z⟩ all
  exact ⟨hs,hα,H,HU,L,LU⟩

end YM.Integration.ManuscriptQLocalScalarDirections
end



