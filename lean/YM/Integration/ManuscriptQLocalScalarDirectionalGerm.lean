import YM.Integration.ManuscriptQLocalStoredGaussianScalar

/-! The stored minus prescribed scalar, on independently specified fields
and at a fixed changed tree, in the measured fine coordinate. -/
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

private theorem rescaled (f h u : E→ℝ) (hf : ContDiffAt ℝ j f 0) (hh : ContDiffAt ℝ j h 0)
    (eqn : ∀ x,u x=f (g • x)+h x) (v : Fin j→E) :
    iteratedFDeriv ℝ j u 0 v-iteratedFDeriv ℝ j h 0 v=g^j*iteratedFDeriv ℝ j f 0 v := by
  let L : E→L[ℝ] E := g • ContinuousLinearMap.id ℝ E
  have hf₀ : ContDiffAt ℝ j f (L 0) := by rw [L.map_zero]; exact hf
  have hu : u=fun x => (f ∘ L) x+h x := funext eqn
  rw [hu,fun_iteratedFDeriv_add_apply (hf₀.comp 0 L.contDiff.contDiffAt) hh,
    add_apply,add_sub_cancel_right,Next.Foundations.jets_linear L hf,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  change (iteratedFDeriv ℝ j f 0) (fun i => g • v i) = _
  have e := (iteratedFDeriv ℝ j f 0).map_smul_univ (fun _ => g) v
  simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] using e

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

/-- Complete original measured root factor minus its independent full
prescription. Both functions include the physical fine-field rescaling. -/
def error (k : (S).Choices) (F : Forest (S).ratio) (q : Chi) (a : ℝ)
    (Y : LinkArray G (Frozen hole θ F)) (o : Site c₀) (B : E) :=
  ManuscriptQLocalStoredGaussianScalar.stored R d k F q a Y o B-ManuscriptQLocalGaussianScalar.scalar R d k F o B

omit [Fintype I] in
/-- The difference of the individual derivatives, on unrestricted named
physical directions. Every one of its independent slots receives g. -/
theorem grade [Fintype I] {n : ℕ→ℕ→ℕ} (p : ManuscriptQLocalStoredGaussianScalar.Paid n R.kit)
    (k : (S).Choices) (q : Chi) (a : ℝ) (Y : LinkArray G (Frozen hole θ d.forest)) (o : Site c₀)
    (j : ℕ) (hj : j≤n j₁ j₀) (v : Fin j→E) :
    iteratedFDeriv ℝ j (ManuscriptQLocalStoredGaussianScalar.stored R d k d.forest q a Y o) 0 v-
      iteratedFDeriv ℝ j (ManuscriptQLocalGaussianScalar.scalar R d k d.forest o) 0 v=
        g₀^j*iteratedFDeriv ℝ j (ManuscriptQLocalScalarFields.regular R d k q a Y o) 0 v := by
  apply rescaled _ _ _ (smooth_of_le (ManuscriptQLocalStoredGaussianScalar.regular_smooth R d p.2.1 k q a Y o) hj)
    (smooth_of_le (ManuscriptQLocalStoredGaussianScalar.ideal_smooth R d p.1 k d.forest o) hj)
  intro B
  unfold ManuscriptQLocalStoredGaussianScalar.stored ManuscriptQLocalScalarFields.regular ManuscriptQLocalGaussianScalar.scalar
  ring

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
theorem through [Fintype I] {n : ℕ→ℕ→ℕ} (p : FundedPredictionSupply.Both (@ManuscriptQLocalScalarSourcePurchase.Paid G n)
    (@ManuscriptQLocalScalarClockPurchase.Paid G n) R.kit) (k : (S).Choices) (q : Chi) (a : ℝ)
    (U : ∀ z : Site c₀, {U : Forest (S).ratio // changed S d.forest U z})
    (Y : LinkArray G (Frozen hole θ d.forest)) (Z : ∀ z,LinkArray G (Frozen hole θ (U z).val)) (o : Site c₀) :
    let N := n j₁ j₀
    let r := p.1.choose j₁ j₀
    let s := ManuscriptQLocalStoredGaussianScalar.cutWidth G P₀ Pt N r
    let α := ManuscriptQLocalScalarClockPurchase.cutoff Pt (P₀).L/2
    let ε := ManuscriptQLocalStoredGaussianScalar.cutAllowance G P₀ Pt N r*Real.exp (-α*(till θ:ℝ))
    let C := (max 1 (torusPay (PAC G 1) s))^N*ε
    0<s ∧ 0<α ∧ Through N (ManuscriptQLocalScalarFields.regular R d k q a Y o) 0 C ∧
    ∀ z,Through N (ManuscriptQLocalScalarFields.changedRoot R d k q a z (U z) Y (Z z) o) 0
      ((torusPay PUnit.{1} s*C)*Real.exp (-s*(separation o z:ℝ))) := by
  intro N r s α ε C
  obtain ⟨hs,hα,all⟩ := ManuscriptQLocalScalarFields.original.{0,0} R d p
  let H := all k q a U Y Z o
  exact ⟨hs,hα,operatorCosts (G:=G) (side:=c₀) (ε:=ε) N o (s:=s) hs _ _ (ManuscriptQLocalStoredGaussianScalar.regular_smooth R d p.1 k q a Y o)
    (fun z => changed_smooth R d p.1 k q a z (U z) Y (Z z) o) H⟩

/-- In the measured variable, the very same two original errors carry
the true fine coupling in each slot and retain the complete uniform quote. -/
theorem physical {n : ℕ→ℕ→ℕ} (p : ManuscriptQLocalStoredGaussianScalar.Paid n R.kit)
    (k : (S).Choices) (q : Chi) (a : ℝ) (U : ∀ z : Site c₀, {U : Forest (S).ratio // changed S d.forest U z})
    (Y : LinkArray G (Frozen hole θ d.forest)) (Z : ∀ z,LinkArray G (Frozen hole θ (U z).val)) (o : Site c₀) :
    let N := n j₁ j₀
    let r := p.2.1.choose j₁ j₀
    let s := ManuscriptQLocalStoredGaussianScalar.cutWidth G P₀ Pt N r
    let α := ManuscriptQLocalScalarClockPurchase.cutoff Pt (P₀).L/2
    let ε := ManuscriptQLocalStoredGaussianScalar.cutAllowance G P₀ Pt N r*Real.exp (-α*(till θ:ℝ))
    let C := (max 1 (torusPay (PAC G 1) s))^N*ε
    0<s ∧ 0<α ∧ Through N (error R d k d.forest q a Y o) 0 C ∧
    ∀ z,Through N (fun B => error R d k (U z).val q a (Z z) o B-error R d k d.forest q a Y o B) 0
      ((torusPay PUnit.{1} s*C)*Real.exp (-s*(separation o z:ℝ))) := by
  intro N r s α ε C
  obtain ⟨hs,hα,H,J⟩ := through R d p.2 k q a U Y Z o
  have hg₀ := ManuscriptQLocalIdealSquare.fine R d p.1
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

