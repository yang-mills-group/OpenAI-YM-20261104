import YM.Integration.ManuscriptQLocalScalarDirectionalGerm
import YM.Integration.ManuscriptQLocalScalarClockDemand

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
theorem fixed {n : ℕ→ℕ→ℕ} (p : ManuscriptQLocalStoredGaussianScalar.Paid n R.kit)
    (k : (S).Choices) (q : Chi) (a : ℝ) (z : Site c₀) (U : {U : Forest (S).ratio // changed S d.forest U z})
    (Y : LinkArray G (Frozen hole θ d.forest)) (Z : LinkArray G (Frozen hole θ U.val)) (o : Site c₀) :
    let N := n j₁ j₀
    let r := p.2.1.choose j₁ j₀
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
    obtain ⟨hs,hα,H,H'⟩ := through R d p.2 k q a (fun w => (familyAt w).1) Y (fun w => (familyAt w).2) o
    obtain ⟨_,_,L,L'⟩ := physical R d p k q a (fun w => (familyAt w).1) Y (fun w => (familyAt w).2) o
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

def deviation {j : ℕ} (k : (S).Choices) (F : Forest (S).ratio) (q : Chi) (a : ℝ)
    (Y : LinkArray G (Frozen hole θ F)) (o : Site c₀) (v : Fin j→E) :=
  iteratedFDeriv ℝ j (ManuscriptQLocalStoredGaussianScalar.stored R d k F q a Y o) 0 v-
    iteratedFDeriv ℝ j (ManuscriptQLocalGaussianScalar.scalar R d k F o) 0 v

/-- Quantitative original-versus-prescribed scalar on arbitrary independent
coarse vectors, retaining g^j and the complete weighted changed-tree sum. -/
theorem original {n : ℕ→ℕ→ℕ} (p : ManuscriptQLocalStoredGaussianScalar.Paid n R.kit)
    (k : (S).Choices) (q : Chi) (a : ℝ) (U : ∀ z : Site c₀, {U : Forest (S).ratio // changed S d.forest U z})
    (Y : LinkArray G (Frozen hole θ d.forest)) (Z : ∀ z,LinkArray G (Frozen hole θ (U z).val)) (o : Site c₀)
    (j : ℕ) (hj : j≤n j₁ j₀) (v : Fin j→E) :
    let N := n j₁ j₀
    let r := p.2.1.choose j₁ j₀
    let s := ManuscriptQLocalStoredGaussianScalar.cutWidth G P₀ Pt N r
    let α := ManuscriptQLocalScalarClockPurchase.cutoff Pt (P₀).L/2
    let ε := ManuscriptQLocalStoredGaussianScalar.cutAllowance G P₀ Pt N r*Real.exp (-α*(till θ:ℝ))
    let X := torusPay (PAC G 1) s
    let V := g₀^j*(∏i,‖v i‖)
    0<s ∧ 0<α ∧ |deviation R d k d.forest q a Y o v|≤V*(X^j*ε) ∧
    ∑ z,(native c₀).weight s o z*
      |deviation R d k (U z).val q a (Z z) o v-deviation R d k d.forest q a Y o v|≤V*((torusPay PUnit.{1} s*X^j)*ε) := by
  intro N r s α ε X V
  obtain ⟨hs,hα,H⟩ := ManuscriptQLocalScalarFields.original.{0,0} R d p.2
  obtain ⟨A₀,A₁⟩ := H k q a U Y Z o j hj
  have hg : 0≤g₀^j := pow_nonneg (ManuscriptQLocalIdealSquare.fine R d p.1).1.le j
  have eb := grade R d p k q a Y o j hj v
  change deviation R d k d.forest q a Y o v=_ at eb
  have ez (z : Site c₀) :
      deviation R d k (U z).val q a (Z z) o v-deviation R d k d.forest q a Y o v=
        g₀^j*iteratedFDeriv ℝ j (ManuscriptQLocalScalarFields.changedRoot R d k q a z (U z) Y (Z z) o) 0 v := by
    let d' : LocalFormal.Datum R.family Γ := {d with forest := (U z).val}
    let A := ManuscriptQLocalScalarFields.regular R d' k q a (Z z) o
    let B := ManuscriptQLocalScalarFields.regular R d k q a Y o
    have eu := grade R d' p k q a (Z z) o j hj v
    change deviation R d k (U z).val q a (Z z) o v=g₀^j*iteratedFDeriv ℝ j A 0 v at eu
    have eqF : ManuscriptQLocalScalarFields.changedRoot R d k q a z (U z) Y (Z z) o=A-B := by
      funext x; dsimp only [A,B,d',Pi.sub_apply]; unfold ManuscriptQLocalScalarFields.changedRoot ManuscriptQLocalScalarFields.regular; ring
    have ha := smooth_of_le (ManuscriptQLocalStoredGaussianScalar.regular_smooth R d' p.2.1 k q a (Z z) o) hj
    have hb := smooth_of_le (ManuscriptQLocalStoredGaussianScalar.regular_smooth R d p.2.1 k q a Y o) hj
    rw [eu,eb,eqF,iteratedFDeriv_sub_apply ha hb]
    change g₀^j*iteratedFDeriv ℝ j A 0 v-g₀^j*iteratedFDeriv ℝ j B 0 v=
      g₀^j*(iteratedFDeriv ℝ j A 0 v-iteratedFDeriv ℝ j B 0 v)
    ring
  refine ⟨hs,hα,?_,?_⟩
  · rw [eb,abs_mul,abs_of_nonneg hg]
    have cost : |iteratedFDeriv ℝ j (ManuscriptQLocalScalarFields.regular R d k q a Y o) 0 v|≤(∏ i,‖v i‖)*(X^j*ε) := by
      have aa : Root j s o (fun _ : PUnit.{1} => o)
          (fun _ : PUnit.{1} => ManuscriptQLocalScalarFields.regular R d k q a Y o) (X^j*ε) := A₀
      simpa only [Fintype.sum_unique, Cost.weight_self, one_mul, mul_assoc] using aa.bounded hs.le v
    exact (mul_le_mul_of_nonneg_left cost hg).trans_eq (mul_assoc ..).symm
  · calc
      _ = g₀^j*∑ z,(native c₀).weight s o z*
          |iteratedFDeriv ℝ j (ManuscriptQLocalScalarFields.changedRoot R d k q a z (U z) Y (Z z) o) 0 v| := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro z _
        rw [ez z,abs_mul,abs_of_nonneg hg]; ring
      _ ≤ _ := (mul_le_mul_of_nonneg_left (A₁.bounded hs.le v) hg).trans_eq (mul_assoc ..).symm


/-- Exact floor-to-radius conversion, valid even at the smallest native
cutoff. Its constant and exponential rate depend only on the stage. -/
theorem price_radius (α x A : ℝ) (hα : 0≤α) :
    A*Real.exp (-α*(till x:ℝ)) ≤ (|A| * Real.exp α)*Real.exp (-(α/100000)*(radiusB x:ℝ)) := by
  have hN : radiusB x≤100000*(till x+1) := by unfold till; omega
  have hr : (radiusB x:ℝ)≤100000*((till x:ℝ)+1) := by exact_mod_cast hN
  have he : (radiusB x:ℝ)/100000-1≤(till x:ℝ) := by linarith
  have hx : Real.exp (-α*(till x:ℝ))≤Real.exp α*Real.exp (-(α/100000)*(radiusB x:ℝ)) := by
    rw [←Real.exp_add]
    apply Real.exp_le_exp.mpr
    calc -α*(till x:ℝ) ≤ -α*((radiusB x:ℝ)/100000-1) := mul_le_mul_of_nonpos_left he (neg_nonpos.mpr hα)
         _ = _ := by ring
  exact ((mul_le_mul_of_nonneg_right (le_abs_self A) (Real.exp_pos _).le).trans
    (mul_le_mul_of_nonneg_left hx (abs_nonneg A))).trans_eq (mul_assoc ..).symm

/-- Cap the retained decay rate to keep the floor loss a universal
constant, leaving a linear polynomial in the preassigned scalar tariff. -/
theorem price_radius_polynomial (α x fee : ℝ) (hα : 0≤α) :
    fee*Real.exp (-α*(till x:ℝ))≤(|fee| * Real.exp 1)*Real.exp (-(min α 1/100000)*(radiusB x:ℝ)) := by
  let κ := min α 1
  have hκ : 0≤κ := le_min hα zero_le_one
  have he : Real.exp (-α*(till x:ℝ))≤Real.exp (-κ*(till x:ℝ)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg (min_le_left α 1)) (Nat.cast_nonneg _))
  have h₁ : fee*Real.exp (-α*(till x:ℝ))≤|fee| * Real.exp (-κ*(till x:ℝ)) :=
    (mul_le_mul_of_nonneg_right (le_abs_self fee) (Real.exp_pos _).le).trans
      (mul_le_mul_of_nonneg_left he (abs_nonneg fee))
  have h₂ := price_radius κ x |fee| hκ
  rw [abs_abs] at h₂
  exact (h₁.trans h₂).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (min_le_right α 1)) (abs_nonneg fee)) (Real.exp_pos _).le)

/-- Uniform physical field operators on a prescribed forest change, in
the original manuscript radius and with its original spatial root. -/
theorem fixed_radius {n : ℕ→ℕ→ℕ} (p : ManuscriptQLocalStoredGaussianScalar.Paid n R.kit)
    (k : (S).Choices) (q : Chi) (a : ℝ) (z : Site c₀) (U : {U : Forest (S).ratio // changed S d.forest U z})
    (Y : LinkArray G (Frozen hole θ d.forest)) (Z : LinkArray G (Frozen hole θ U.val)) (o : Site c₀) :
    let N := n j₁ j₀
    let r := p.2.1.choose j₁ j₀
    let s := ManuscriptQLocalStoredGaussianScalar.cutWidth G P₀ Pt N r
    let α := ManuscriptQLocalScalarClockPurchase.cutoff Pt (P₀).L/2
    let c := α/100000
    let geo := |ManuscriptQLocalStoredGaussianScalar.cutAllowance G P₀ Pt N r| * Real.exp α
    let C := (max 1 (torusPay (PAC G 1) s))^N*(geo*Real.exp (-c*(radiusB θ:ℝ)))
    let K := (torusPay PUnit.{1} s*C)*Real.exp (-s*(separation o z:ℝ))
    0<s ∧ 0<c ∧ Through N (ManuscriptQLocalScalarFields.regular R d k q a Y o) 0 C ∧
    Through N (ManuscriptQLocalScalarFields.changedRoot R d k q a z U Y Z o) 0 K ∧
    Through N (error R d k d.forest q a Y o) 0 C ∧
    Through N (fun B => error R d k U.val q a Z o B-error R d k d.forest q a Y o B) 0 K := by
  intro N r s α c geo C K
  obtain ⟨hs,hα,H,H',J,J'⟩ := fixed R d p k q a z U Y Z o
  have hM := price_radius α θ (ManuscriptQLocalStoredGaussianScalar.cutAllowance G P₀ Pt N r) hα.le
  have hC := mul_le_mul_of_nonneg_left hM
    (pow_nonneg (zero_le_one.trans (le_max_left (1:ℝ) (torusPay (PAC G 1) s))) N)
  have hK := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hC (torusPay_nn PUnit.{1} s hs))
    (Real.exp_pos (-s*(separation o z:ℝ))).le
  exact ⟨hs,div_pos hα (by norm_num),H.mono hC,H'.mono hK,J.mono hC,J'.mono hK⟩

/-- The same four physical comparisons with a uniformly polynomial
prefactor and an explicit positive capped stage decay. -/
theorem fixed_polynomial {n : ℕ→ℕ→ℕ} (p : ManuscriptQLocalStoredGaussianScalar.Paid n R.kit)
    (k : (S).Choices) (q : Chi) (a : ℝ) (z : Site c₀) (U : {U : Forest (S).ratio // changed S d.forest U z})
    (Y : LinkArray G (Frozen hole θ d.forest)) (Z : LinkArray G (Frozen hole θ U.val)) (o : Site c₀) :
    let N := n j₁ j₀
    let r := p.2.1.choose j₁ j₀
    let s := ManuscriptQLocalStoredGaussianScalar.cutWidth G P₀ Pt N r
    let α := ManuscriptQLocalScalarClockPurchase.cutoff Pt (P₀).L/2
    let c := min α 1/100000
    let geo := |ManuscriptQLocalStoredGaussianScalar.cutAllowance G P₀ Pt N r| * Real.exp 1
    let C := (max 1 (torusPay (PAC G 1) s))^N*(geo*Real.exp (-c*(radiusB θ:ℝ)))
    let K := (torusPay PUnit.{1} s*C)*Real.exp (-s*(separation o z:ℝ))
    0<s ∧ 0<c ∧ Through N (ManuscriptQLocalScalarFields.regular R d k q a Y o) 0 C ∧
    Through N (ManuscriptQLocalScalarFields.changedRoot R d k q a z U Y Z o) 0 K ∧
    Through N (error R d k d.forest q a Y o) 0 C ∧
    Through N (fun B => error R d k U.val q a Z o B-error R d k d.forest q a Y o B) 0 K := by
  intro N r s α c geo C K
  obtain ⟨hs,hα,H,H',J,J'⟩ := fixed R d p k q a z U Y Z o
  have hM := price_radius_polynomial α θ (ManuscriptQLocalStoredGaussianScalar.cutAllowance G P₀ Pt N r) hα.le
  have hC := mul_le_mul_of_nonneg_left hM
    (pow_nonneg (zero_le_one.trans (le_max_left (1:ℝ) (torusPay (PAC G 1) s))) N)
  have hK := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hC (torusPay_nn PUnit.{1} s hs))
    (Real.exp_pos (-s*(separation o z:ℝ))).le
  exact ⟨hs,div_pos (lt_min hα zero_lt_one) (by norm_num),H.mono hC,H'.mono hK,J.mono hC,J'.mono hK⟩

/-- The strengthened delay is purchased together with the actual scalar
prices, before the level, period, aperture field and forest are supplied. -/
def PaidOrders {G : Gauge} (n order : ℕ→ℕ→ℕ) :=
  @FundedPredictionSupply.Both G (@ManuscriptQLocalStoredGaussianScalar.Paid G n)
    (@ManuscriptQLocalScalarClockPurchase.Demand G (fun _ _ _ _ => 1) order)

theorem order_prices {G : Gauge} (n order : ℕ→ℕ→ℕ) : FundedPredictionSupply.AllPrices (@PaidOrders G n order) :=
  fun s K => FundedPredictionSupply.both (ManuscriptQLocalStoredGaussianScalar.allPrices n s K)
    (ManuscriptQLocalScalarClockPurchase.demand_prices (fun _ _ _ _ => 1) order s K)

/-- Spend one half of the original cutoff exponent on an arbitrarily
preassigned true coupling grade. The other half still pays the actual
radius, while a changed physical tree keeps its independently priced site. -/
theorem fixed_order {n order : ℕ→ℕ→ℕ} (p : PaidOrders n order R.kit)
    (k : (S).Choices) (q : Chi) (a : ℝ) (z : Site c₀) (U : {U : Forest (S).ratio // changed S d.forest U z})
    (Y : LinkArray G (Frozen hole θ d.forest)) (Z : LinkArray G (Frozen hole θ U.val)) (o : Site c₀) :
    let N := n j₁ j₀
    let r := p.1.2.1.choose j₁ j₀
    let s := ManuscriptQLocalStoredGaussianScalar.cutWidth G P₀ Pt N r
    let κ := ManuscriptQLocalScalarClockPurchase.cutoff Pt (P₀).L/4
    let c := min κ 1/100000
    let ρ := ManuscriptQLocalStoredGaussianScalar.cutAllowance G P₀ Pt N r
    let W := (max 1 (torusPay (PAC G 1) s))^N
    let geo := (|ρ| * Real.exp 1)*Real.exp (-c*(radiusB θ:ℝ))
    let C := (W*geo)*g₀^(order j₁ j₀)
    let K := (torusPay PUnit.{1} s*C)*Real.exp (-s*(separation o z:ℝ))
    0<s ∧ 0<c ∧ Through N (ManuscriptQLocalScalarFields.regular R d k q a Y o) 0 C ∧
    Through N (ManuscriptQLocalScalarFields.changedRoot R d k q a z U Y Z o) 0 K ∧
    Through N (error R d k d.forest q a Y o) 0 C ∧
    Through N (fun B => error R d k U.val q a Z o B-error R d k d.forest q a Y o B) 0 K := by
  intro N r s κ c ρ W geo C K
  obtain ⟨hs,_,H,H',J,J'⟩ := fixed R d p.1 k q a z U Y Z o
  have hκ : 0<κ := div_pos (ManuscriptQLocalScalarClockPurchase.cutoff_pos Pt (P₀).L) (by norm_num)
  have hW : 0≤W := pow_nonneg (zero_le_one.trans (le_max_left (1:ℝ) (torusPay (PAC G 1) s))) N
  have hgeo : 0≤geo := mul_nonneg (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le) (Real.exp_pos _).le
  have hp := ManuscriptQLocalScalarClockPurchase.demand_realized R p.2 d.cutoff d.level d.period d.below
  change |(1:ℝ)| * Real.exp (-κ*(till θ:ℝ))≤g₀^(order j₁ j₀) at hp
  rw [abs_one,one_mul] at hp
  have hM : ρ*Real.exp (-κ*(till θ:ℝ))≤geo := price_radius_polynomial κ θ ρ hκ.le
  have split : Real.exp (-(ManuscriptQLocalScalarClockPurchase.cutoff Pt (P₀).L/2)*(till θ:ℝ))=
      Real.exp (-κ*(till θ:ℝ))*Real.exp (-κ*(till θ:ℝ)) := by
    rw [←Real.exp_add]
    congr 1
    dsimp only [κ]
    ring
  have hC : W*(ρ*Real.exp (-(ManuscriptQLocalScalarClockPurchase.cutoff Pt (P₀).L/2)*(till θ:ℝ)))≤C := by
    rw [split]
    calc _ = (W*(ρ*Real.exp (-κ*(till θ:ℝ))))*Real.exp (-κ*(till θ:ℝ)) := by ring
         _ ≤ (W*geo)*Real.exp (-κ*(till θ:ℝ)) :=
           mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hM hW) (Real.exp_pos _).le
         _ ≤ _ := mul_le_mul_of_nonneg_left hp (mul_nonneg hW hgeo)
  have hK := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hC (torusPay_nn PUnit.{1} s hs))
    (Real.exp_pos (-s*(separation o z:ℝ))).le
  exact ⟨hs,div_pos (lt_min hκ zero_lt_one) (by norm_num),H.mono hC,H'.mono hK,J.mono hC,J'.mono hK⟩

/-- The primary scalar comparison on the actual radius M=radiusB θ. The
preperiod constant includes only the exact cost of taking the integer cutoff. -/
theorem radius {n : ℕ→ℕ→ℕ} (p : ManuscriptQLocalStoredGaussianScalar.Paid n R.kit)
    (k : (S).Choices) (q : Chi) (a : ℝ) (U : ∀ z : Site c₀, {U : Forest (S).ratio // changed S d.forest U z})
    (Y : LinkArray G (Frozen hole θ d.forest)) (Z : ∀ z,LinkArray G (Frozen hole θ (U z).val)) (o : Site c₀)
    (j : ℕ) (hj : j≤n j₁ j₀) (v : Fin j→E) :
    let N := n j₁ j₀
    let r := p.2.1.choose j₁ j₀
    let s := ManuscriptQLocalStoredGaussianScalar.cutWidth G P₀ Pt N r
    let α := ManuscriptQLocalScalarClockPurchase.cutoff Pt (P₀).L/2
    let c := α/100000
    let geo := |ManuscriptQLocalStoredGaussianScalar.cutAllowance G P₀ Pt N r| * Real.exp α
    let ε := geo*Real.exp (-c*(radiusB θ:ℝ))
    let X := torusPay (PAC G 1) s
    let V := g₀^j*∏ i,‖v i‖
    0<s ∧ 0<c ∧ |deviation R d k d.forest q a Y o v|≤V*(X^j*ε) ∧
    ∑ z,(native c₀).weight s o z*
      |deviation R d k (U z).val q a (Z z) o v-deviation R d k d.forest q a Y o v|≤V*((torusPay PUnit.{1} s*X^j)*ε) := by
  intro N r s α c geo ε X V
  obtain ⟨hs,hα,H,K⟩ := original R d p k q a U Y Z o j hj v
  have M := price_radius α θ (ManuscriptQLocalStoredGaussianScalar.cutAllowance G P₀ Pt N r) hα.le
  have hg : 0≤g₀ := (ManuscriptQLocalIdealSquare.fine R d p.1).1.le
  have hV : 0≤V := mul_nonneg (pow_nonneg hg j) (Finset.prod_nonneg fun _ _ => norm_nonneg _)
  have hX : 0≤X^j := pow_nonneg (torusPay_nn _ _ hs) j
  refine ⟨hs,div_pos hα (by norm_num),?_,?_⟩
  · exact H.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left M hX) hV)
  · exact K.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left M (mul_nonneg (torusPay_nn _ _ hs) hX)) hV)

end YM.Integration.ManuscriptQLocalScalarDirections
end

