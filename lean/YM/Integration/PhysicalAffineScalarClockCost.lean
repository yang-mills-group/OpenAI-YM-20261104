import YM.Integration.ManuscriptQLocalCompleteScalar
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Numerics
import YM.Integration.WilsonLimitConstruction.FundedWilsonSparsePrice

/-! The numerical scalar fee on the actual fine regulator and scheduled
cutoff. A single independent half of the genuine cutoff exponential buys
the full selected normalization and its named source temperature degree. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.PhysicalAffineScalarClockCost
open Filter Function Lattice RG Pressure Pressure.Stores FreeResolvent FreeResolvent.Affine
open Bloch Next.SectorChange Next.SectorChange.Rows AnalyticBridge.SectorAffine PhysicalAffineScalarResidualPrice
open PhysicalAffineScalarOperatorPrices PhysicalAffineScalarRootContraction ConnectedActivityE6
open scoped Topology Classical ContDiff BigOperators

variable {G : Gauge} {L : Side}

def Power (G : Gauge) (L : Side) (f : ℝ→ℝ) := ∃ a : ℝ, Rate G L a f

namespace Power
variable {f h : ℝ→ℝ}

theorem constant (s : ℝ) : Power G L (fun _ => s) := ⟨0,Rate.const s⟩

theorem product (hf : Power G L f) (hh : Power G L h) : Power G L (fun x => f x*h x) := by
  obtain ⟨a,ha⟩ := hf; obtain ⟨b,hb⟩ := hh; exact ⟨a+b,ha.mul hb⟩

theorem sum (hf : Power G L f) (hh : Power G L h) : Power G L (fun x => f x+h x) := by
  obtain ⟨a,ha⟩ := hf; obtain ⟨b,hb⟩ := hh; exact ⟨max a b,(ha.weaken (le_max_left ..)).add (hb.weaken (le_max_right ..))⟩

theorem scale (hf : Power G L f) (c : ℝ) : Power G L (fun x => c*f x) := by
  obtain ⟨a,ha⟩ := hf; exact ⟨a,ha.mul_left c⟩

theorem fine : Power G L (fun x => betaF G x L) := by
  refine ⟨1,?_⟩; simpa only [Real.rpow_one] using (Rate.power (G:=G) (L:=L) (a:=1))

theorem input_scale (G : Gauge) (L : Side) : ∀ᶠ x : ℝ in atTop, 1≤betaF G x L ∧ max 1 (temp x)⁻¹≤2*betaF G x L := by
  let t := G.slopeConstant*Real.log L.val
  filter_upwards [eventually_ge_atTop (max 1 (max (1-t) (-2*t)))] with x hx
  have hx₀ : 1≤x := (le_max_left ..).trans hx
  have hx₁ : 1≤betaF G x L := by
    change 1≤x+t; have H := ((le_max_left (1-t) (-2*t)).trans (le_max_right ..)).trans hx; linarith
  have hβ : x≤2*betaF G x L := by
    change x≤2*(x+t); have H := ((le_max_right (1-t) (-2*t)).trans (le_max_right ..)).trans hx; linarith
  have hr : Real.sqrt x≤x := (Real.sqrt_le_iff).2 ⟨by linarith,by nlinarith [hx₀]⟩
  have hs : 1≤Real.exp ((Real.log (Real.log x))^2) := Real.one_le_exp_iff.mpr (sq_nonneg _)
  have ht : (temp x)⁻¹≤x := by
    unfold temp; rw [mul_inv_rev,inv_inv]
    simpa only [one_mul] using (mul_le_mul_of_nonneg_right (inv_le_one_of_one_le₀ hs) (Real.sqrt_nonneg x)).trans
      (by simpa only [one_mul] using hr : 1*Real.sqrt x≤x)
  exact ⟨hx₁,max_le (hx₀.trans hβ) (ht.trans hβ)⟩

theorem temperature (n : ℕ) : Power G L (fun x => (max 1 (temp x)⁻¹)^n) := by
  have hf : Rate G L 1 (fun x => max 1 (temp x)⁻¹) := by
    apply ((Rate.power (G:=G) (L:=L) (a:=1)).mul_left 2).compare
    filter_upwards [input_scale G L] with x hx
    rw [Real.rpow_one,abs_of_nonneg (zero_le_one.trans (le_max_left ..)),abs_of_nonneg (by linarith only [hx.1] : 0≤2*betaF G x L)]
    exact hx.2
  exact ⟨_,hf.pow n⟩

theorem source (G : Gauge) (L : Side) (n : ℕ) (N D ρ : ℝ) (hρ : 0<ρ) :
    Power G L (ConditionalAffineLoadPrices.fullFee G L n N D ρ) := by
  have hf : Power G L (fiery G · L) := ⟨_,Rate.flame⟩
  have hcut : Power G L (fun x => Real.exp (-ρ*(till x:ℝ))) := ⟨0,Rate.cutoff hρ⟩
  exact ((temperature n).product (hf.scale N)).sum (hcut.scale (|slip| * D))

theorem residual (n : ℕ) (j h t e : ℝ) (u : ℝ→ℝ) (hu : Power G L u) : Power G L
    (fun x => PhysicalAffineScalarResidualPrice.price n j h t (u x+e) (u x) e) := by
  let center (f : ℝ→ℝ) := fun x => centerFee j h (f x)
  let resid (f : ℝ→ℝ) := fun x => residualFee j h (f x)
  have hc (f : ℝ→ℝ) (hf : Power G L f) : Power G L (center f) := (hf.scale j).scale h
  have hr (f : ℝ→ℝ) (hf : Power G L f) : Power G L (resid f) := hf.sum ((hc f hf).scale j)
  have hv := hu.sum (constant e)
  have hsum := (hr _ hv).sum (hr _ hu)
  have hy : Power G L (fun x => forcingFee j h t (u x) e) := (constant e).sum ((hc u hu).scale t)
  have htodo := (hy.scale j).sum ((hr u hu).scale t)
  have hrem : Power G L (fun x => remainderFee j h t (u x) e) := hy.sum ((htodo.scale h).scale j)
  exact ((hrem.product hsum).scale (2^n)).sum ((hsum.product hrem).scale (2^n))

/-- Any such actual numeric factor consumes just half the existing cutoff
exponent on the common prospective clock. -/
theorem absorb (hf : Power G L f) {κ : ℝ} (hκ : 0<κ) : ∀ᶠ x : ℝ in atTop,
    f x*Real.exp (-κ*(till x:ℝ))≤Real.exp (-(κ/2)*(till x:ℝ)) := by
  obtain ⟨a,H⟩ := hf
  have hsmall := (H.mul (Rate.cutoff (a:=-a-1) (half_pos hκ))).below (by linarith) 1 zero_lt_one
  filter_upwards [hsmall] with x hx
  let e := Real.exp (-(κ/2)*(till x:ℝ))
  have h₀ : Real.exp (-κ*(till x:ℝ))=e*e := by unfold e; rw [←Real.exp_add]; congr 1; ring
  rw [h₀,←mul_assoc]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right ((le_abs_self _).trans hx) (Real.exp_pos _).le
end Power

/-- Original squared fine coupling upper band is four times the scheduled
fine β. The factor two below includes the actual Gaussian half. -/
def envelope (G : Gauge) (P : Patch) (K : KernelChoices) (p : Clip) (n : ℕ)
    (a b δ N D Q ρ : ℝ) (x : ℝ) :=
  let u := ConditionalAffineLoadPrices.fullFee G P.L n N D ρ x
  let e := |slip| * Q
  let C := PhysicalAffineScalarResidualPrice.price n (rowFee G P K p n a b) (inverseFee G P K p n a b δ)
    (PhysicalAffineScalarOperatorPrices.tailFee G P K n a b) (u+e) u e
  2*betaF G x P.L*physicalVolume G P.L δ*C + ManuscriptQLocalCompleteScalar.logFee G P K p n a b

theorem purchase (G : Gauge) (P : Patch) (K : KernelChoices) (p : Clip) (n : ℕ)
    (a b δ N D Q ρ : ℝ) (hρ : 0<ρ) {κ : ℝ} (hκ : 0<κ) : ∀ᶠ x : ℝ in atTop,
    envelope G P K p n a b δ N D Q ρ x*Real.exp (-κ*(till x:ℝ))≤Real.exp (-(κ/2)*(till x:ℝ)) := by
  let hU := Power.source G P.L n N D ρ hρ
  have hC := Power.residual n (rowFee G P K p n a b) (inverseFee G P K p n a b δ)
    (PhysicalAffineScalarOperatorPrices.tailFee G P K n a b) (|slip| * Q) _ hU
  have hF := (((Power.fine (G:=G) (L:=P.L)).scale 2).product (Power.constant (physicalVolume G P.L δ))).product hC
  exact (hF.sum (Power.constant (ManuscriptQLocalCompleteScalar.logFee G P K p n a b))).absorb hκ

/-- Exact half normalization at the real physical Gaussian coupling. -/
theorem coefficient (β : ℝ) (hβ : 0<β) : |(2*(coupling β)^2)⁻¹|=β/2 := by
  have h : (coupling β)^2=β⁻¹ := by simp only [coupling,inv_pow,Real.sq_sqrt hβ.le]
  rw [h,abs_of_pos (inv_pos.mpr (mul_pos (by norm_num) (inv_pos.mpr hβ)))]
  field_simp

/-- Prospective cutoff test independent of all freely purchased row,
translation and inverse budgets. A single fixed field order determines
the required growth degree. -/
def Hot (G : Gauge) (L : Side) (n : ℕ) (κ x : ℝ) :=
  1≤betaF G x L ∧ max 1 (temp x)⁻¹≤2*betaF G x L ∧ fiery G x L≤1 ∧
    (betaF G x L)^(2*n+1)*Real.exp (-(κ/2)*(till x:ℝ))≤1

theorem hot (G : Gauge) (L : Side) (n : ℕ) {κ : ℝ} (hκ : 0<κ) : ∀ᶠ x : ℝ in atTop, Hot G L n κ x := by
  let m := 2*n+1
  have hr : Rate G L (m:ℝ) (fun x => betaF G x L^m) := by simpa only [Real.rpow_natCast] using (Rate.power (G:=G) (L:=L) (a:=m))
  have hpower := (hr.mul (Rate.cutoff (a:=-(m:ℝ)-1) (half_pos hκ))).below (by linarith) 1 zero_lt_one
  have hfire := (Rate.flame (G:=G) (L:=L)).below (by norm_num) 1 zero_lt_one
  filter_upwards [Power.input_scale G L,hpower,hfire] with x hx hb hf
  exact ⟨hx.1,hx.2,(le_abs_self _).trans hf,(le_abs_self _).trans hb⟩

/-- Every priced residual expression is homogeneous of degree two in its
three input-source budgets. The two heat powers are genuine scalar rows,
not a degree charged per intermediate Gaussian matrix. -/
theorem homogeneous (n : ℕ) (j h t v u e s : ℝ) :
    PhysicalAffineScalarResidualPrice.price n j h t (s*v) (s*u) (s*e)=s^2*PhysicalAffineScalarResidualPrice.price n j h t v u e := by
  unfold PhysicalAffineScalarResidualPrice.price remainderFee forcingFee residualFee centerFee; ring

private theorem monotone (n : ℕ) {j h t v u e v' u' e' : ℝ} (hj : 0≤j) (hh : 0≤h) (ht : 0≤t)
    (hv : 0≤v) (hu : 0≤u) (he : 0≤e) (av : v≤v') (au : u≤u') (ae : e≤e') :
    PhysicalAffineScalarResidualPrice.price n j h t v u e≤PhysicalAffineScalarResidualPrice.price n j h t v' u' e' := by
  have hv' := hv.trans av
  have hu' := hu.trans au
  have he' := he.trans ae
  dsimp only [PhysicalAffineScalarResidualPrice.price, remainderFee, forcingFee, residualFee, centerFee]
  gcongr

/-- A numeric, period-independent scalar allowance containing all original
row/inverse prices at the selected coarse field and one changed tree site. -/
def allowance (G : Gauge) (P : Patch) (K : KernelChoices) (p : Clip) (n : ℕ)
    (a b δ N D Q : ℝ) :=
  let U := 2^n*N+|slip| * D
  let e := |slip| * Q
  let C := PhysicalAffineScalarResidualPrice.price n (rowFee G P K p n a b) (inverseFee G P K p n a b δ)
    (PhysicalAffineScalarOperatorPrices.tailFee G P K n a b) (U+e) U e
  2*physicalVolume G P.L δ*C+ManuscriptQLocalCompleteScalar.logFee G P K p n a b

theorem priced (G : Gauge) (P : Patch) (K : KernelChoices) (p : Clip) (n : ℕ)
    (a b δ N D Q ρ κ x β : ℝ) (hd : 0<δ) (hN : 0≤N) (hD : 0≤D) (hQ : 0≤Q) (hρ : 0≤ρ)
    (hlg₀ : 0≤ManuscriptQLocalCompleteScalar.logFee G P K p n a b) (hβ : 0<β) (band : β≤4*betaF G x P.L) (H : Hot G P.L n κ x) :
    let u := ConditionalAffineLoadPrices.fullFee G P.L n N D ρ x
    let e := |slip| * Q
    (ManuscriptQLocalGaussianRootPrice.prefactor G P K p n a b δ (u+e) u e (coupling β)+
      ManuscriptQLocalCompleteScalar.logFee G P K p n a b)*Real.exp (-κ*(till x:ℝ)) ≤
    allowance G P K p n a b δ N D Q*Real.exp (-(κ/2)*(till x:ℝ)) := by
  intro u e
  let θ := betaF G x P.L
  let s := θ^n
  let j := rowFee G P K p n a b
  let h := inverseFee G P K p n a b δ
  let t := PhysicalAffineScalarOperatorPrices.tailFee G P K n a b
  let U := 2^n*N+|slip| * D
  let V := physicalVolume G P.L δ
  let A := PhysicalAffineScalarResidualPrice.price n j h t (U+e) U e
  let C := PhysicalAffineScalarResidualPrice.price n j h t (u+e) u e
  let lg := ManuscriptQLocalCompleteScalar.logFee G P K p n a b
  have hθ : 1≤θ := H.1
  have hθ₀ := zero_le_one.trans hθ
  have hs : 1 ≤ s := one_le_pow₀ hθ
  have hE : 0≤e := mul_nonneg (abs_nonneg _) hQ
  have htorus := torusPay_nn (Co P.L (PAC G 1)) δ hd
  have hV : 0≤V := by
    dsimp [V,physicalVolume]; have := torusPay_nn (Co P.L (PAC G 2)) δ hd; have := torusPay_nn (PAC G 1) δ hd; positivity
  have hj : 0≤j := by dsimp [j,rowFee]; positivity
  have hh : 0≤h := by dsimp [h,inverseFee]; positivity
  have ht : 0≤t := by dsimp [t,PhysicalAffineScalarOperatorPrices.tailFee]; positivity
  have hu : 0≤u := by dsimp [u,ConditionalAffineLoadPrices.fullFee]; unfold fiery temp; positivity
  have u₁ : u ≤ s*U := by
    have term : (max 1 (temp x)⁻¹)^n≤2^n*s := (pow_le_pow_left₀ (zero_le_one.trans (le_max_left ..)) H.2.1 n).trans_eq (mul_pow ..)
    have decay : Real.exp (-ρ*(till x:ℝ))≤1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hρ) (by positivity))
    have hf : 0≤fiery G x P.L := by unfold fiery temp; positivity
    change _+_ ≤ s*(2^n*N+|slip| * D)
    calc
      _ ≤ (2^n*s)*(N*1)+(|slip| * D)*s := add_le_add (mul_le_mul term (mul_le_mul_of_nonneg_left H.2.2.1 hN)
        (mul_nonneg hN hf) (by positivity)) (mul_le_mul_of_nonneg_left (decay.trans hs) (mul_nonneg (abs_nonneg _) hD))
      _ = _ := by ring
  have e₁ : e ≤ s*e := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hs hE
  have c₁ : C ≤ s^2*A := by
    rw [←homogeneous n j h t (U+e) U e s]
    exact monotone n hj hh ht (add_nonneg hu hE) hu hE ((add_le_add u₁ e₁).trans_eq (mul_add ..).symm) u₁ e₁
  have hC : 0≤C := by dsimp [C,PhysicalAffineScalarResidualPrice.price,remainderFee,forcingFee,residualFee,centerFee]; positivity
  have hA : 0≤A := by
    have hU : 0≤U := by dsimp [U]; positivity
    dsimp [A,PhysicalAffineScalarResidualPrice.price,remainderFee,forcingFee,residualFee,centerFee]
    positivity
  have hlg : 0≤lg := hlg₀
  have L₁ : 1≤θ^(2*n+1) := one_le_pow₀ hθ
  have pow : θ*s^2=θ^(2*n+1) := by
    rw [pow_succ θ (2*n), Nat.mul_comm 2 n, pow_mul]
    exact mul_comm ..
  have base : (ManuscriptQLocalGaussianRootPrice.prefactor G P K p n a b δ (u+e) u e (coupling β)+lg)≤
      θ^(2*n+1)*allowance G P K p n a b δ N D Q := by
    change |(2*(coupling β)^2)⁻¹| * V*C+lg≤θ^(2*n+1)*(2*V*A+lg)
    rw [coefficient β hβ]
    have step := mul_le_mul (mul_le_mul_of_nonneg_right (show β/2≤2*θ by linarith only [band]) hV) c₁ hC
      (mul_nonneg (mul_nonneg (by norm_num) hθ₀) hV)
    have logstep : lg≤θ^(2*n+1)*lg := by simpa only [one_mul] using mul_le_mul_of_nonneg_right L₁ hlg
    calc _ ≤ ((2*θ)*V)*(s^2*A)+θ^(2*n+1)*lg := add_le_add step logstep
         _ = _ := by rw [←pow]; ring
  let z := Real.exp (-(κ/2)*(till x:ℝ))
  have positive : 0≤allowance G P K p n a b δ N D Q := add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hV) hA) hlg
  have split : Real.exp (-κ*(till x:ℝ))=z*z := by unfold z; rw [←Real.exp_add]; congr 1; ring
  calc _ ≤ (θ^(2*n+1)*allowance G P K p n a b δ N D Q)*Real.exp (-κ*(till x:ℝ)) := mul_le_mul_of_nonneg_right base (Real.exp_pos _).le
       _ = (allowance G P K p n a b δ N D Q*(θ^(2*n+1)*z))*z := by rw [split]; ring
       _ ≤ _ := by simpa only [mul_one] using mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left H.2.2.2 positive) (Real.exp_pos _).le

end YM.Integration.PhysicalAffineScalarClockCost


