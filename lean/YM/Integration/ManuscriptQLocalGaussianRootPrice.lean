import YM.Integration.ManuscriptQLocalPaidRootSquare
import YM.Integration.PhysicalAffineScalarOperatorPrices

/-! The actual no-hole scalar square at the original changed physical tree.
The genuine paired determinant has its own independently rooted spectral
estimate. The complete remaining coefficient here is numeric. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.ManuscriptQLocalGaussianRootPrice
open Marker Function Filter Matrix Lattice Wilson RG RG.Shoot Tree Precision Exterior
open Pressure Supply Pressure.Testing Pressure.Tube Pressure.Stores Push.SectorMeasure Push.SectorMeasure.Oriented
open Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Gaussian Next.Fluctuations.Sector
open AnalyticBridge.GaussianFieldAlignment FreeResolvent FreeResolvent.Affine FreeResolvent.TestD FreeResolvent.Mark
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Progress.DirectedRecipe
open PhysicalAffineScalarCutWeights PhysicalAffineScalarCutResidual PhysicalAffineScalarGaussianWeights
open PhysicalAffineScalarRootContraction PhysicalAffineScalarResidualVectors PhysicalAffineScalarResidualPrice
open PhysicalAffineScalarOperatorPrices ConditionalAffineLoadPrices ConditionalAffineForcing
open PhysicalAffineScalarAperture (noHole)
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

/-- Explicit physical root amount. Every parameter is original stage data or
a purchase made before its torus, actual tree, translation or field legs. -/
def prefactor (G : Gauge) (P : Patch) (K : KernelChoices) (p : Clip) (n : ℕ)
    (a b δ v u e g : ℝ) := |(2*g^2)⁻¹| * physicalVolume G P.L δ *
  PhysicalAffineScalarResidualPrice.price n (rowFee G P K p n a b) (inverseFee G P K p n a b δ)
    (PhysicalAffineScalarOperatorPrices.tailFee G P K n a b) v u e

variable {G : Gauge} {I : Type} [DecidableEq I] [Fintype I] {Γ : Census I}
    (R : Run G) (d : LocalFormal.Datum R.family Γ)
local notation "S" => R.family.path.levels.clock.op d.level d.period
local notation "θ" => R.alloy.B.a.clock.hatBeta d.level
local notation "T" => ships R.alloy.B d.cutoff d.level d.period
local notation "A" => noHole S
local notation "c₀" => R.family.side d.level d.period
local notation "Coarse" => Gaussian.Vec (Raw G c₀)
local notation "rows" => Rows.Receipt G S
local notation "rpos" => PhysicalAffineScalarComparison.rowRoot (G:=G) S
local notation "j₁" => R.alloy.B.a.clock.J (d.level+1)
local notation "j₀" => R.alloy.B.a.clock.J d.level
local notation "Pt" => query R.metals.p R.metals.K (j₁) (j₀)
local notation "ρ" => ConditionalAffineSourcePrices.rate (Pt) (S).patch.L
local notation "a₀" => (Pt).top.paths
local notation "b₀" => (Pt).top.width

/-- Constants selected before a stage's torus, signed gauge, and tree. -/
def sourceWidth (G : Gauge) (P : Teller G) (L : Side) (n : ℕ) :=
  (PhysicalAffineScalarInputPrices.source G P L n).choose

def sourcePrice (G : Gauge) (P : Teller G) (L : Side) (n : ℕ) :=
  (PhysicalAffineScalarInputPrices.source G P L n).choose_spec.choose

def fixedWidth (G : Gauge) (P : Patch) (K : KernelChoices) (p : Clip) (purchase : Teller G) (n : ℕ) (s : ℝ) :=
  min (min (sourceWidth G purchase P.L n) s) (PhysicalAffineScalarOperatorPrices.range G P K p n purchase.top.paths purchase.top.width)

private theorem changed_residual {x y u v a b c d : ℝ} (first : x-u=a+c) (second : y-v=b+d) :
    (x-y)-(u-v)-(a-b)=c-d := by linarith only [first, second]

private theorem restrict_difference (test : Prop) [Decidable test] (first second : ℝ) :
    (if test then first else 0) - (if test then second else 0) =
      if test then first-second else 0 := by
  by_cases h : test <;> simp [h]

omit [Fintype I] in
theorem original {order : ℕ→ℕ→ℕ} (paid : ManuscriptQLocalScalarSourcePurchase.Paid order R.kit) :
    let n := order (j₁) (j₀)
    let r := paid.choose (j₁) (j₀)
    let u₀ := ConditionalAffineLoadPrices.fullFee G (S).patch.L n r.ordinary r.discarded ρ θ
    let κ := min ρ (b₀/4)
    let δ := fixedWidth G (S).patch (S).kernel (T).high (Pt) n r.spatial
    let M := sourcePrice G (Pt) (S).patch.L n
    0<δ ∧ 0<M ∧ 0<κ ∧ ∀ (k : (S).Choices) (q : Chi) (b : ℝ) (tag : Site c₀)
    (F' : {U : Forest (S).ratio // changed S d.forest U tag})
    (Y : LinkArray G (Frozen A θ d.forest)) (Z : LinkArray G (Frozen A θ F'.val)) (g : ℝ) (o : Site c₀)
    (l : List (raw G c₀)), l.length≤n →
      (ContDiffAt ℝ n (ManuscriptQLocalRootPrice.error R d k q b tag F' Y Z g o) 0 ∧
      (marks G c₀ δ).pay l o * ((native c₀).weight δ o tag *
        |jet (ray G c₀) (ManuscriptQLocalRootPrice.error R d k q b tag F' Y Z g o) l 0|) ≤
      prefactor G (S).patch (S).kernel (T).high n a₀ b₀ δ (u₀+|slip| * M) u₀ (|slip| * M) g *
        Real.exp (-κ*(till θ:ℝ))) ∧
      (ContDiffAt ℝ n (squareGap T θ k d.forest q b Y g o) 0 ∧
       (marks G c₀ δ).pay l o*|jet (ray G c₀) (squareGap T θ k d.forest q b Y g o) l 0|≤
       prefactor G (S).patch (S).kernel (T).high n a₀ b₀ δ (u₀+|slip| * M) u₀ (|slip| * M) g *
         Real.exp (-κ*(till θ:ℝ))) := by
  intro n r u₀ κ δ M
  have hP := Testing.proceeds R.alloy.B d.cutoff d.level d.period d.below
  have hv := ManuscriptQLocalScalarSourcePurchase.realized R paid d.cutoff d.level d.period d.below
  obtain ⟨_,_,hW₀,_⟩ := hP.feeds
  have hW : Sheet (T).up b₀ a₀ := hW₀.rows
  have hb := (Pt).top.width_pos
  have ha := (Pt).top.paths_pos.le
  have hp : (S).patch.Branches (S).kernel G := hP.knobs.symm ▸ hP.kernel
  have hsize : 100*(1+radiusB θ)≤(R.alloy.B.a.S.side d.level d.period).val := by
    rw [add_comm 1]; exact R.alloy.B.a.fits.sizeT d.level d.period
  have hc : 1<(c₀).val := by
    change 1 < (R.alloy.B.a.S.side d.level d.period).val
    omega
  have he := ManuscriptQLocalStationaryGeometry.larger R d.cutoff d.level d.period d.below
  obtain ⟨σ,K,Λ,_,hT⟩ := ManuscriptQLocalRootWeights.purchased R d
  let s := sourceWidth G (Pt) (S).patch.L n
  obtain ⟨hs,hM,hρ,hTail⟩ := (PhysicalAffineScalarInputPrices.source G (Pt) (S).patch.L n).choose_spec.choose_spec
  have hδ : 0<δ := lt_min (lt_min hs r.spatial_pos) (range_pos G (S).patch (S).kernel (T).high n a₀ b₀ hb ha)
  have hRange : δ≤PhysicalAffineScalarOperatorPrices.range G (S).patch (S).kernel (T).high n a₀ b₀ := min_le_right ..
  have hκ : 0<κ := lt_min hρ (by positivity)
  let ε := Real.exp (-κ*(till θ:ℝ))
  have hε : 0<ε := Real.exp_pos _
  have hε₁ : ε≤1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hκ.le) (by positivity))
  have hτ : Real.exp (-ρ*(till θ:ℝ))≤ε := Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_right (neg_le_neg (min_le_left ..)) (by positivity))
  let e₀ := |slip| * M
  have hE₀ : 0≤e₀ := mul_nonneg (abs_nonneg _) hM.le
  have hx : 0≤fiery G θ (S).patch.L := by unfold fiery temp; positivity
  have hu₀ : 0≤u₀ := by dsimp [u₀,ConditionalAffineLoadPrices.fullFee]; have := r.ordinary_pos; have := r.discarded_pos; positivity
  refine ⟨hδ,hM,hκ,?_⟩
  intro k q b tag F' Y Z g o l hl
  let J := rawRows T k (shorter (till θ))
  let L := rawRows T k all
  let D := columnTail T θ k
  let C (F : Forest (S).ratio) := covariance T k F (shorter (till θ))
  let H (F : Forest (S).ratio) := covariance T k F all
  let u := PhysicalAffineScalarUncut.offset T k
  let v := shortSource T θ k
  let e := sourceTail T θ
  have hfull : Paid rpos δ u₀ n u := by
    apply Paid.weaken (d:=r.spatial) _ ((min_le_left ..).trans (min_le_right ..)) le_rfl
    apply Paid.of_rays (fun i => (hv.2 d.forest k i).1)
    intro i m hm l
    apply ((hv.2 d.forest k i).2 m hm l).trans
    have hpow : (temp θ)⁻¹^m ≤ (max 1 (temp θ)⁻¹)^n :=
      (pow_le_pow_left₀ (inv_nonneg.mpr hv.1.le) (le_max_right ..) m).trans (pow_le_pow_right₀ (le_max_left ..) hm)
    exact add_le_add (mul_le_mul_of_nonneg_right hpow (mul_nonneg r.ordinary_pos.le hx)) le_rfl
  have hdisc : Paid rpos δ (ε*e₀) n e := by
    have H₀ := hTail S T hP rfl d.forest θ hv.1
    apply Paid.weaken (d:=s) (Paid.of_rays (fun i => (H₀ i).1) (fun i => (H₀ i).2))
      ((min_le_left ..).trans (min_le_left ..))
    change e₀ * Real.exp (-ρ * (till θ:ℝ)) ≤ ε * e₀
    exact (mul_le_mul_of_nonneg_left hτ hE₀).trans_eq (mul_comm e₀ ε)
  have hcFee : Paid rpos δ (u₀+e₀) n v := by
    have hcut : (fun B => u B+e B)=v := by
      funext B
      change PhysicalAffineScalarUncut.offset T k B + sourceTail T θ B = shortSource T θ k B
      rw [PhysicalAffineScalarRetainedSource.full_decomposition T θ k B]
      abel
    rw [←hcut]
    exact hfull.sum (hdisc.weaken le_rfl (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hε₁ hE₀))
  have hJ := rows_bought n a₀ b₀ T k hc hb ha hW hp hδ.le hRange (shorter (till θ)) tag
  have hL := rows_bought n a₀ b₀ T k hc hb ha hW hp hδ.le hRange all tag
  have hD := removed n a₀ b₀ T k (till θ) hc hb ha hW hδ.le hRange (min_le_right ρ (b₀/4)) tag
  let j := rowFee G (S).patch (S).kernel (T).high n a₀ b₀
  let h := inverseFee G (S).patch (S).kernel (T).high n a₀ b₀ δ
  have hC : Acts (home (G:=G) (r:=1) S) (home (G:=G) (r:=1) S) tag δ h n
      (C d.forest) (C F'.val) := by
    intro first second credit hCredit pair
    exact inverses n a₀ b₀ T k d.forest F'.val hb ha hW he hδ hRange tag F'.prop (shorter (till θ)) hCredit pair
  have hH : Acts (home (G:=G) (r:=1) S) (home (G:=G) (r:=1) S) tag δ h n
      (H d.forest) (H F'.val) := by
    intro first second credit hCredit pair
    exact inverses n a₀ b₀ T k d.forest F'.val hb ha hW he hδ hRange tag F'.prop all hCredit pair
  let t := PhysicalAffineScalarOperatorPrices.tailFee G (S).patch (S).kernel n a₀ b₀
  have hj : 0≤j := by dsimp [j,rowFee]; positivity
  have ht : 0≤t := by dsimp [t,PhysicalAffineScalarOperatorPrices.tailFee]; positivity
  have hvol := home_volume (G:=G) S 1 δ hδ
  have hV : 0≤torusPay (Bloch.Co (S).patch.L (PAC G 1)) δ := (Finset.sum_nonneg (fun _ _ => (native c₀).weight_nn ..)).trans (hvol.bound (0:Site c₀))
  have hh : 0≤h := by
    dsimp only [h,inverseFee]
    exact mul_nonneg (by positivity) (add_nonneg (le_max_left ..) (mul_nonneg (le_max_left ..) hV))
  let cost := PhysicalAffineScalarResidualPrice.price n j h t (u₀+e₀) u₀ e₀
  have hcost : 0≤cost := by
    dsimp [cost,PhysicalAffineScalarResidualPrice.price,centerFee,residualFee,forcingFee,remainderFee]; positivity
  let integrand (F : Forest (S).ratio) (B : Coarse) (i : rows) :=
    small (J B) (L B) (D B) (C F B) (H F B) (u B) (e B) i *
      (residual (J B) (C F B) (v B) i+residual (L B) (H F B) (u B) i)
  let increment := fun B i => integrand F'.val B i-integrand d.forest B i
  have purchased := PhysicalAffineScalarResidualPrice.integrand
    hJ.1 hJ.2 hL.1 hL.2 hD.1 hD.2 hC hH hcFee hfull hdisc hj hh ht (add_nonneg hu₀ hE₀) hu₀ hE₀ hε.le
  have hrow : Rooted rpos tag δ (ε*cost) n increment := purchased.2
  have ordinary : Paid rpos δ (ε*cost) n (integrand d.forest) := purchased.1
  let held := fun B : Coarse => ∑ i : rows, if rpos i=o then increment B i else 0
  let α := -(2*g^2)⁻¹
  have funded : (marks G c₀ δ).pay l o*((native c₀).weight δ o tag*|jet (ray G c₀) held l 0|)≤
      physicalVolume G (S).patch.L δ*(ε*cost) :=
    hrow.translated (mul_nonneg hε.le hcost) (row_volume S δ hδ) o l hl
  have h₀ := PhysicalAffineScalarResidualVectors.square T θ k d.forest q b Y g o hp hT (ManuscriptQLocalRootWeights.positive R d k d.forest)
  have h₁ := PhysicalAffineScalarResidualVectors.square T θ k F'.val q b Z g o hp hT (ManuscriptQLocalRootWeights.positive R d k F'.val)
  have et : ManuscriptQLocalRootPrice.error R d k q b tag F' Y Z g o=ᶠ[𝓝 0] fun B => α*held B := by
    filter_upwards [h₀,h₁] with B h₀ h₁
    have e : ManuscriptQLocalRootPrice.error R d k q b tag F' Y Z g o B=
        squareGap T θ k F'.val q b Z g o B-squareGap T θ k d.forest q b Y g o B := by
      unfold ManuscriptQLocalRootPrice.error
      exact changed_residual (PhysicalAffineScalarCutResidual.root T θ k F'.val q b Z g o B)
        (PhysicalAffineScalarCutResidual.root T θ k d.forest q b Y g o B)
    rw [e,h₀,h₁,←mul_sub,←Finset.sum_sub_distrib]
    apply congrArg (fun s => α*s)
    refine Finset.sum_congr rfl fun i _ => ?_
    change (if rpos i=o then integrand F'.val B i else 0) -
      (if rpos i=o then integrand d.forest B i else 0) =
      if rpos i=o then integrand F'.val B i - integrand d.forest B i else 0
    exact restrict_difference (rpos i=o) _ _
  have hheld₀ : ContDiffAt ℝ n held 0 := by
    apply ContDiffAt.sum; intro i _
    by_cases hi : rpos i=o
    · simp only [hi,if_true]; exact (TestD.evaluate i ()).contDiff.contDiffAt.comp 0 hrow.smooth
    · simp only [hi,if_false]; exact contDiffAt_const
  constructor
  · refine ⟨(contDiffAt_const.mul hheld₀).congr_of_eventuallyEq et,?_⟩
    have hheld := smooth_of_le hheld₀ hl
    have heq : jet (ray G c₀) (ManuscriptQLocalRootPrice.error R d k q b tag F' Y Z g o) l 0 =
        α*jet (ray G c₀) held l 0 := by
      have e : jet (ray G c₀) (ManuscriptQLocalRootPrice.error R d k q b tag F' Y Z g o) l 0=
          jet (ray G c₀) (fun B => α*held B) l 0 := by
        change iteratedFDeriv ℝ l.length _ 0 _=iteratedFDeriv ℝ l.length _ 0 _
        rw [(et.iteratedFDeriv (𝕜:=ℝ) l.length).self_of_nhds]
      exact e.trans (jet_linear (ray G c₀) l (α • ContinuousLinearMap.id ℝ ℝ) hheld)
    rw [heq,abs_mul]
    calc
      _ = |α| * ((marks G c₀ δ).pay l o*((native c₀).weight δ o tag*|jet (ray G c₀) held l 0|)) := by ring
      _ ≤ |α| * (physicalVolume G (S).patch.L δ*(ε*cost)) := mul_le_mul_of_nonneg_left funded (abs_nonneg _)
      _ = _ := by simp only [prefactor,cost,j,h,t,u₀,e₀,ε,α,abs_neg]; ring
  · have hu := Rooted.scaled_ordinary ordinary (mul_nonneg hε.le hcost) (row_volume S δ hδ) o α
        (squareGap T θ k d.forest q b Y g o) h₀ l hl
    refine ⟨hu.1,hu.2.trans_eq ?_⟩
    simp only [prefactor,cost,j,h,t,u₀,e₀,ε,α,abs_neg]; ring

end YM.Integration.ManuscriptQLocalGaussianRootPrice
