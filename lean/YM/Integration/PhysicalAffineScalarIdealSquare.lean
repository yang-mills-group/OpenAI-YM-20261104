import YM.Integration.PhysicalAffineScalarIdealGrading
import YM.Integration.ManuscriptQLocalGaussianRootPrice
import YM.Integration.ManuscriptQLocalStationaryScalar
import YM.Integration.PhysicalAffineScalarSpectralRoot

/-! Absolute uncut stationary square.  Its source and its full load carry
a fixed pre-period purchase. The fine coupling is reinserted only after
the first derivative of the actual physical held residual has vanished. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.PhysicalAffineScalarIdealSquare
open Function Filter Matrix Lattice Wilson RG RG.Shoot Tree Precision Exterior
open Pressure Supply Pressure.Testing Pressure.Tube Pressure.Stores Push.SectorMeasure Push.SectorMeasure.Oriented
open Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Gaussian Next.Fluctuations.Sector
open AnalyticBridge.GaussianFieldAlignment FreeResolvent FreeResolvent.Affine FreeResolvent.TestD FreeResolvent.Mark
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Progress.DirectedRecipe
open PhysicalAffineScalarRootContraction PhysicalAffineScalarChangedFields PhysicalAffineScalarOperatorPrices
open ConditionalAffineForcing ConditionalAffineLoadPrices ConditionalAffineMeanDifference
open PhysicalAffineScalarAperture (noHole)
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {c f : Side} {S : StepData c f} (T : Tube G S) (k : S.Choices)
local notation "E" => Vec G c 1
local notation "rp" => PhysicalAffineScalarComparison.rowRoot (G:=G) S
local notation "E₁" => PhysicalAffineScalarUncut.offset T k
local notation "J" => rawRows T k all

/-- Full physical square on its native raw signed row array. -/
def residual (F : Forest S.ratio) (B : E) := E₁ B -
  (J B) *ᵥ (PhysicalAffineScalarGaussianWeights.covariance T k F all B *ᵥ wholeLoad T k B)

def mass (F : Forest S.ratio) (o : Site c) (B : E) :=
  ∑ i : Rows.Receipt G S, if rp i=o then residual T k F B i*residual T k F B i else 0

theorem matrix (B : E) : PhysicalAffineScalarProjection.responseMatrix T k B=J B := by
  ext i j
  rw [PhysicalAffineScalarProjection.responseMatrix,LinearMap.toMatrix'_apply]
  rfl

/-- Both entries are defined independently on the original affine problem.
The off-shell identity is removed from the genuine spectral inverse. -/
theorem physical (F : Forest S.ratio) (B : E) (h : (primary S F k T.high T.up all B).PosDef) :
    residual T k F B = PhysicalAffineScalarSpectralRoot.retained T k F B := by
  rw [residual,PhysicalAffineScalarSpectralRoot.retained,PhysicalAffineScalarProjection.inputForcing,
    matrix,PhysicalAffineScalarGaussianWeights.spectral T k F all B (IsUnit.mk0 _ h.det_pos.ne')]
  rfl

theorem zero (hp : S.patch.Branches S.kernel G) (F : Forest S.ratio) : residual T k F 0=0 := by
  simp [residual,wholeLoad,PhysicalAffineScalarUncut.offset_zero T k hp]

def rowCost (j h C : ℝ) := C+j*(h*C)

/-- All independent field and actual one-site tree perturbations reach the
original physical uncut residual through exactly its deposited inverse. -/
theorem vectors {n : ℕ} {δ C σ A : ℝ} (hδ : 0<δ) (hC : 0≤C) (hc : 1<c.val)
    (hσ : 0<σ) (hA : 0≤A) (hW : Sheet T.up σ A) (he : Bid.Larger (G:=G) S)
    (hr : δ≤range G S.patch S.kernel T.high n A σ) (F U : Forest S.ratio)
    (z : Site c) (htu : changed S F U z) (hsource : Paid rp δ C n (PhysicalAffineScalarUncut.offset T k))
    (hload : Paid (home S) δ C n (wholeLoad T k)) :
    let j := rowFee G S.patch S.kernel T.high n A σ
    let h := inverseFee G S.patch S.kernel T.high n A σ δ
    Pair rp z δ (rowCost j h C) n (residual T k F) (residual T k U) := by
  intro j h
  have hj := rows_bought n A σ T k hc hσ hA hW he.1 hδ.le hr all z
  have hh := inverses n A σ T k F U hσ hA hW he hδ hr z htu all hC (Pair.same hload hC)
  have volume := home_volume (G:=G) S 1 δ hδ
  have hv : 0≤torusPay (Bloch.Co S.patch.L (PAC G 1)) δ :=
    (Finset.sum_nonneg fun _ _ => (native c).weight_nn ..).trans (volume.bound (0:Site c))
  have hn : 0≤h := by dsimp [h,inverseFee]; positivity
  exact (Pair.same hsource hC).diff (hj.1 (mul_nonneg hn hC) hh)

theorem positions {n : ℕ} {δ C : ℝ} (hδ : 0<δ) (hC : 0≤C)
    (F U : Forest S.ratio) (z : Site c)
    (H : Pair rp z δ C n (residual T k F) (residual T k U)) (o : Site c)
    (l : List (raw G c)) (hl : l.length≤n) :
    let K := (2:ℝ)^n*(C*C)
    (marks G c δ).pay l o*|jet (ray G c) (mass T k F o) l 0|≤physicalVolume G S.patch.L δ*K ∧
    (marks G c δ).pay l o*((native c).weight δ o z*
      |jet (ray G c) (fun B => mass T k U o B-mass T k F o B) l 0|)≤physicalVolume G S.patch.L δ*(K+K) := by
  intro K
  have hK : 0≤K := by dsimp [K]; positivity
  have H₁ := Rooted.ordinary_product H.left H.left hC hC
  have H₂ := H.changed_product H hC hC
  refine ⟨Rooted.ordinary_root H₁ hK (row_volume S δ hδ) o l hl,?_⟩
  have hdiff : (fun b => mass T k U o b-mass T k F o b) =
      (fun b => ∑ i : Rows.Receipt G S, if rp i=o then
        residual T k U b i*residual T k U b i-residual T k F b i*residual T k F b i else 0) := by
    funext b; unfold mass; rw [←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro i _; split_ifs <;> simp
  rw [hdiff]
  exact Rooted.translated H₂ (add_nonneg hK hK) (row_volume S δ hδ) o l hl

/-- A single uniform uncut-source and deposited-Jacobian fee which applies
to every actual geometric choice and all periodic copies. -/
def Voucher (S : StepData c f) (T : Tube G S) (n : ℕ) (δ C : ℝ) := ∀ k : S.Choices,
  ∀ (F U : Forest S.ratio) (z : Site c), changed S F U z →
    Pair (PhysicalAffineScalarComparison.rowRoot (G:=G) S) z δ C n (residual T k F) (residual T k U)

theorem purchased (G : Gauge) (P : Patch) (Pt : Teller G) (hP : P.Branches Pt.bind G) (n : ℕ) :
    ∃ δ C : ℝ, ∃ R : ℕ, 0<δ ∧ 0<C ∧ ∀ {c f : Side} (S : StepData c f) (T : Tube G S),
      S.patch=P → Pt.Funds S T → 100*(1+R)≤c.val → Voucher S T n δ C := by
  obtain ⟨u,D,R,hu,hD,H⟩ := ConditionalAffineLoadPrices.whole_ordinary G P Pt hP n
  let a := Pt.top.paths
  let b := Pt.top.width
  let δ := min u (range G P Pt.bind Pt.top.clip n a b)
  have hd : 0<δ := lt_min hu (range_pos G P Pt.bind Pt.top.clip n a b Pt.top.width_pos Pt.top.paths_pos.le)
  let j := rowFee G P Pt.bind Pt.top.clip n a b
  let h := inverseFee G P Pt.bind Pt.top.clip n a b δ
  let C := |rowCost j h D|+1
  let R₀ := max R (macroR P)
  refine ⟨δ,C,R₀,hd,by dsimp [C]; positivity,?_⟩
  intro c f S T hS hT hsize k F U z e
  have hR : 100*(1+R)≤c.val := le_trans (by dsimp only [R₀]; gcongr; exact le_max_left ..) hsize
  have hmac : 100*macroR P≤c.val := by have H' : macroR P≤R₀ := le_max_right ..; omega
  have he : Bid.Larger (G:=G) S := ⟨hT.knobs.symm ▸ hT.kernel,by
    rw [hS,S.ratio.exact_size]; exact hmac.trans (Nat.le_mul_of_pos_right _ S.ratio.count.property),by omega⟩
  obtain ⟨_,_,hW,_⟩ := hT.feeds
  have hr : δ≤range G S.patch S.kernel T.high n a b := by rw [hS,hT.knobs,hT.high]; exact min_le_right ..
  obtain ⟨hf,hload⟩ := H S T hS hT hR F k
  apply (vectors T k hd hD.le (by omega) Pt.top.width_pos Pt.top.paths_pos.le hW.rows he hr F U z e
    (hf.weaken (min_le_left ..) le_rfl) (hload.weaken (min_le_left ..) le_rfl)).mono_fee
  rw [hS,hT.knobs,hT.high]
  exact (le_abs_self _).trans (le_add_of_nonneg_right zero_le_one)

end YM.Integration.PhysicalAffineScalarIdealSquare
