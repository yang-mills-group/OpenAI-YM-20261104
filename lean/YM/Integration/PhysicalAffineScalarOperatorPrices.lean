import YM.Integration.PhysicalAffineScalarResidualPrice
import YM.Integration.PhysicalAffineScalarOrdinaryColumns
import YM.Integration.PhysicalAffineScalarWeightChange

/-! Original row and covariance purchases used in the stationarity price.
All widths and fees are independent of the forest, translation and period. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.PhysicalAffineScalarOperatorPrices
open Function Filter Matrix Lattice Wilson RG RG.Shoot Precision Exterior Tree
open Pressure Pressure.Tube Pressure.Stores Push.SectorMeasure Push.SectorMeasure.Oriented
open Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Gaussian Next.Fluctuations.Sector
open AnalyticBridge.GaussianFieldAlignment FreeResolvent FreeResolvent.Affine FreeResolvent.TestD FreeResolvent.Mark
open PhysicalNext.Repeat.Greenbelt PhysicalAffineScalarGaussianWeights PhysicalAffineScalarResidualPrice
open ConditionalAffineForcing PhysicalAffineScalarOrdinaryColumns
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

variable (G : Gauge) (P : Patch) (K : KernelChoices) (p : Clip) (n : ℕ) (a b : ℝ)

def range := min (width G P K p (n+1) a b) (min (tier b n) (wider b n/(n+1)))
def rowFee := 2^n*max 0 (PhysicalAffineScalarOrdinaryColumns.price G P K p n a b)
def tailFee := 2^n*max 0 ((Fintype.card Signed:ℝ)*|slip| *phasePrice G P K n a b)
def inverseFee (δ : ℝ) :=
  let m := max 0 (earnings G P K p (n+1) a b+1)
  2^n*(m+m*torusPay (Bloch.Co P.L (PAC G 1)) δ)

theorem range_pos (hb : 0<b) (ha : 0≤a) : 0<range G P K p n a b := by
  have h := ordering hb n
  exact lt_min (gauged G P K p (n+1) hb ha).pos
    (lt_min h.1 (div_pos (h.1.trans_le h.2.1) (by positivity)))

private theorem fits {δ : ℝ} (h : δ≤range G P K p n a b) :
    δ≤width G P K p (n+1) a b ∧ δ≤tier b n ∧ δ+n*δ≤wider b n := by
  have h₀ := h.trans (min_le_right ..)
  refine ⟨h.trans (min_le_left ..),h₀.trans (min_le_left ..),?_⟩
  have H := (le_div_iff₀ (by positivity : 0<(n:ℝ)+1)).1 (h₀.trans (min_le_right ..))
  linarith

variable {G} {c f : Side} {S : StepData c f} (T : Tube G S) (k : S.Choices)
local notation "rows" => PhysicalAffineScalarComparison.rowRoot (G:=G) S
local notation "keys" => home (G:=G) (r:=1) S
local notation "w" => width G S.patch S.kernel T.high (n+1) a b
local notation "nativeFee" => max 0 (earnings G S.patch S.kernel T.high (n+1) a b+1)
local notation "J₀" => rowFee G S.patch S.kernel T.high n a b
local notation "D₀" => tailFee G S.patch S.kernel n a b

/-- The actual two orientations of every ordinary common cut/full signed row. -/
theorem rows_bought (hc : 1<c.val) (hs : 0<b) (ha : 0≤a) (hW : Sheet T.up b a)
    (hp : S.patch.Branches S.kernel G) {δ : ℝ} (hd : 0≤δ) (hr : δ≤range G S.patch S.kernel T.high n a b)
    (q : Admit) (z : Site c) :
    Acts keys rows z δ J₀ n (rawRows T k q) (rawRows T k q) ∧
    Acts rows keys z δ J₀ n (fun B => (rawRows T k q B).transpose) (fun B => (rawRows T k q B).transpose) := by
  have h := fits G S.patch S.kernel T.high n a b hr
  have M := (PhysicalAffineScalarOrdinaryColumns.ordinary T k q hc n hs ha hW hp hd h.2.1).mono le_rfl (le_max_right 0 _)
  exact ⟨Acts.ordinary M (le_max_left ..) hd h.2.2,Acts.ordinary M.transpose (le_max_left ..) hd h.2.2⟩

/-- The true removed Jacobian carries its native exponential once, in both
Schur orientations, with its stored sign. -/
theorem removed (R : ℕ) (hc : 1<c.val) (hs : 0<b) (ha : 0≤a) (hW : Sheet T.up b a)
    {δ κ : ℝ} (hd : 0≤δ) (hr : δ≤range G S.patch S.kernel T.high n a b) (hκ : κ≤b/4) (z : Site c) :
    let J := fun X => rawRows T k (shorter R) X-rawRows T k all X
    let ε := Real.exp (-κ*(R:ℝ))
    Acts keys rows z δ (ε*D₀) n J J ∧ Acts rows keys z δ (ε*D₀) n (fun X => (J X).transpose) (fun X => (J X).transpose) := by
  intro J ε
  have h := fits G S.patch S.kernel T.high n a b hr
  let M := max 0 ((Fintype.card Signed:ℝ)*|slip| *phasePrice G S.patch S.kernel n a b)
  have hE : Real.exp (-(b/4)*(R:ℝ))≤ε := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg hκ) (by positivity))
  have src := (PhysicalAffineScalarOrdinaryColumns.tail T k R hc n hs ha hW hd h.2.1).scale (-1)
  have cap : |(-1:ℝ)| *((Fintype.card Signed:ℝ)*(|slip| *(Real.exp (-(b/4)*(R:ℝ))*phasePrice G S.patch S.kernel n a b)))≤ε*M := by
    rw [abs_neg,abs_one,one_mul]
    calc
      _ = ((Fintype.card Signed:ℝ)*|slip| *phasePrice G S.patch S.kernel n a b)*Real.exp (-(b/4)*(R:ℝ)) := by ring
      _ ≤ M*ε := mul_le_mul (le_max_right ..) hE (Real.exp_pos ..).le (le_max_left ..)
      _ = _ := mul_comm ..
  have mat := (src.mono le_rfl cap).glue (Eventually.of_forall fun X =>
    (show (-1:ℝ) • (rawRows T k all X-rawRows T k (shorter R) X)=J X by simp only [neg_one_smul,neg_sub]; rfl))
  have H₀ : 0≤ε*M := mul_nonneg (Real.exp_pos ..).le (le_max_left ..)
  have fee : 2^n*(ε*M) = ε*D₀ := by
    dsimp only [tailFee,M]
    ring
  rw [←fee]
  exact ⟨Acts.ordinary mat H₀ hd h.2.2,Acts.ordinary mat.transpose H₀ hd h.2.2⟩

/-- The independent physically embedded inverse acts at both genuine forest
choices. One extra native slot pays the changed tree even at order n. -/
theorem inverses (F U : Forest S.ratio) (hs : 0<b) (ha : 0≤a) (hW : Sheet T.up b a)
    (he : Bid.Larger (G:=G) S) {δ : ℝ} (hd : 0<δ) (hr : δ≤range G S.patch S.kernel T.high n a b)
    (z : Site c) (hFU : changed S F U z) (q : Admit) :
    Acts keys keys z δ (inverseFee G S.patch S.kernel T.high n a b δ) n (covariance T k F q) (covariance T k U q) := by
  have h := fits G S.patch S.kernel T.high n a b hr
  have hw := (gauged G S.patch S.kernel T.high (n+1) hs ha).pos
  let γ := 4*((n+1)+1:ℕ)*w
  have common (V : Forest S.ratio) : Bundle (ray G c) (marks G c δ) (native c) keys keys (covariance T k V q) 0 n γ nativeFee := by
    have h₀ := PhysicalAffineScalarWeightChange.covariance_ordinary T k V hs ha hW he q (n+1)
    refine ⟨h₀.smooth.of_le (by exact_mod_cast Nat.le_succ n),fun l hl => ?_⟩
    have old := (h₀.bound l (hl.trans (Nat.le_succ n))).mono le_rfl (le_max_right 0 _)
    refine ⟨⟨fun i => le_trans ?_ (old.row.rows i)⟩,⟨fun j => le_trans ?_ (old.col.rows j)⟩⟩
    all_goals
      exact mul_le_mul_of_nonneg_right (ConditionalAffineRootContraction.pay_le
        (D:=native c) (p:=hearth (G:=G) (r:=1)) h.1 l _) (Finset.sum_nonneg fun _ _ =>
          mul_nonneg ((native c).weight_nn ..) (abs_nonneg _))
  have mark (l : List (raw G c)) (hl : l.length≤n) : Lever.Here (ray G c) (native c) keys hearth w γ z l nativeFee
      (covariance T k F q) (covariance T k U q) := by
    have h₀ := PhysicalAffineScalarWeightChange.covariance_price T k F U hs ha hW he hFU q (n:=n+1) l (Nat.lt_succ_of_le hl)
    refine ⟨fun i j => ?_⟩
    have M : earnings G S.patch S.kernel T.high (n+1) a b+(if l=[] then 1 else 0)≤nativeFee := by
      apply le_trans _ (le_max_right ..); split_ifs <;> linarith
    exact ⟨((h₀.test i j).1.trans M),((h₀.test i j).2.trans M)⟩
  have γh : δ+n*δ≤γ := by
    have h₀ := mul_le_mul_of_nonneg_left h.1 (by positivity : (0:ℝ)≤n)
    dsimp [γ]; push_cast; nlinarith only [h.1,h₀,hw,(by positivity : (0:ℝ)≤n*w)]
  have hV := home_volume (G:=G) S 1 δ hd
  intro V W price hp pair
  exact Acts.inverse (common F) (common U) mark (le_max_left ..) (le_max_left ..) hd.le h.1 γh hV
    ((Finset.sum_nonneg (fun _ _ => (native c).weight_nn ..)).trans (hV.bound (0:Site c))) hp pair

end YM.Integration.PhysicalAffineScalarOperatorPrices
