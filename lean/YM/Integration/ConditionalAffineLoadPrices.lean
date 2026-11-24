import YM.Integration.ConditionalAffineRootContraction
import YM.Integration.PhysicalAffineScalarGaussianWeights
import YM.Integration.PhysicalAffineScalarRetainedSource
import YM.Integration.PhysicalAffineScalarOrdinaryColumns

/-! The actual empty-sector mean variation on common physical keys. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ConditionalAffineMeanDifference
open Function Filter Set Lattice Wilson RG Precision Exterior Tree Matrix
open Pressure Pressure.Tube Pressure.Stores Push.SectorMeasure Push.SectorMeasure.Oriented
open Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Gaussian Next.Fluctuations.Sector
open FreeResolvent FreeResolvent.Affine FreeResolvent.TestD AnalyticBridge.GaussianFieldAlignment
open PhysicalNext.Repeat.Greenbelt ConditionalTreeCovarianceJets
open PhysicalAffineScalarAperture (noHole)
open PhysicalAffineScalarCutResidual (shortSource)
open ConditionalAffineForcing (rawRows)
open PhysicalAffineScalarGaussianWeights (covariance)
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {c f : Side} {S : StepData c f} {σ K Λ : ℝ}
variable (T : Tube G S) (x : ℝ) (k : S.Choices)
local notation "Coarse" => Gaussian.Vec (Raw G c)
local notation "V" => fun B : Coarse => represent (decode B)
local notation "A" => noHole S
local notation "short" => shorter (till x)

def shortLoad (B : Coarse) :=
  (rawRows T k short B).transpose *ᵥ shortSource T x k B

def wholeLoad (B : Coarse) :=
  (rawRows T k all B).transpose *ᵥ PhysicalAffineScalarUncut.offset T k B

def error (r : Reserve S) (q : Chi) (d : ℝ) (Y : LinkArray G (Frozen A x (allot r))) (B : Coarse) :=
  insertion (address A (allot r) x) *ᵥ (meanLog A (allot r) T x (V B) k q d Y -
    PhysicalAffineScalarUncut.center T x k (allot r) B)

private theorem extend {ι κ : Type*} [Fintype ι] [Fintype κ] (I : Matrix ι κ ℝ) (Q : Matrix κ κ ℝ)
    (b : ι → ℝ) : I *ᵥ (-(Q *ᵥ (I.transpose *ᵥ b))) = -((I*Q*I.transpose) *ᵥ b) := by
  simp only [Matrix.mulVec_neg,Matrix.mulVec_mulVec,Matrix.mul_assoc]

def fullCenter (F : Forest S.ratio) (B : Coarse) :=
  insertion (address A F x) *ᵥ PhysicalAffineScalarUncut.center T x k F B

/-- The true independent ideal mean uses the uncut density's entire common raw
force. Its deposited value is independent of the chosen no-hole radius chart. -/
theorem full_center (F : Forest S.ratio) (h : S.patch.Branches S.kernel G) (hT : T.up.Bounds T.high σ K Λ) :
    fullCenter T x k F =ᶠ[𝓝 0] fun B => -(covariance T k F all B *ᵥ wholeLoad T k B) := by
  let e := address (G:=G) A F x
  let I := insertion e
  filter_upwards [PhysicalAffineScalarGaussianWeights.deposited T x k F h hT] with B hB
  have hd : PhysicalAffineScalarUncut.columns T x k F B=ConditionalAffineForcing.rawRows T k all B*I :=
    (ConditionalAffineForcing.original_column T k F x B).trans (insertion.mul e _).symm
  change I *ᵥ (-((PhysicalAffineScalarUncut.gram T x k F B)⁻¹ *ᵥ
    ((PhysicalAffineScalarUncut.columns T x k F B).transpose *ᵥ PhysicalAffineScalarUncut.offset T k B))) = _
  rw [hd,Matrix.transpose_mul,←Matrix.mulVec_mulVec,extend,hB.2]
  rfl

/-- The two common loads are forest independent before differentiation. -/
theorem original (r : Reserve S) (hx : 120 ≤ radiusB x) (q : Chi) (d : ℝ)
    (Y : LinkArray G (Frozen A x (allot r))) (h : S.patch.Branches S.kernel G)
    (he : Bid.Larger (G:=G) S) (hs : 0<σ) (hK : 0≤K) (hT : T.up.Bounds T.high σ K Λ) :
    error T x k r q d Y =ᶠ[𝓝 0] fun B =>
      -(ConditionalAffinePanelWindow.columns .adjoint x hx (till x) r k T.high T.up 0 B *ᵥ shortLoad T x k B) -
      covariance T k (allot r) all B *ᵥ (shortLoad T x k B - wholeLoad T k B) := by
  let F := allot r
  let I := insertion (address (G:=G) A F x)
  let η := headGap G S.patch S.kernel T.high
  have hη : 0<η := headGap_pos ..
  have H := knows F k hs hK (path_sheet T hT) he T.high 0 all
  have hh := AnalyticBridge.RelativeLogdet.Differential.holds H.smooth.continuousAt H.gap (η/2)
    (by dsimp [η]; linarith) (native c) (theta S.ratio F)
  filter_upwards [hh,ConditionalAffinePanelWindow.physical F x hx T k h he hs hK hT,
    PhysicalAffineScalarGaussianWeights.loads T x k F q d Y h hT,
    PhysicalAffineScalarGaussianWeights.deposited T x k F h hT] with B hgap hp ⟨hc,hw⟩ hd
  let C := covariance T k F all B
  let P := Schur.per (panels A F) (Rows.gram T x (V B) k (shots S x) A F)
  let E := ConditionalAffinePanelWindow.columns .adjoint x hx (till x) r k T.high T.up 0 B
  have hi := PhysicalAffineScalarGaussianWeights.spectral T k F all B (hgap.unit_det (half_pos hη))
  have hP : I*P.transpose*I.transpose = E+C := by
    rw [show E = _ from ConditionalAffinePanelWindow.adjoint_columns x hx (till x) r B,
      hp,show C=_ from hi]
    change _ = (fill (address A F x) P).transpose - action (whole S F k T.high T.up all) 0 B +
      (action (whole S F k T.high T.up all) 0 B - Shell.off (freeTo G S F))
    rw [fill,Matrix.transpose_add,Matrix.transpose_mul,Matrix.transpose_mul,Matrix.transpose_transpose,Shell.undo]
    rw [show Shell.off (address (G:=G) A F x)=Shell.off (freeTo G S F) from
      congrArg (fun M => 1-M) (ConditionalAffinePanelWindow.same_rim F x)]
    dsimp only [I]; rw [Matrix.mul_assoc]; abel
  have a : I *ᵥ meanLog A F T x (V B) k q d Y = -((E+C) *ᵥ shortLoad T x k B) := by
    rw [meanLog,hc,Matrix.neg_mulVec,extend,hP]
    rfl
  have b : I *ᵥ PhysicalAffineScalarUncut.center T x k F B = -(C *ᵥ wholeLoad T k B) := by
    change I *ᵥ (-((PhysicalAffineScalarUncut.gram T x k F B)⁻¹ *ᵥ (_ *ᵥ _))) = _
    rw [hw,extend,hd.2]
    rfl
  change I *ᵥ (_-_) = _
  rw [Matrix.mulVec_sub,a,b,Matrix.add_mulVec,Matrix.mulVec_sub]
  abel

/-- One actual physical forest draw varies only the two stated tensors. -/
theorem one_tag (r s : Reserve S) (hx : 120 ≤ radiusB x) (q : Chi) (d : ℝ)
    (Y : LinkArray G (Frozen A x (allot r))) (Z : LinkArray G (Frozen A x (allot s)))
    (h : S.patch.Branches S.kernel G) (he : Bid.Larger (G:=G) S) (hs : 0<σ)
    (hK : 0≤K) (hT : T.up.Bounds T.high σ K Λ) :
    (fun B => error T x k s q d Z B-error T x k r q d Y B) =ᶠ[𝓝 0] fun B =>
      -((ConditionalAffinePanelWindow.columns .adjoint x hx (till x) s k T.high T.up 0 B -
        ConditionalAffinePanelWindow.columns .adjoint x hx (till x) r k T.high T.up 0 B) *ᵥ shortLoad T x k B) -
      (covariance T k (allot s) all B - covariance T k (allot r) all B) *ᵥ (shortLoad T x k B-wholeLoad T k B) := by
  filter_upwards [original T x k r hx q d Y h he hs hK hT,
    original T x k s hx q d Z h he hs hK hT] with B hR hS
  rw [hR,hS,Matrix.sub_mulVec,Matrix.sub_mulVec]
  abel

end YM.Integration.ConditionalAffineMeanDifference

/-! The true raw cut and whole loads, estimated before a physical forest draw. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ConditionalAffineLoadPrices
open Function Filter Set Lattice Wilson RG Precision Tree Matrix
open FreeResolvent FreeResolvent.Affine FreeResolvent.TestD FreeResolvent.Mark
open Pressure Pressure.Tube Pressure.Stores AnalyticBridge.GaussianFieldAlignment
open Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Gaussian
open PhysicalAffineScalarOrdinaryColumns
open PhysicalAffineScalarCutResidual (shortSource)
open ConditionalAffineForcing (rawRows)
open ConditionalAffineMeanDifference (shortLoad wholeLoad)
open scoped BigOperators Classical ContDiff Topology Matrix.Norms.Frobenius
variable {G : Gauge} {c fSide : Side} {S : StepData c fSide} {ι κ : Type*} [Fintype ι] [Fintype κ]
local notation "ray₀" => FreeResolvent.Affine.ray G c

def column (F : FreeResolvent.Vec G c 1 → ι → ℝ) (x : FreeResolvent.Vec G c 1) : Matrix ι Unit ℝ := fun i _ => F x i

structure Paid (p : ι → Site c) (δ C : ℝ) (n : ℕ) (F : FreeResolvent.Vec G c 1 → ι → ℝ) : Prop where
  smooth : ContDiffAt ℝ n (column (G:=G) (c:=c) (ι:=ι) F) 0
  rows (l : List (raw G c)) (hl : l.length ≤ n) (i : ι) :
    (marks G c δ).pay l (p i)*|jet ray₀ (column (G:=G) (c:=c) (ι:=ι) F) l 0 i ()| ≤ C

namespace Paid
variable {p : ι → Site c} {q : κ → Site c} {δ d C C' M γ : ℝ} {n : ℕ} {F H : FreeResolvent.Vec G c 1 → ι → ℝ}

theorem of_rays (hs : ∀ i : ι, ContDiffAt ℝ n (fun B : FreeResolvent.Vec G c 1 => F B i) 0)
    (hh : ∀ (i : ι) (m : ℕ), m ≤ n → ∀ l : Fin m → raw G c,
      Real.exp (δ*Stars.rays (native c) (p i) (hearth∘l))*
        |iteratedFDeriv ℝ m (fun B : FreeResolvent.Vec G c 1 => F B i) 0 (ray₀∘l)| ≤ C) : Paid (G:=G) p δ C n F := by
  have sm : ContDiffAt ℝ n (column (G:=G) (c:=c) (ι:=ι) F) 0 := TestD.rectangle_smooth (fun i _ => hs i)
  refine ⟨sm,fun l hl i => ?_⟩
  have hz := TestD.entry ray₀ l (smooth_of_le sm hl) i ()
  change jet ray₀ (fun b => F b i) l 0 = _ at hz
  rw [←hz]
  have hm : (marks G c δ).pay l (p i)=Real.exp (δ*Stars.rays (native c) (p i) (hearth ∘ l.get)) := by
    simpa using Stars.pays (native c) (p i) δ hearth l.get
  rw [hm]
  exact hh i l.length hl l.get

theorem weaken (h : Paid (G:=G) p d C n F) (hd : δ ≤ d) (hm : C ≤ M) : Paid (G:=G) p δ M n F := by
  refine ⟨h.smooth,fun l hl i => ?_⟩
  exact (mul_le_mul_of_nonneg_right (ConditionalAffineRootContraction.pay_le (D:=native c) (p:=hearth) hd l (p i))
    (abs_nonneg _)).trans ((h.rows l hl i).trans hm)

theorem negative (h : Paid (G:=G) p δ C n F) : Paid (G:=G) p δ C n (fun B : FreeResolvent.Vec G c 1 => -(F B)) := by
  refine ⟨h.smooth.neg,fun l hl i => ?_⟩
  have H : jet ray₀ (fun B : FreeResolvent.Vec G c 1 => -(column (G:=G) (c:=c) (ι:=ι) F B)) l 0 = -(jet ray₀ (column (G:=G) (c:=c) (ι:=ι) F) l 0) :=
    DFunLike.congr_fun (iteratedFDeriv_neg_apply (𝕜:=ℝ) (f:=column (G:=G) (c:=c) (ι:=ι) F) (i:=l.length) (x:=0)) (ray₀ ∘ l.get)
  change _*|jet ray₀ (fun B : FreeResolvent.Vec G c 1 => -(column (G:=G) (c:=c) (ι:=ι) F B)) l 0 i ()| ≤ _
  rw [H,Matrix.neg_apply,abs_neg]
  exact h.rows l hl i

theorem germ (h : Paid (G:=G) p δ C n F) (he : H=ᶠ[𝓝 0] F) : Paid (G:=G) p δ C n H := by
  have hc : column (G:=G) (c:=c) (ι:=ι) H=ᶠ[𝓝 0] column (G:=G) (c:=c) (ι:=ι) F := by
    filter_upwards [he] with b hb
    change (fun (i : ι) (_ : Unit)=>H b i)=(fun (i : ι) (_ : Unit)=>F b i)
    rw [hb]
  refine ⟨h.smooth.congr_of_eventuallyEq hc,fun l hl i => ?_⟩
  rw [TestD.identical ray₀ hc l]
  exact h.rows l hl i

theorem matrix_weaken {J : FreeResolvent.Vec G c 1 → Matrix κ ι ℝ} {m : ℕ}
    (h : Bundle ray₀ (marks G c d) (native c) q p J 0 m γ M) (hd : δ ≤ d) (hn : n ≤ m) :
    Bundle ray₀ (marks G c δ) (native c) q p J 0 n γ M := by
  refine ⟨smooth_of_le h.smooth hn,fun l hl => ?_⟩
  have hh := h.bound l (hl.trans hn)
  constructor
  · constructor; intro i
    exact (mul_le_mul_of_nonneg_right
      (ConditionalAffineRootContraction.pay_le (D:=native c) (p:=hearth) hd l (q i))
      (Finset.sum_nonneg fun j _ => mul_nonneg ((native c).weight_nn ..) (abs_nonneg _))).trans (hh.row.rows i)
  · constructor; intro i
    exact (mul_le_mul_of_nonneg_right
      (ConditionalAffineRootContraction.pay_le (D:=native c) (p:=hearth) hd l (p i))
      (Finset.sum_nonneg fun j _ => mul_nonneg ((native c).weight_nn ..) (abs_nonneg _))).trans (hh.col.rows i)


theorem matrix_cost {J : FreeResolvent.Vec G c 1 → Matrix κ ι ℝ} {N : ℝ}
    (h : Bundle ray₀ (marks G c δ) (native c) q p J 0 n γ M) (hm : M ≤ N) :
    Bundle ray₀ (marks G c δ) (native c) q p J 0 n γ N :=
  ⟨h.smooth,fun l hl => (h.bound l hl).mono le_rfl hm⟩

theorem sum (h : Paid (G:=G) p δ C n F) (h' : Paid (G:=G) p δ C' n H) : Paid (G:=G) p δ (C+C') n (fun B : FreeResolvent.Vec G c 1 => F B+H B) := by
  refine ⟨h.smooth.add h'.smooth,fun l hl i => ?_⟩
  change _*|(jet ray₀ (fun B : FreeResolvent.Vec G c 1 => column (G:=G) (c:=c) (ι:=ι) F B+column (G:=G) (c:=c) (ι:=ι) H B) l 0 : Matrix ι Unit ℝ) i ()| ≤ _
  rw [jet_add ray₀ l (smooth_of_le h.smooth hl) (smooth_of_le h'.smooth hl),Matrix.add_apply]
  exact (mul_le_mul_of_nonneg_left (abs_add_le ..) ((marks G c δ).pay_pos ..).le).trans
    ((mul_add ..).le.trans (add_le_add (h.rows l hl i) (h'.rows l hl i)))

theorem diff (h : Paid (G:=G) p δ C n F) (h' : Paid (G:=G) p δ C' n H) : Paid (G:=G) p δ (C+C') n (fun B : FreeResolvent.Vec G c 1 => F B-H B) := by
  refine ⟨h.smooth.sub h'.smooth,fun l hl i => ?_⟩
  change _*|(jet ray₀ (fun B : FreeResolvent.Vec G c 1 => column (G:=G) (c:=c) (ι:=ι) F B-column (G:=G) (c:=c) (ι:=ι) H B) l 0 : Matrix ι Unit ℝ) i ()| ≤ _
  rw [jet_sub ray₀ l (smooth_of_le h.smooth hl) (smooth_of_le h'.smooth hl),Matrix.sub_apply]
  exact (mul_le_mul_of_nonneg_left (by simpa only [sub_zero,zero_sub,abs_neg] using abs_sub_le _ (0:ℝ) _) ((marks G c δ).pay_pos ..).le).trans
    ((mul_add ..).le.trans (add_le_add (h.rows l hl i) (h'.rows l hl i)))

theorem action (hF : Paid (G:=G) p δ C n F) (hC : 0 ≤ C) {J : FreeResolvent.Vec G c 1 → Matrix κ ι ℝ}
    (hJ : Bundle ray₀ (marks G c δ) (native c) q p J 0 n γ M)
    (hM : 0 ≤ M) (hδ : 0 ≤ δ) (hγ : n*δ ≤ γ) :
    Paid (G:=G) q δ (2^n*(C*M)) n (fun b => J b *ᵥ F b) := by
  have hs : (column (G:=G) (c:=c) (ι:=κ) (fun b : FreeResolvent.Vec G c 1 => J b *ᵥ F b)) = fun b => J b*column (G:=G) (c:=c) (ι:=ι) F b := rfl
  constructor
  · rw [hs]; exact prod_smooth hJ.smooth hF.smooth
  intro l hl i
  rw [hs,jet_mul ray₀ l (smooth_of_le hJ.smooth hl) (smooth_of_le hF.smooth hl),Matrix.sum_apply]
  let P := marks G c δ
  have H (m : Masks l) : P.pay l (q i)*
      |(jet ray₀ J (lo l m) 0 * jet ray₀ (column (G:=G) (c:=c) (ι:=ι) F) (hi l m) 0) i ()| ≤ C*M := by
    have hu := (len_high l m).trans hl
    let e : Unit → Site c := fun _ => 0
    have hcol : P.Rates (native c) p e (hi l m) 0 C (jet ray₀ (column (G:=G) (c:=c) (ι:=ι) F) (hi l m) 0) := by
      constructor; intro j
      simpa only [Fintype.sum_unique,Cost.weight_zero,one_mul] using hF.rows (hi l m) hu j
    have hh := (hJ.bound (lo l m) ((len_low l m).trans hl)).row.mul
      (position_move (native c) hearth hδ) zero_le_one (le_refl (0:ℝ))
      (show 0+(hi l m).length*δ ≤ γ from by rw [zero_add]; exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hu) hδ).trans hγ)
      (P.pay_masks l m) hcol hC
    simpa only [Fintype.sum_unique,Cost.weight_zero,one_mul,one_pow] using hh.rows i
  calc
    _ ≤ P.pay l (q i)*∑ m : Masks l, |(jet ray₀ J (lo l m) 0*jet ray₀ (column (G:=G) (c:=c) (ι:=ι) F) (hi l m) 0) i ()| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs ..) (P.pay_pos ..).le
    _ ≤ 2^l.length*(C*M) := by
      rw [Finset.mul_sum]
      exact (Finset.sum_le_sum (fun m _ => H m)).trans_eq (by simp [TestD.card,nsmul_eq_mul])
    _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hl) (mul_nonneg hC hM)

end Paid

def fullFee (G : Gauge) (L : Side) (n : ℕ) (N D ρ x : ℝ) :=
  (max 1 (temp x)⁻¹)^n*(N*fiery G x L)+(|slip| *D)*Real.exp (-ρ*(till x:ℝ))

def sourceFee (D ρ x : ℝ) := (|slip| *D)*Real.exp (-ρ*(till x:ℝ))

def jacFee (G : Gauge) (P : Patch) (Pt : Teller G) (n : ℕ) := max 0
  (price G P Pt.bind Pt.top.clip n Pt.top.paths Pt.top.width)

def jacTail (G : Gauge) (P : Patch) (Pt : Teller G) (n : ℕ) (x : ℝ) :=
  (max 0 ((Fintype.card Signed:ℝ)*|slip| *phasePrice G P Pt.bind n Pt.top.paths Pt.top.width))*
    Real.exp (-(Pt.top.width/4)*(till x:ℝ))

def ordinaryFee (G : Gauge) (P : Patch) (Pt : Teller G) (n : ℕ) (N D D' x : ℝ) :=
  let ρ := ConditionalAffineSourcePrices.rate Pt P.L
  2^n*((fullFee G P.L n N D ρ x+sourceFee D' ρ x)*jacFee G P Pt n)

def tailFee (G : Gauge) (P : Patch) (Pt : Teller G) (n : ℕ) (N D D' x : ℝ) :=
  let ρ := ConditionalAffineSourcePrices.rate Pt P.L
  2^n*(sourceFee D' ρ x*jacFee G P Pt n)+2^n*(fullFee G P.L n N D ρ x*jacTail G P Pt n x)

/-- Two exact matrix-vector products purchase the actual common load and its
cutoff variation. Cost is selected before every physical period and forest. -/
theorem charges (G : Gauge) (P : Patch) (Pt : Teller G) (hp : P.Branches Pt.bind G) (n : ℕ) :
    ∃ δ N D D' : ℝ, 0<δ ∧ 0<N ∧ 0<D ∧ 0<D' ∧ ∀ᶠ x : ℝ in atTop,
      ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch=P → Pt.Funds S T → 100*(1+radiusB x) ≤ c.val → 0<temp x → ∀ (_ : Forest S.ratio) (k : S.Choices),
        Paid (G:=G) (home S) δ (ordinaryFee G P Pt n N D D' x) n (shortLoad T x k) ∧
        Paid (G:=G) (home S) δ (tailFee G P Pt n N D D' x) n (fun B => shortLoad T x k B-wholeLoad T k B) := by
  obtain ⟨u,N,D,hu,hN,hD,H⟩ := PhysicalAffineScalarRetainedSource.full G P Pt hp n
  obtain ⟨v,D',hv,hD',hρ,H'⟩ := PhysicalAffineScalarInputPrices.source G Pt P.L n
  let b := Pt.top.width
  let δ := min (min u v) (tier b n)
  have hb : 0<b := Pt.top.width_pos
  have ha := Pt.top.paths_pos.le
  have orders := ordering hb n
  have hδ : 0<δ := lt_min (lt_min hu hv) orders.1
  have he : δ ≤ tier b n := min_le_right ..
  have hν : n*δ ≤ wider b n := by
    have h := mul_le_mul_of_nonneg_left he (by positivity : (0:ℝ) ≤ n)
    unfold wider; linarith [orders.1]
  refine ⟨δ,N,D,D',hδ,hN,hD,hD',?_⟩
  filter_upwards [H] with x hx
  intro c f S T hS hT ht hθ F k
  let ρ := ConditionalAffineSourcePrices.rate Pt P.L
  let p := PhysicalAffineScalarComparison.rowRoot (G:=G) S
  let C := fullFee G P.L n N D ρ x
  let D₀ := sourceFee D' ρ x
  let J₀ := jacFee G P Pt n
  let J₁ := jacTail G P Pt n x
  let R := till x
  have hfire : 0 ≤ fiery G x P.L := by unfold fiery temp; positivity
  have hC : 0 ≤ C := by dsimp [C,fullFee]; positivity
  have hD₀ : 0 ≤ D₀ := by dsimp [D₀,sourceFee]; positivity
  have hJ₀ : 0 ≤ J₀ := le_max_left ..
  have hJ₁ : 0 ≤ J₁ := mul_nonneg (le_max_left ..) (Real.exp_pos _).le
  have hF := hx S T hS hT ht hθ F k
  have hDtrue := H' S T hT (by rw [hS]) F x hθ
  have whole : Paid (G:=G) p δ C n (PhysicalAffineScalarUncut.offset T k) := by
    apply Paid.weaken (G:=G) (c:=c) (p:=p) (F:=PhysicalAffineScalarUncut.offset T k) (C:=C) (d:=u) _ ((min_le_left ..).trans (min_le_left ..)) le_rfl
    apply Paid.of_rays (G:=G) (c:=c) (p:=p) (F:=PhysicalAffineScalarUncut.offset T k) (fun i => (hF i).1)
    intro i m hm l
    apply ((hF i).2 m hm l).trans
    have hpow : (temp x)⁻¹^m ≤ (max 1 (temp x)⁻¹)^n :=
      (pow_le_pow_left₀ (inv_nonneg.mpr hθ.le) (le_max_right ..) m).trans
        (pow_le_pow_right₀ (le_max_left ..) hm)
    exact add_le_add (mul_le_mul_of_nonneg_right hpow (mul_nonneg hN.le hfire)) le_rfl
  have defect : Paid (G:=G) p δ D₀ n (PhysicalAffineScalarCutWeights.sourceTail T x) := by
    apply Paid.weaken (G:=G) (c:=c) (p:=p) (F:=PhysicalAffineScalarCutWeights.sourceTail T x) (C:=D₀) (d:=v) _ ((min_le_left ..).trans (min_le_right ..)) le_rfl
    exact Paid.of_rays (G:=G) (c:=c) (p:=p) (F:=PhysicalAffineScalarCutWeights.sourceTail T x) (fun i => (hDtrue i).1) (fun i => (hDtrue i).2)
  have hsource : (fun B => PhysicalAffineScalarUncut.offset T k B+PhysicalAffineScalarCutWeights.sourceTail T x B) =
      shortSource T x k := by
    funext B; rw [PhysicalAffineScalarRetainedSource.full_decomposition T x k B]; abel
  have short := whole.sum defect
  rw [hsource] at short
  obtain ⟨m,y,H₁,H₂⟩ := hT.feeds
  have hW : Sheet T.up b Pt.top.paths := H₁.rows
  have hc : 1<c.val := by omega
  have hh : S.patch.Branches S.kernel G := hT.knobs.symm ▸ hT.kernel
  have U := PhysicalAffineScalarOrdinaryColumns.ordinary T k (shorter R) hc n hb ha hW hh hδ.le he
  have V := PhysicalAffineScalarOrdinaryColumns.tail T k R hc n hb ha hW hδ.le he
  have hU := U.transpose.mono le_rfl (show price G S.patch S.kernel T.high n Pt.top.paths b ≤ J₀ from by
    rw [hS,hT.knobs,hT.high]; exact le_max_right ..)
  have hV := V.transpose.mono le_rfl (show _ ≤ J₁ from by
    rw [hS,hT.knobs]
    let e := Real.exp (-(b/4)*(R:ℝ))
    let p := phasePrice G P Pt.bind n Pt.top.paths b
    change (Fintype.card Signed:ℝ)*(|slip| *(e*p)) ≤ max 0 ((Fintype.card Signed:ℝ)*|slip| *p)*e
    calc
      _ = ((Fintype.card Signed:ℝ)*|slip| *p)*e := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right ..) (Real.exp_pos _).le)
  refine ⟨short.action (add_nonneg hC hD₀) hU hJ₀ hδ.le hν,?_⟩
  have h₁ := defect.action hD₀ hU hJ₀ hδ.le hν
  have h₂ := whole.action hC hV hJ₁ hδ.le hν
  have hdiff : (fun B => (rawRows T k (shorter R) B).transpose *ᵥ PhysicalAffineScalarCutWeights.sourceTail T x B -
        (rawRows T k all B-rawRows T k (shorter R) B).transpose *ᵥ PhysicalAffineScalarUncut.offset T k B) =
      fun B => shortLoad T x k B-wholeLoad T k B := by
    funext B i
    have hs := congrFun hsource B
    simp only [shortLoad,wholeLoad,Matrix.transpose_sub,Matrix.sub_mulVec,←hs,Matrix.mulVec_add,Pi.sub_apply,Pi.add_apply]
    abel
  have Hfin := h₁.diff h₂
  rw [hdiff] at Hfin
  exact Hfin

/-- Fix one late funded radius before naming the torus. The full source and raw
load have no temperature variable, so their ordinary constants are independent
of every subsequent cutoff temperature, including at higher derivative orders. -/
theorem whole_ordinary (G : Gauge) (P : Patch) (Pt : Teller G) (hp : P.Branches Pt.bind G) (n : ℕ) :
    ∃ δ C : ℝ, ∃ R₀ : ℕ, 0<δ ∧ 0<C ∧
    ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch=P → Pt.Funds S T → 100*(1+R₀) ≤ c.val → ∀ (_ : Forest S.ratio) (k : S.Choices),
      Paid (G:=G) (PhysicalAffineScalarComparison.rowRoot S) δ C n (PhysicalAffineScalarUncut.offset T k) ∧
      Paid (G:=G) (home S) δ C n (wholeLoad T k) := by
  obtain ⟨u,N,D,hu,hN,hD,full⟩ := PhysicalAffineScalarRetainedSource.full G P Pt hp n
  obtain ⟨v,N',D₁,D₂,hv,hN',hD₁,hD₂,loads⟩ := charges G P Pt hp n
  obtain ⟨x,hxF,hxL,hx⟩ := (full.and (loads.and (eventually_gt_atTop (1:ℝ)))).exists
  have ht := Work.E09.temp_pos (zero_lt_one.trans hx)
  let α := fullFee G P.L n N D (ConditionalAffineSourcePrices.rate Pt P.L) x
  let A := ordinaryFee G P Pt n N' D₁ D₂ x
  let deltaCost := tailFee G P Pt n N' D₁ D₂ x
  let C := 1+max |α| (|A|+|deltaCost|)
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨min u v,C,radiusB x,lt_min hu hv,hC,?_⟩
  intro c f S T hS hT hR F k
  have H := hxF S T hS hT hR ht F k
  have hF : Paid (G:=G) (PhysicalAffineScalarComparison.rowRoot S) u α n (PhysicalAffineScalarUncut.offset T k) := by
    apply Paid.of_rays (G:=G) (c:=c) (p:=PhysicalAffineScalarComparison.rowRoot S) (F:=PhysicalAffineScalarUncut.offset T k) (fun i => (H i).1)
    intro i j hj l
    apply ((H i).2 j hj l).trans
    have hp : (temp x)⁻¹^j ≤ (max 1 (temp x)⁻¹)^n :=
      (pow_le_pow_left₀ (inv_nonneg.mpr ht.le) (le_max_right ..) j).trans (pow_le_pow_right₀ (le_max_left ..) hj)
    have hf : 0 ≤ fiery G x P.L := by unfold fiery temp; positivity
    exact add_le_add (mul_le_mul_of_nonneg_right hp (mul_nonneg hN.le hf)) le_rfl
  obtain ⟨H₁,H₂⟩ := hxL S T hS hT hR ht F k
  have hL := H₁.diff H₂
  have hh : (fun B => shortLoad T x k B-(shortLoad T x k B-wholeLoad T k B))=wholeLoad T k := by
    funext B; abel
  rw [hh] at hL
  have hα : α ≤ C := by dsimp only [C]; linarith [le_abs_self α,le_max_left |α| (|A|+|deltaCost|)]
  have hβ : A+deltaCost ≤ C := by dsimp only [C]; linarith [le_abs_self A,le_abs_self deltaCost,le_max_right |α| (|A|+|deltaCost|)]
  exact ⟨hF.weaken (min_le_left ..) hα,hL.weaken (min_le_right ..) hβ⟩

end YM.Integration.ConditionalAffineLoadPrices
