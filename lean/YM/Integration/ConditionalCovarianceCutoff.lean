import YM.Integration.ConditionalTreeCovarianceJets
import YM.AnalyticBridge.GAUSSIAN_FIELD_ALIGNMENT.Operators
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Shutter
import YM.AnalyticBridge.SELECTED_ORDERED_KERNELS.SectorWindows

/-! The actual selected window and the rooted flat-position sums for the
cut versus uncut identity-completed affine covariance. A single physical
block-tree change is treated on the same coarse Taylor coordinates at
each spectral shift. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.ConditionalTreeCovarianceSums
open Lattice Wilson RG Precision Tree Matrix FreeResolvent FreeResolvent.Affine
  FreeResolvent.Mark FreeResolvent.TestD FreeResolvent.Lever FreeResolvent.Stars
  PhysicalNext.Repeat.Greenbelt ConditionalTreeCovarianceJets Function Filter Set
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f : Side} {S : StepData c f}

theorem anchor_weight {X ι τ : Type*} (D : Cost X) (a : ι → X) (b : τ → X)
    {j : ℕ} (i z : ι) (k : Fin j → τ) (d y : ℝ) :
    (positions D b d).pay (List.ofFn k) (a i) * (D.weight d (a i) (a z) * y) =
      Real.exp (d * costs D (a i) (a i) (a z) (b ∘ k)) * y := by
  rw [pays]
  simp only [costs,D.self,zero_add,mul_add,Real.exp_add,Cost.weight]
  ring

theorem sum_schedule {p : Clip} {j n : ℕ} {A σ : ℝ} (hj : j ≤ n)
    (hs : 0 < σ) (ha : 0 ≤ A) :
    let d := width G S.patch S.kernel p n A σ
    let γ := together G S.patch S.kernel p n A σ
    let V := totalFoot G S.patch S.kernel p n A σ
    0 < γ ∧ 2*(j+3:ℕ)*γ ≤ d ∧ 0 ≤ V ∧
      (native c).Volume (home (G:=G) (r:=1) S) γ V ∧
      (native c).Volume (hearth (G:=G) (c:=c) (r:=1)) γ V := by
  intro d γ V
  have hd : 0 < d := (gauged G S.patch S.kernel p n hs ha).pos
  have hγ : 0 < γ := div_pos hd (by positivity)
  have hV := home_volume (G:=G) S 1 γ hγ
  have hc := volume c (PAC G 1) γ hγ
  refine ⟨hγ,?_,(torusPay_nn (Bloch.Co S.patch.L (PAC G 1)) γ hγ).trans (le_max_left _ _),
    hV.le (le_max_left _ _),hc.le (le_max_right _ _)⟩
  have hN : (j:ℝ) ≤ n := by exact_mod_cast hj
  dsimp only [γ,together,d]
  push_cast
  rw [←mul_div_assoc,div_le_iff₀ (by positivity)]
  nlinarith only [mul_le_mul_of_nonneg_right hN hd.le]

/-- Resolve a rooted matrix-jet envelope and its one-block finite difference
against all physical slots. The ordinary selector can retain either endpoint
or any one of the independent derivative positions. -/
theorem summed {p : Clip} {j n : ℕ} {A σ M : ℝ} (hj : j < n)
    (hs : 0 < σ) (ha : 0 ≤ A) (hM : 0 ≤ M)
    (F : Reserve S → Vec G c 1 → Matrix (raw G f) (raw G f) ℝ)
    (ordinary : ∀ r, Site c → Bundle (ray G c) (marks G c (width G S.patch S.kernel p n A σ))
      (native c) (home S) (home S) (F r) 0 n (width G S.patch S.kernel p n A σ) M)
    (one : ∀ (r s : Reserve S) (v : Site c), (∀ w, w ≠ v → r w = s w) →
      ∀ l : List (raw G c), l.length < n → Here (ray G c) (native c) (home S) hearth
        (width G S.patch S.kernel p n A σ) (width G S.patch S.kernel p n A σ) v l M (F r) (F s)) :
    let γ := together G S.patch S.kernel p n A σ
    let V := totalFoot G S.patch S.kernel p n A σ
    let K (r : Reserve S) (i z : raw G f) (k : Fin j → raw G c) :=
      iteratedFDeriv ℝ j (F r) 0 (ray G c ∘ k) i z
    (∀ (r : Reserve S) (v : Site c) (g : raw G f → raw G f → (Fin j → raw G c) → Bool),
      (∀ i z k, g i z k = true → v = home S i ∨ v = home S z ∨ ∃ m, v = hearth (k m)) →
      NearStar j (native c) (home S) (home S) hearth v g γ (crowd j M V) (K r)) ∧
    ∀ (r s : Reserve S) (v : Site c), (∀ w, w ≠ v → r w = s w) →
      NearStar j (native c) (home S) (home S) hearth v (fun _ _ _ => true) γ (crowd j M V)
        (fun i z k => K s i z k - K r i z k) := by
  intro γ V K
  obtain ⟨hγ,hd,hV,hf,hc⟩ := sum_schedule (G:=G) (S:=S) (p:=p) hj.le hs ha
  constructor
  · intro r v g hg
    apply sums_no_mark hγ.le hM hd hV _ hg hf hf hc
    intro i z k
    have h := ((ordinary r v).bound (List.ofFn k) (by simpa using hj.le)).row.entry i z
    rw [list_result,anchor_weight] at h
    exact h
  intro r s v H
  apply sums_tagged hγ.le hM hd hV _ hf hf hc
  intro i z k
  have h := ((one r s v H (List.ofFn k) (by simpa using hj)).test i z).1
  rw [list_result,list_result,Matrix.sub_apply,mul_assoc,anchor_weight,←mul_assoc] at h
  exact h

theorem window_price {p : Clip} {n : ℕ} {A σ u R : ℝ} :
    windowPrice G S.patch S.kernel p n A σ u R =
      windowPrice G S.patch S.kernel p n A σ 0 0 *
        Real.exp (-(n+1:ℕ)*(width G S.patch S.kernel p n A σ)*R) * drain u ^ 2 := by
  have h₀ : drain 0 = 1 := by simp [drain]
  simp [ConditionalTreeCovarianceJets.windowPrice,patchFee,tagPrice,h₀]
  ring

theorem window_price_nonneg {p : Clip} {n : ℕ} {A σ u R : ℝ}
    (hs : 0 < σ) (ha : 0 ≤ A) (hu : 0 ≤ u) :
    0 ≤ windowPrice G S.patch S.kernel p n A σ u R := by
  have P := gauged G S.patch S.kernel p n hs ha
  have hC := mul_nonneg P.meter_abs (drain_pos hu).le
  exact tag_nn hC (mul_nonneg (Real.exp_pos _).le (tag_nn P.m (mul_nonneg P.vol hC)))

variable {t : S.Choices} {p : Clip} {W : PathData G} {σ A u : ℝ} {n j : ℕ}
  (hs : 0 < σ) (ha : 0 ≤ A) (hW : Sheet W σ A) (he : Bid.Larger (G:=G) S) (hu : 0 ≤ u)

include hs ha hW he hu

/-- The actual cut affine precision, its principal window and the assembled
tree law pay the simultaneous position sums uniformly across periods. -/
theorem window {I : raw G f → Type*} [∀ i, Fintype (I i)] [∀ i, DecidableEq (I i)]
    {R : ℝ} (Z : FreeResolvent.Window.Survey I) (hZ : Z.Near (native c) (home S) R)
    (q : Admit) (hj : j < n) :
    let γ := together G S.patch S.kernel p n A σ
    let V := totalFoot G S.patch S.kernel p n A σ
    let M := windowPrice G S.patch S.kernel p n A σ u R
    let K (r : Reserve S) (i z : raw G f) (k : Fin j → raw G c) :=
      iteratedFDeriv ℝ j (windowError Z (allot r) t p W q u) 0 (ray G c ∘ k) i z
    (∀ (r : Reserve S) (v : Site c) (g : raw G f → raw G f → (Fin j → raw G c) → Bool),
      (∀ i z k, g i z k = true → v = home S i ∨ v = home S z ∨ ∃ m, v = hearth (k m)) →
      NearStar j (native c) (home S) (home S) hearth v g γ (crowd j M V) (K r)) ∧
    ∀ (r s : Reserve S) (v : Site c), (∀ w, w ≠ v → r w = s w) →
      NearStar j (native c) (home S) (home S) hearth v (fun _ _ _ => true) γ (crowd j M V)
        (fun i z k => K s i z k - K r i z k) :=
  summed hj hs ha (window_price_nonneg hs ha hu) (fun r => windowError Z (allot r) t p W q u)
    (fun r v => window_regular hs ha hW he hu Z hZ r v q)
    (fun r s v h l hl => window_tag hs ha hW he hu Z hZ r s v h q l hl)

end YM.Integration.ConditionalTreeCovarianceSums

namespace YM.Integration.ConditionalCovarianceShutter
open Function Set Lattice Wilson RG Pressure Tree Matrix
  FreeResolvent FreeResolvent.Affine AnalyticBridge.GaussianFieldAlignment
  ConnectedActivityE6 ConnectedActivityE6.Coat ConnectedActivityE6.Census Next.SectorChange
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f}

def columns (G : Gauge) (S : StepData c f) (B : ℕ) (i : raw G f) : Set (raw G f) :=
  asSlot.symm ⁻¹' ((frames G S B).take (asSlot.symm i) : Set _)

private theorem self_mem (G : Gauge) (S : StepData c f) (B : ℕ) (i : raw G f) :
    i ∈ columns G S B i := (frames G S B).here _

def survey (G : Gauge) (S : StepData c f) (B : ℕ) :=
  view (columns G S B) (self_mem G S B)

theorem near (G : Gauge) (S : StepData c f) (B : ℕ) :
    (survey G S B).Near (native c) (home S) B := by
  intro i j hj
  change (B:ℝ) ≤ (separation (home S i) (home S j) : ℕ)
  exact_mod_cast (show B ≤ separation (home S i) (home S j) from by
    by_contra! h
    apply hj
    refine ⟨⟨j,(frames G S B).low _ _ ?_⟩,rfl⟩
    change separation (home S j) (home S i) ≤ B
    rw [separation_comm]
    exact h.le)

private theorem pad_per {ι : Type} [Fintype ι] [DecidableEq ι] {a : ι → Site c}
    {B : ℕ} (Z : ConnectedActivityE6.Window a B) (A : Matrix ι ι ℝ) :
    Z.pad A = Schur.per (fun i => (Z.take i : Set ι)) A := by
  ext i j
  by_cases hi : i ∈ Z.take j
  · rw [Z.inside A j ⟨i,hi⟩,Schur.per_read _ _ (Z.here j) hi]
    congr!
  rw [Z.outside A i j hi,Schur.per_zero _ _ hi]

/-- Restriction followed by inversion takes precisely the selected columns
of `Coat.frames`, including entries whose projection straddles a period seam. -/
theorem pad (G : Gauge) (S : StepData c f) (B : ℕ) (A : Matrix (raw G f) (raw G f) ℝ) :
    ((survey G S B).inspect A 0).submatrix asSlot asSlot =
      (frames G S B).pad (A.submatrix asSlot asSlot) := by
  rw [survey,per_view,per_relabel,pad_per]
  have H : (fun i : Tubular f G => asSlot ⁻¹' columns G S B (asSlot i)) =
      (fun i : Tubular f G => ((frames G S B).take i : Set _)) := by
    funext i
    ext j
    simp [columns]
  rw [H]

/-- The covariance used by the physical conditional Gaussian is the
symmetrized column integral in these same coordinates. -/
theorem covariance {T : Tube G S} {F : Forest S.ratio} (X : Coat T F) :
    let A := X.plate.submatrix asSlot.symm asSlot.symm
    let Z := (survey G S X.B).inspect A 0
    ((1/2:ℝ) • (Z + Z.transpose)).submatrix asSlot asSlot = X.relating := by
  intro A Z
  have hA : A.submatrix asSlot asSlot = X.plate := by ext i j; simp [A]
  have hp : Z.submatrix asSlot asSlot = X.shutter.pad X.plate :=
    (pad G S X.B A).trans (congrArg (frames G S X.B).pad hA)
  ext i j
  change (1/2:ℝ) * (Z (asSlot i) (asSlot j) + Z (asSlot j) (asSlot i)) =
    (1/2:ℝ) * (X.shutter.pad X.plate i j + X.shutter.pad X.plate j i)
  rw [show Z (asSlot i) (asSlot j) = X.shutter.pad X.plate i j from congr_fun (congr_fun hp i) j,
    show Z (asSlot j) (asSlot i) = X.shutter.pad X.plate j i from congr_fun (congr_fun hp j) i]

end YM.Integration.ConditionalCovarianceShutter

namespace YM.Integration.ConditionalCovarianceCutoff
open Lattice Wilson RG Precision Tree Matrix FreeResolvent FreeResolvent.Affine
  FreeResolvent.Mark FreeResolvent.TestD FreeResolvent.Lever FreeResolvent.Stars
  PhysicalNext.Repeat.Greenbelt ConditionalTreeCovarianceJets ConditionalTreeCovarianceSums
  SelectedOrderedKernels.Sector Function Filter Set
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f : Side} {S : StepData c f} {t : S.Choices}
  {p : Clip} {W : PathData G} {σ A u : ℝ} {n : ℕ}

/-- Principal columns are used directly by the affine stationarity equation and
transposed by its Gaussian mean. The covariance uses their symmetric part. -/
inductive ColumnMode where
  | direct
  | adjoint
  | symmetric

def ColumnMode.matrix {ι : Type*} (mode : ColumnMode) (Q : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  match mode with
  | .direct => Q
  | .adjoint => Q.transpose
  | .symmetric => (1/2:ℝ) • (Q + Q.transpose)

def ColumnMode.field {ι E : Type*} (mode : ColumnMode) (Q : E → Matrix ι ι ℝ) :=
  fun x => mode.matrix (Q x)

private theorem ColumnMode.bound {ι E X τ : Type*} [Fintype ι] [NormedAddCommGroup E]
    [NormedSpace ℝ E] {v : τ → E} {C : Mark τ X} {D : Cost X} {a : ι → X}
    {s M : ℝ} {k : ℕ} {Q : E → Matrix ι ι ℝ} {x : E}
    (mode : ColumnMode) (h : Bundle v C D a a Q x k s M) :
    Bundle v C D a a (mode.field Q) x k s M := by
  cases mode with
  | direct => exact h
  | adjoint => exact h.transpose
  | symmetric => exact polarize_cost h

def columns (mode : ColumnMode) (B L : ℕ) (r : Reserve S) (t : S.Choices) (p : Clip)
    (W : PathData G) (u : ℝ) :=
  mode.field (glimpse (ConditionalCovarianceShutter.survey G S B) (whole S (allot r) t p W (shorter L)) u -
    action (whole S (allot r) t p W all) u)

abbrev difference (B L : ℕ) (r : Reserve S) (t : S.Choices) (p : Clip) (W : PathData G) (u : ℝ) :=
  columns .symmetric B L r t p W u

theorem whole_symm (F : Forest S.ratio) (q : Admit) (x : Vec G c 1) :
    (whole S F t p W q x).IsSymm := by
  have h : (block S t p W q x).IsSymm := by
    unfold block
    apply Matrix.IsSymm.smul
    unfold Matrix.IsSymm channel squareQ
    simp [Matrix.transpose_sum]
  change (Shell.pad (freeTo G S F) (block S t p W q x)).transpose =
    Shell.pad (freeTo G S F) (block S t p W q x)
  simp only [Shell.pad,Shell.slice,Shell.off,Matrix.transpose_add,Matrix.transpose_mul,
    Matrix.transpose_sub,Matrix.transpose_one,Shell.clockwise,h.eq,Matrix.mul_assoc]

/-- At every coarse field the ideal leg is the full resolvent itself. At
zero spectral shift the first leg is the physical symmetrized covariance. -/
theorem difference_eq (B L : ℕ) (r : Reserve S) :
    difference B L r t p W u = polarize (glimpse (ConditionalCovarianceShutter.survey G S B)
        (whole S (allot r) t p W (shorter L)) u) - action (whole S (allot r) t p W all) u := by
  apply polarize_sub
  intro x
  change ((whole S (allot r) t p W all x + u • 1)⁻¹).IsSymm
  apply Matrix.IsSymm.inv
  unfold Matrix.IsSymm
  rw [Matrix.transpose_add,Matrix.transpose_smul,Matrix.transpose_one,(whole_symm (allot r) all x).eq]

/-- At every field, the transpose used by the mean leaves the full ideal
resolvent fixed. The identity-completed raw coordinates are unchanged. -/
theorem adjoint_columns (B L : ℕ) (r : Reserve S) (x : Vec G c 1) :
    columns .adjoint B L r t p W u x =
      ((ConditionalCovarianceShutter.survey G S B).inspect (whole S (allot r) t p W (shorter L) x) u).transpose -
      resolve (whole S (allot r) t p W all x) u := by
  have h : (resolve (whole S (allot r) t p W all x) u).IsSymm := by
    apply Matrix.IsSymm.inv
    unfold Matrix.IsSymm
    rw [Matrix.transpose_add,Matrix.transpose_smul,Matrix.transpose_one,(whole_symm (allot r) all x).eq]
  exact (Matrix.transpose_sub _ _).trans (congrArg (fun Q => _ - Q) h.eq)

/-- The cut affine mean minus its ideal mean retains two genuine defects:
the transposed propagator acting on the cut source and the full shifted
inverse acting on the difference of the sources. -/
theorem mean_split (B L : ℕ) (r : Reserve S) (x : Vec G c 1) (bcut ball : raw G f → ℝ) :
    let Z := (ConditionalCovarianceShutter.survey G S B).inspect (whole S (allot r) t p W (shorter L) x) u
    let I := resolve (whole S (allot r) t p W all x) u
    I.mulVec ball - Z.transpose.mulVec bcut =
      -((columns .adjoint B L r t p W u x).mulVec bcut + I.mulVec (bcut - ball)) := by
  intro Z I
  rw [adjoint_columns,Matrix.sub_mulVec,Matrix.mulVec_sub]
  abel

/-- After the simultaneous affine Gaussian reference change, these are
the actual active rows in the remaining no-hole exponent. Their germ is
the restriction of the same full matrix used throughout the comparison. -/
theorem physical_rows (A₀ : Pressure.Stores S) (r : Reserve S) (x : ℝ) (T : Pressure.Tube G S)
    (t : S.Choices) {Γ E Λ : ℝ} (h : S.patch.Branches S.kernel G) (hT : T.up.Bounds T.high Γ E Λ) :
    let F := allot r
    let e := AnalyticBridge.GaussianFieldAlignment.address A₀ F x (G:=G)
    ∀ᶠ y : Vec G c 1 in 𝓝 0,
      (whole S F t T.high T.up (shorter (Pressure.Stores.till x)) y).submatrix e e =
        Next.SectorChange.Rows.gram T x (represent (decode y)) t (Next.SectorChange.shots S x) A₀ F := by
  intro F e
  filter_upwards [AnalyticBridge.GaussianFieldAlignment.affine_near A₀ F x T t h hT] with y hy
  rw [hy]
  ext i j
  exact congrArg (fun Q => Q (AnalyticBridge.GaussianFieldAlignment.live A₀ F x i)
      (AnalyticBridge.GaussianFieldAlignment.live A₀ F x j))
    (Shell.reaches (freeTo G S F) (block S t T.high T.up (shorter (Pressure.Stores.till x)) y))

private theorem family (mode : ColumnMode) (hs : 0 < σ) (ha : 0 ≤ A) (hW : Sheet W σ A) (he : Bid.Larger (G:=G) S)
    (hu : 0 ≤ u) (B L : ℕ) {T U : Forest S.ratio} {v : Site c} (hTU : changed S T U v)
    {θ : ℝ} (hθ : θ ∈ Icc (0:ℝ) 1) :
    let d := width G S.patch S.kernel p n A σ
    let Z := ConditionalCovarianceShutter.survey G S B
    let F := crest S t (W:=W) (T:=T) (U:=U) (p:=p)
    Bundle (guides (ray G c)) (park (native c) hearth d v) (native c) (home S) (home S)
      (mode.field (glimpse Z (F (shorter L)) u - action (F all) u)) (0,θ) n d
      (windowPrice G S.patch S.kernel p n A σ u B + diminish G S.patch S.kernel p n L A σ u) := by
  intro d Z F
  have P := gauged G S.patch S.kernel p n hs ha
  have hfull := mast S t (p:=p) (n:=n) hs ha hW he hTU all hθ
  have hcut := mast S t (p:=p) (n:=n) hs ha hW he hTU (shorter L) hθ
  have V := home_volume (G:=G) S 1 _ P.pos
  have hm := position_move (native c) (fun i : Option (raw G c) => i.elim v hearth) P.pos.le
  have hw := hcut.discrepancy P hu hm V (ConditionalCovarianceShutter.near G S B)
  have hr := roll S t (p:=p) (n:=n) hs ha hW he hTU L hθ
  let C := phasePrice G S.patch S.kernel n A σ
  have hC : 0 ≤ C := phase_nn G S.patch S.kernel hs ha
  have ht : 0 ≤ 3*(Real.exp (-(σ/4)*L)*(2*tagPrice 1 n C C)) :=
    mul_nonneg (by norm_num) (mul_nonneg (Real.exp_pos _).le (mul_nonneg (by norm_num) (tag_nn hC hC)))
  have hd : (2*(n+1:ℕ)+1)*d ≤ tier σ n / 2 := by
    refine le_trans ?_ (P.roomEnough.trans P.roomTop)
    apply mul_le_mul_of_nonneg_right _ P.pos.le
    push_cast
    linarith [show (0:ℝ) ≤ n by positivity]
  have hc := hfull.change hcut P hu hm V ht (hr.mono hd le_rfl)
  apply mode.bound
  apply (hw.one_add hc).glue
  exact Eventually.of_forall fun z => by simp only [Pi.sub_apply]; abel

theorem cut_price {L : ℕ} : diminish G S.patch S.kernel p n L A σ u =
    diminish G S.patch S.kernel p n 0 A σ 0 * Real.exp (-(σ/4)*L) * drain u ^ 2 := by
  have h₀ : drain 0 = 1 := by simp [drain]
  simp [diminish,tagPrice,h₀]
  ring

theorem spectral_price (B L : ℕ) :
    windowPrice G S.patch S.kernel p n A σ u B + diminish G S.patch S.kernel p n L A σ u =
    (windowPrice G S.patch S.kernel p n A σ 0 B + diminish G S.patch S.kernel p n L A σ 0) * drain u ^ 2 := by
  rw [window_price (R:=(B:ℝ)) (u:=u),cut_price (L:=L) (u:=u),
    window_price (R:=(B:ℝ)) (u:=0),cut_price (L:=L) (u:=0)]
  simp only [drain,add_zero,inv_one,one_pow,mul_one,add_mul]

theorem cut_nonneg (hs : 0 < σ) (ha : 0 ≤ A) (hu : 0 ≤ u) (L : ℕ) :
    0 ≤ diminish G S.patch S.kernel p n L A σ u := by
  have P := gauged G S.patch S.kernel p n hs ha
  have h0 := mul_nonneg P.meter_abs (drain_pos hu).le
  have hC := phase_nn G S.patch S.kernel (k:=n) hs ha
  exact tag_nn (tag_nn h0 (mul_nonneg (by norm_num)
      (mul_nonneg (Real.exp_pos _).le (mul_nonneg (by norm_num) (tag_nn hC hC))))) h0

/-- Every funded stage has at least one complete cutoff unit. Its integer
rounding can then be paid entirely out of the rate, so the coefficient is
the same native algebraic price at radius zero. -/
theorem funded_price (hs : 0 < σ) (ha : 0 ≤ A) (B : ℕ) (hB : 100000 ≤ B) :
    let d := width G S.patch S.kernel p n A σ
    let rate := min (((n+1:ℕ):ℝ)*d) (σ/800000)
    let C := windowPrice G S.patch S.kernel p n A σ 0 0 + diminish G S.patch S.kernel p n 0 A σ 0
    0 < rate ∧ windowPrice G S.patch S.kernel p n A σ u B +
      diminish G S.patch S.kernel p n (B/100000) A σ u ≤ C*Real.exp (-rate*B)*drain u^2 := by
  intro d μ C
  have hd : 0 < d := (gauged G S.patch S.kernel p n hs ha).pos
  have hN : (B:ℝ) ≤ 200000*(((B/100000:ℕ):ℝ)) := by
    exact_mod_cast (show B ≤ 200000*(B/100000) from by omega)
  have h₁ : Real.exp (-(n+1:ℕ)*d*B) ≤ Real.exp (-μ*B) := by
    apply Real.exp_monotone
    have hμ : μ ≤ ((n+1:ℕ):ℝ)*d := min_le_left ..
    linarith only [mul_le_mul_of_nonneg_right hμ (Nat.cast_nonneg B)]
  have h₂ : Real.exp (-(σ/4)*(B/100000:ℕ)) ≤ Real.exp (-μ*B) := by
    apply Real.exp_monotone
    have hμ : μ ≤ σ/800000 := min_le_right ..
    nlinarith only [mul_le_mul_of_nonneg_right hμ (Nat.cast_nonneg B),mul_le_mul_of_nonneg_left hN hs.le]
  have wh := window_price_nonneg (G:=G) (S:=S) (p:=p) (n:=n) (R:=0) hs ha (le_refl 0)
  have dh := cut_nonneg (G:=G) (S:=S) (p:=p) (n:=n) hs ha (le_refl 0) 0
  refine ⟨lt_min (mul_pos (by positivity) hd) (by positivity),?_⟩
  rw [window_price,cut_price,←add_mul]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact (add_le_add (mul_le_mul_of_nonneg_left h₁ wh) (mul_le_mul_of_nonneg_left h₂ dh)).trans_eq
    (add_mul _ _ _).symm

theorem regular (hs : 0 < σ) (ha : 0 ≤ A) (hW : Sheet W σ A) (he : Bid.Larger (G:=G) S)
    (hu : 0 ≤ u) (B L : ℕ) (r : Reserve S) (v : Site c) (mode : ColumnMode := .symmetric) :
    let d := width G S.patch S.kernel p n A σ
    Bundle (ray G c) (marks G c d) (native c) (home S) (home S) (columns mode B L r t p W u) 0 n d
      (windowPrice G S.patch S.kernel p n A σ u B + diminish G S.patch S.kernel p n L A σ u) := by
  intro d
  have hf := family mode (t:=t) (p:=p) (n:=n) hs ha hW he hu B L
    (change_draw r r v (fun _ _ => rfl)) (Set.left_mem_Icc.mpr zero_le_one)
  let Z := ConditionalCovarianceShutter.survey G S B
  refine (restricted 0 hf).glue (Eventually.of_forall fun x => ?_)
  exact congrArg₂ (fun Q R => mode.matrix (Z.inspect Q u - resolve R u))
    (now (allot r) (allot r) t p (shorter L) x) (now (allot r) (allot r) t p all x)

theorem tagged (hs : 0 < σ) (ha : 0 ≤ A) (hW : Sheet W σ A) (he : Bid.Larger (G:=G) S)
    (hu : 0 ≤ u) (B L : ℕ) (r s : Reserve S) (v : Site c) (h : ∀ w, w ≠ v → r w = s w)
    (l : List (raw G c)) (hl : l.length < n) (mode : ColumnMode := .symmetric) :
    let d := width G S.patch S.kernel p n A σ
    Here (ray G c) (native c) (home S) hearth d d v l
      (windowPrice G S.patch S.kernel p n A σ u B + diminish G S.patch S.kernel p n L A σ u)
      (columns mode B L r t p W u) (columns mode B L s t p W u) := by
  intro d
  let Z := ConditionalCovarianceShutter.survey G S B
  let F := crest S t (W:=W) (T:=allot r) (U:=allot s) (p:=p)
  refine paid (G:=mode.field (glimpse Z (F (shorter L)) u - TestD.action (F all) u)) ?_ ?_ hl ?_
  · intro x
    exact congrArg₂ (fun Q R => mode.matrix (Z.inspect Q u - resolve R u))
      (now (allot r) (allot s) t p (shorter L) x) (now (allot r) (allot s) t p all x)
  · intro x
    exact congrArg₂ (fun Q R => mode.matrix (Z.inspect Q u - resolve R u))
      (thenAt (allot r) (allot s) t p (shorter L) x) (thenAt (allot r) (allot s) t p all x)
  exact fun θ hθ => family mode hs ha hW he hu B L (change_draw r s v h) hθ

/-- The full weighted sum over matrix endpoints and every external field
position, with one specified terminal, derivative site or changed tree block. -/
theorem position_sum (hs : 0 < σ) (ha : 0 ≤ A) (hW : Sheet W σ A) (he : Bid.Larger (G:=G) S)
    (hu : 0 ≤ u) (B L j : ℕ) (hj : j < n) (mode : ColumnMode := .symmetric) :
    let γ := together G S.patch S.kernel p n A σ
    let V := totalFoot G S.patch S.kernel p n A σ
    let M := windowPrice G S.patch S.kernel p n A σ u B + diminish G S.patch S.kernel p n L A σ u
    let K (r : Reserve S) (i z : raw G f) (k : Fin j → raw G c) :=
      iteratedFDeriv ℝ j (columns mode B L r t p W u) 0 (ray G c ∘ k) i z
    (∀ (r : Reserve S) (v : Site c) (g : raw G f → raw G f → (Fin j → raw G c) → Bool),
      (∀ i z k, g i z k = true → v = home S i ∨ v = home S z ∨ ∃ m, v = hearth (k m)) →
      NearStar j (native c) (home S) (home S) hearth v g γ (crowd j M V) (K r)) ∧
    ∀ (r s : Reserve S) (v : Site c), (∀ w, w ≠ v → r w = s w) →
      NearStar j (native c) (home S) (home S) hearth v (fun _ _ _ => true) γ (crowd j M V)
        (fun i z k => K s i z k - K r i z k) := by
  apply summed hj hs ha (add_nonneg (window_price_nonneg hs ha hu) (cut_nonneg hs ha hu L))
      (fun r => columns mode B L r t p W u)
  · exact fun r v => regular hs ha hW he hu B L r v mode
  exact fun r s v h l hl => tagged hs ha hW he hu B L r s v h l hl mode

end YM.Integration.ConditionalCovarianceCutoff
