import YM.Integration.ConditionalCovarianceCutoff
import YM.RG02.Roots.Radius
import YM.AnalyticBridge.RELATIVE_LOGDET_TRACE.Papyrus
import YM.AnalyticBridge.RELATIVE_LOGDET_TRACE.Teller
import YM.AnalyticBridge.RELATIVE_LOGDET_TRACE.Gains
import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.Accuracy
import YM.Integration.ActualRunSpring
import YM.Integration.ActualKernelIdentification
import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Station
import YM.Progress.STATIONARY_SCENES.Response

/-! Rooted radius coefficients and paired half-logarithms of the actual
cut-window discrepancy, including the selected no-hole Run stage. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ConditionalCovarianceLayers
open Lattice RG Wilson Precision Tree FreeResolvent FreeResolvent.Affine FreeResolvent.TestD
  FreeResolvent.Mark FreeResolvent.Stars PhysicalNext.Repeat.Greenbelt RG02.Roots
  ConditionalTreeCovarianceJets ConditionalTreeCovarianceSums ConditionalCovarianceCutoff
open scoped Classical Topology BigOperators ContDiff Matrix.Norms.Frobenius

/-- The coordinate-order paths connecting every slot to the retained root have
total nearest-neighbor length bounded by four times the native star cost. -/
theorem nearest_neighbor {c : Side} {ι κ τ : Type*} [Fintype ι] [Fintype κ] [Fintype τ]
    {n : ℕ} {a : ι → Site c} {b : κ → Site c} {p : τ → Site c} {v : Site c}
    {T : ι → κ → (Fin n → τ) → Bool} {F : ι → κ → (Fin n → τ) → ℝ}
    {γ M : ℝ} (hγ : 0 ≤ γ) (h : NearStar n (native c) a b p v T γ M F) :
    NearStar n (taxi c) a b p v T (γ/4) M F := by
  constructor
  refine (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
    Finset.sum_le_sum fun k _ => ?_).trans h.limit
  split_ifs
  · refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (abs_nonneg _)
    have hr : rays (taxi c) v (p ∘ k) ≤ 4 * rays (native c) v (p ∘ k) := by
      unfold FreeResolvent.Stars.rays
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun s _ => taxi_le_native v (p (k s))
    have hc : costs (taxi c) v (a i) (b j) (p ∘ k) ≤
        4 * costs (native c) v (a i) (b j) (p ∘ k) := by
      unfold costs
      linarith [taxi_le_native v (a i), taxi_le_native v (b j)]
    nlinarith [mul_nonneg hγ (sub_nonneg.mpr hc)]
  · exact le_rfl

private theorem remove_weight {x y M : ℝ} (h : Real.exp x * y ≤ M) :
    y ≤ M * Real.exp (-x) := by
  calc
    y = Real.exp (-x) * (Real.exp x * y) := by rw [←mul_assoc,←Real.exp_add,neg_add_cancel,
      Real.exp_zero,one_mul]
    _ ≤ Real.exp (-x)*M := mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    _ = _ := mul_comm ..

private theorem count_sites (c : Side) {d : ℝ} (hd : 0 < d) :
    Covers (id : Site c → Site c) d (max 1 (torusPay Unit d)) := by
  let e : Site c → Site c × Unit := fun v => (v,())
  have hv := (volume c Unit d hd).comp (e:=e) (fun _ _ h => congr_arg Prod.fst h)
  exact ⟨le_max_left ..,fun i => (hv.bound i).trans (le_max_right ..)⟩

variable {G : Gauge} {c f : Side} {S : StepData c f} {t : S.Choices}
  {p : Clip} {W : PathData G} {σ A u : ℝ} {n j : ℕ}

def horizon (x : Site c) : ℕ := Finset.univ.sup (separation x)

/-- On each finite torus these very shells reconstruct the physical-draw
coefficient. Only this last radius can depend on the period. -/
theorem reconstruct (B L : ℕ) (i z : raw G f) (k : Fin j → raw G c) (r₀ r : Reserve S) :
    let K (s : Reserve S) : ℂ :=
      (iteratedFDeriv ℝ j (difference B L s t p W u) 0 (ray G c ∘ k) i z : ℝ)
    (∑ m : Fin (horizon (home S i)+1), layer id (home S i) r₀ K m r) = K r := by
  intro K
  have h (v : Site c) : separation (home S i) v ≤ horizon (home S i) :=
    Finset.le_sup (Finset.mem_univ v)
  simpa only [Finset.sum_apply] using congrFun (combined id (home S i) _ h r₀ K) r

theorem layers (hs : 0 < σ) (ha : 0 ≤ A) (hW : Sheet W σ A) (he : Bid.Larger (G:=G) S)
    (hu : 0 ≤ u) (B L : ℕ) (hj : j < n) (i z : raw G f) (k : Fin j → raw G c)
    (r₀ : Reserve S) (m : ℕ) :
    let d := width G S.patch S.kernel p n A σ
    let M := windowPrice G S.patch S.kernel p n A σ u B + diminish G S.patch S.kernel p n L A σ u
    let D := costs (native c) (home S i) (home S i) (home S z) (hearth ∘ k)
    let K (r : Reserve S) : ℂ := (iteratedFDeriv ℝ j (difference B L r t p W u) 0 (ray G c ∘ k) i z : ℝ)
    let H := layer id (home S i) r₀ K m
    RG02.Wick.Actor.Needs H (dots id (home S i) m) ∧
      ∀ r, ‖H r‖ ≤ max 1 (torusPay Unit (d/2)) *
        (M * Real.exp (-d*D)) * RG02.Roots.span (d/2) m := by
  intro d M D K H
  have h0 : 0 < d := (gauged G S.patch S.kernel p n hs ha).pos
  let J (r : Reserve S) := iteratedFDeriv ℝ j (difference B L r t p W u) 0 (ray G c ∘ k) i z
  have base (r : Reserve S) : Real.exp (d*D) * |J r| ≤ M := by
    have h := ((regular (p:=p) (t:=t) (n:=n) hs ha hW he hu B L r (home S i)).bound
      (List.ofFn k) (by simpa using hj.le)).row.entry i z
    rw [list_result,anchor_weight] at h
    exact h
  have vary (r s : Reserve S) (v : Site c) (hv : ∀ w, w ≠ v → r w = s w) :
      (native c).weight d (home S i) v * (Real.exp (d*D) * |J r - J s|) ≤ M := by
    have h := ((tagged (p:=p) (t:=t) (n:=n) hs ha hW he hu B L s r v
      (fun w hw => (hv w hw).symm) (List.ofFn k) (by simpa using hj)).test i z).1
    rw [list_result,list_result,Matrix.sub_apply,mul_assoc,anchor_weight] at h
    exact h
  have hM : 0 ≤ M := (mul_nonneg (Real.exp_pos _).le (abs_nonneg _)).trans (base r₀)
  have ht : Tolls id (home S i) K d (M * Real.exp (-d*D)) := by
    refine ⟨mul_nonneg hM (Real.exp_pos _).le,?_,?_⟩
    · intro r
      change ‖((J r : ℝ):ℂ)‖ ≤ _
      rw [Complex.norm_real,Real.norm_eq_abs,neg_mul]
      exact remove_weight (base r)
    intro r s v hv
    change ‖((J r:ℝ):ℂ) - ((J s:ℝ):ℂ)‖ ≤ _
    rw [←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
    let q : ℝ := separation (home S i) v
    have hh := vary r s v hv
    change Real.exp (d*q)*(Real.exp (d*D)*|J r-J s|) ≤ M at hh
    rw [←mul_assoc,←Real.exp_add] at hh
    refine (remove_weight hh).trans_eq ?_
    change M * Real.exp (-(d*q+d*D)) = M * Real.exp (-d*D) * Real.exp (-d*q)
    rw [mul_assoc,←Real.exp_add]
    congr 2
    ring
  refine ⟨touches _ _ _ _ _,fun r => ?_⟩
  have ht' : Tolls id (home S i) K (d/2+d/2) (M * Real.exp (-d*D)) := by
    convert ht using 1
    ring
  exact ht'.layer_bound (half_pos h0) (count_sites c (half_pos h0)) m r r₀

/-- At each tag radius the full rooted sum over derivative sites, matrix
endpoints, fine residues and colors pays the same summable radial factor. -/
theorem rooted_layers (hs : 0 < σ) (ha : 0 ≤ A) (hW : Sheet W σ A) (he : Bid.Larger (G:=G) S)
    (hu : 0 ≤ u) (B L : ℕ) (hj : j < n) (r₀ r : Reserve S) (m : ℕ) (v : Site c)
    (g : raw G f → raw G f → (Fin j → raw G c) → Bool)
    (hg : ∀ i z k, g i z k = true → v = home S i ∨ v = home S z ∨ ∃ a, v = hearth (k a)) :
    let d := width G S.patch S.kernel p n A σ
    let γ := together G S.patch S.kernel p n A σ
    let V := totalFoot G S.patch S.kernel p n A σ
    let M := windowPrice G S.patch S.kernel p n A σ u B + diminish G S.patch S.kernel p n L A σ u
    let K (i z : raw G f) (k : Fin j → raw G c) (s : Reserve S) : ℂ :=
      (iteratedFDeriv ℝ j (difference B L s t p W u) 0 (ray G c ∘ k) i z : ℝ)
    NearStar j (native c) (home S) (home S) hearth v g γ
      (crowd j (max 1 (torusPay Unit (d/2)) * M * RG02.Roots.span (d/2) m) V)
      (fun i z k => ‖layer id (home S i) r₀ (K i z k) m r‖) := by
  intro d γ V M K
  have hM : 0 ≤ M := add_nonneg (window_price_nonneg hs ha hu) (cut_nonneg hs ha hu L)
  have hc : 0 ≤ max 1 (torusPay Unit (d/2)) := zero_le_one.trans (le_max_left ..)
  obtain ⟨hγ,hd,hV,hf,hw⟩ := sum_schedule (G:=G) (S:=S) (p:=p) hj.le hs ha
  apply sums_no_mark hγ.le (mul_nonneg (mul_nonneg hc hM) (span_pos ..).le) hd hV _ hg hf hf hw
  intro i z k
  let D := costs (native c) (home S i) (home S i) (home S z) (hearth ∘ k)
  have H := (layers (t:=t) (p:=p) hs ha hW he hu B L hj i z k r₀ m).2 r
  rw [abs_of_nonneg (norm_nonneg _)]
  apply (mul_le_mul_of_nonneg_left H (Real.exp_pos _).le).trans_eq
  change Real.exp (d*D) * (max 1 (torusPay Unit (d/2)) * (M*Real.exp (-d*D)) * _) = _
  rw [neg_mul,Real.exp_neg]
  field_simp
  rfl

/-- Specialization to the incoming no-hole stage with its original funded
path rows, selected true-length cutoff, and actual block window. -/
theorem selected {P : Pressure.Teller G} {T : Pressure.Tube G S} {x : ℝ}
    (h : ConnectedActivityE6.Room P S T x) (hu : 0 ≤ u) (hj : j < n)
    (i z : raw G f) (k : Fin j → raw G c) (r₀ : Reserve S) (m : ℕ) :
    let σ := P.top.width
    let A := P.top.paths
    let B := Pressure.radiusB x
    let L := Pressure.Stores.till x
    let d := width G S.patch S.kernel T.high n A σ
    let M := windowPrice G S.patch S.kernel T.high n A σ u B + diminish G S.patch S.kernel T.high n L A σ u
    let D := costs (native c) (home S i) (home S i) (home S z) (hearth ∘ k)
    let K (r : Reserve S) : ℂ :=
      (iteratedFDeriv ℝ j (difference B L r t T.high T.up u) 0 (ray G c ∘ k) i z : ℝ)
    let H := layer id (home S i) r₀ K m
    RG02.Wick.Actor.Needs H (dots id (home S i) m) ∧
      ∀ r, ‖H r‖ ≤ max 1 (torusPay Unit (d/2)) *
        (M * Real.exp (-d*D)) * RG02.Roots.span (d/2) m := by
  obtain ⟨_,_,hr,_⟩ := h.accepted.feeds
  exact layers P.top.width_pos P.top.paths_pos.le hr.rows h.larger hu
    (Pressure.radiusB x) (Pressure.Stores.till x) hj i z k r₀ m

end YM.Integration.ConditionalCovarianceLayers

namespace YM.Integration.ConditionalCovarianceLogarithm
open Function Set Filter Lattice RG Wilson Tree Precision Matrix MeasureTheory
  FreeResolvent FreeResolvent.Affine FreeResolvent.TestD PhysicalNext.Repeat.Greenbelt
  AnalyticBridge.RelativeLogdet AnalyticBridge.RelativeLogdet.Ink AnalyticBridge.RelativeLogdet.Differential
  ConditionalTreeCovarianceJets ConditionalTreeCovarianceSums
  ConditionalCovarianceCutoff
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius

variable {G : Gauge} {c f : Side} {S : StepData c f} {t : S.Choices} {p : Clip}
  {W : PathData G} {σ A : ℝ} {n : ℕ}

def rooted (B L : ℕ) (r : Reserve S) (t : S.Choices) (p : Clip) (W : PathData G)
    (i : raw G f) (x : Vec G c 1) :=
  letterBase (ConditionalCovarianceShutter.columns G S B) (whole S (allot r) t p W (shorter L) x) i -
    logKernel (whole S (allot r) t p W all x) i i

def paired (B L : ℕ) (r : Reserve S) (t : S.Choices) (p : Clip) (W : PathData G)
    (i : raw G f) (x : Vec G c 1) :=
  (1/2:ℝ) * (rooted B L r t p W i x - rooted B L r t p W i 0)

theorem flat (B L : ℕ) (r : Reserve S) (i : raw G f) : paired B L r t p W i 0 = 0 := by
  simp [paired]

private theorem gram (hs : 0 < σ) (ha : 0 ≤ A) (hW : Sheet W σ A) (he : Bid.Larger (G:=G) S)
    (r : Reserve S) (q : Admit) :
    let Q := whole S (allot r) t p W q
    ContDiffAt ℝ n Q 0 ∧ ∀ᶠ y in 𝓝 0, (Q y).PosDef := by
  intro Q
  have h := mast S t (p:=p) (n:=n) hs ha hW he (change_draw r r 0 (fun _ _ => rfl)) q
    (Set.left_mem_Icc.mpr zero_le_one)
  have hc : ContDiffAt ℝ n Q 0 := by
    apply (h.smooth.comp (0:Vec G c 1) (contDiffAt_id.prodMk (contDiffAt_const (c:=(0:ℝ))))).congr_of_eventuallyEq
    exact Eventually.of_forall fun y => (now (allot r) (allot r) t p q y).symm
  have hg : Gap (Q 0) (gum G S.patch S.kernel p) := by simpa only [now] using h.gap
  have hr := gum_pos G S.patch S.kernel p
  have hy := holds hc.continuousAt hg _ (half_lt_self hr) (native c) (home S)
  exact ⟨hc,hy.mono fun y hQ => AnalyticBridge.LocalGaussianLaws.gap_positive (whole_symm _ _ y) hQ (half_pos hr)⟩

private theorem diag (B L : ℕ) (r : Reserve S) (x : Vec G c 1) (u : ℝ) (i : raw G f) :
    difference B L r t p W u x i i =
      pie (ConditionalCovarianceShutter.columns G S B) (whole S (allot r) t p W (shorter L) x) u i i -
      resolve (whole S (allot r) t p W all x) u i i := by
  have h (j : raw G f) : j ∈ ConditionalCovarianceShutter.columns G S B j :=
    (ConnectedActivityE6.Coat.frames G S B).here _
  rw [pie_inspects _ _ _ h]
  let Z := (study (ConditionalCovarianceShutter.columns G S B) h).inspect
    (whole S (allot r) t p W (shorter L) x) u i i
  let I := resolve (whole S (allot r) t p W all x) u i i
  change (1/2:ℝ)*((Z-I)+(Z-I))=Z-I
  ring

/-- The integral identity uses both genuine logarithms and keeps the
fixed matrix index. Differentiation is justified by the native compactified
spectral formula on the positive Gram germs. -/
theorem integral (hs : 0 < σ) (ha : 0 ≤ A) (hW : Sheet W σ A) (he : Bid.Larger (G:=G) S)
    (r : Reserve S) (B L : ℕ) (i : raw G f) (l : List (raw G c)) (hl : l.length ≤ n) :
    let v := ray G c
    let J (u : ℝ) := jet v (fun y => difference B L r t p W u y i i) l 0
    IntegrableOn J (Ioi 0) ∧ jet v (rooted B L r t p W i) l 0 = -(∫ u in Ioi 0, J u) := by
  intro v J
  let Q := whole S (allot r) t p W
  let P := ConditionalCovarianceShutter.columns G S B
  have H := gram (t:=t) (p:=p) (n:=n) hs ha hW he r (shorter L)
  have F := gram (t:=t) (p:=p) (n:=n) hs ha hW he r all
  have hp (i : raw G f) : i ∈ P i := (ConnectedActivityE6.Coat.frames G S B).here _
  have H₁ := annotated_base (W:=P) v H.1 H.2 hp i
  have F₁ := annotated_log v F.1 F.2 i i
  let fc (u : ℝ) (y : Vec G c 1) := attenuation u - pie P (Q (shorter L) y) u i i
  let fi (u : ℝ) (y : Vec G c 1) := density (Q all y) u i i
  have hj : ∀ u ∈ Ioi (0:ℝ), jet v (fi u) l 0 - jet v (fc u) l 0 = J u := by
    intro u hu
    have full : ContDiffAt ℝ l.length (TestD.action (Q all) u) 0 :=
      action_smooth (IsUnit.mk0 _ (shift_posDef F.2.self_of_nhds hu.out.le).det_pos.ne')
        (smooth_of_le F.1 hl)
    have cut : ContDiffAt ℝ l.length (fun y => pie P (Q (shorter L) y) u) 0 := by
      have hq := mast S t (p:=p) (n:=n) hs ha hW he (change_draw r r 0 (fun _ _ => rfl)) (shorter L)
        (Set.left_mem_Icc.mpr zero_le_one)
      have hx := (glimpse_smooth hq (study P hp) hu.out.le (gum_pos G S.patch S.kernel p)).comp
        (0:Vec G c 1) (contDiffAt_id.prodMk (contDiffAt_const (c:=(0:ℝ))))
      simp_rw [pie_inspects P _ _ hp]
      apply (smooth_of_le hx hl).congr_of_eventuallyEq
      exact Eventually.of_forall fun y => congrArg (fun X => (study P hp).inspect X u)
        (now (allot r) (allot r) t p (shorter L) y).symm
    have hf : ContDiffAt ℝ l.length (fi u) 0 := by
      exact contDiffAt_const.sub ((TestD.evaluate i i).contDiff.contDiffAt.comp 0 full)
    have hc : ContDiffAt ℝ l.length (fc u) 0 :=
      contDiffAt_const.sub ((TestD.evaluate i i).contDiff.contDiffAt.comp 0 cut)
    change _ = jet v (fun y => difference B L r t p W u y i i) l 0
    rw [←jet_sub v l hf hc]
    apply congrArg (fun z => jet v z l 0)
    funext y
    rw [diag]
    simp [fc,fi,density,P,Q]
  have hi : IntegrableOn J (Ioi 0) := ((F₁.2 l hl).1.sub (H₁.2 l hl).1).congr_fun hj measurableSet_Ioi
  refine ⟨hi,?_⟩
  change jet v (fun y => letterBase P (Q (shorter L) y) i - logKernel (Q all y) i i) l 0 = _
  rw [jet_sub v l (smooth_of_le H₁.1 hl) (smooth_of_le F₁.1 hl), (H₁.2 l hl).2,(F₁.2 l hl).2,
    ←setIntegral_congr_fun measurableSet_Ioi hj,integral_sub (F₁.2 l hl).1 (H₁.2 l hl).1]
  abel

/-- Actual smooth germ of the retained paired scalar, for differentiating
its finite physical-root sum. -/
theorem paired_smooth (hs : 0 < σ) (ha : 0 ≤ A) (hW : Sheet W σ A)
    (he : Bid.Larger (G:=G) S) (r : Reserve S) (B L : ℕ) (i : raw G f) :
    ContDiffAt ℝ n (paired B L r t p W i) 0 := by
  let P := ConditionalCovarianceShutter.columns G S B
  have H := gram (t:=t) (p:=p) (n:=n) hs ha hW he r (shorter L)
  have F := gram (t:=t) (p:=p) (n:=n) hs ha hW he r all
  have h₁ := annotated_base (W:=P) (ray G c) H.1 H.2
    (fun _ => (ConnectedActivityE6.Coat.frames G S B).here _) i
  have h₂ := annotated_log (ray G c) F.1 F.2 i i
  have h : ContDiffAt ℝ n (rooted B L r t p W i) 0 := h₁.1.sub h₂.1
  exact contDiffAt_const.mul (h.sub contDiffAt_const)

private theorem charged (hs : 0 < σ) (ha : 0 ≤ A) (hW : Sheet W σ A) (he : Bid.Larger (G:=G) S)
    (r : Reserve S) (B L : ℕ) (i : raw G f) (l : List (raw G c)) (hl : l.length ≤ n) (hz : l ≠ []) :
    jet (ray G c) (paired B L r t p W i) l 0 =
    -(1/2:ℝ) * ∫ u in Ioi 0, jet (ray G c) (fun y => difference B L r t p W u y i i) l 0 := by
  let P := ConditionalCovarianceShutter.columns G S B
  have H := gram (t:=t) (p:=p) (n:=n) hs ha hW he r (shorter L)
  have F := gram (t:=t) (p:=p) (n:=n) hs ha hW he r all
  have h₁ := annotated_base (W:=P) (ray G c) H.1 H.2
    (fun _ => (ConnectedActivityE6.Coat.frames G S B).here _) i
  have h₂ := annotated_log (ray G c) F.1 F.2 i i
  have h : ContDiffAt ℝ l.length (rooted B L r t p W i) 0 := smooth_of_le (h₁.1.sub h₂.1) hl
  change jet (ray G c) (fun x => (1/2:ℝ) • (rooted B L r t p W i x - rooted B L r t p W i 0)) l 0 = _
  rw [jet_const_smul _ _ _ (h.sub contDiffAt_const),jet_sub _ _ h contDiffAt_const,
    jet_const _ _ hz,sub_zero,(integral hs ha hW he r B L i l hl).2,smul_eq_mul]
  ring

/-- Ordinary and single-physical-tag positive-order half-log jets at a
specified root. The logarithmic integral consumes no period factor. -/
theorem one_tag (hs : 0 < σ) (ha : 0 ≤ A) (hW : Sheet W σ A) (he : Bid.Larger (G:=G) S)
    (B L : ℕ) (r s : Reserve S) (v : Site c) (h : ∀ w, w ≠ v → r w = s w)
    (i : raw G f) (l : List (raw G c)) (hl : l.length < n) (hz : l ≠ []) :
    let d := width G S.patch S.kernel p n A σ
    let M := windowPrice G S.patch S.kernel p n A σ 0 B + diminish G S.patch S.kernel p n L A σ 0
    let y := home S i
    let P := (marks G c d).pay l y
    let K (r : Reserve S) := jet (ray G c) (paired B L r t p W i) l 0
    P * |K r| ≤ M/2 ∧ (native c).weight d y v * P * |K s - K r| ≤ M/2 := by
  intro d M y P K
  let J (r : Reserve S) (u : ℝ) := jet (ray G c) (fun z => difference B L r t p W u z i i) l 0
  have hi (r : Reserve S) : IntegrableOn (J r) (Ioi 0) := (integral hs ha hW he r B L i l hl.le).1
  have answer (r : Reserve S) : K r = -(1/2:ℝ) * ∫ u in Ioi 0, J r u :=
    charged hs ha hW he r B L i l hl.le hz
  have hP : 0 ≤ P := (FreeResolvent.Mark.pay_pos ..).le
  have hJ (r : Reserve S) {u : ℝ} (hu : 0 ≤ u) : J r u = jet (ray G c) (difference B L r t p W u) l 0 i i :=
    TestD.entry _ l (smooth_of_le (regular hs ha hW he hu B L r y).smooth hl.le) i i
  have hF := Differential.Speech.judge hP (hi r) (C:=M) (by
    intro u hu
    have H := ((regular (t:=t) (p:=p) (n:=n) hs ha hW he hu.out.le B L r y).bound l hl.le).row.entry i i
    rw [spectral_price,Cost.weight_self,one_mul] at H
    rw [hJ r hu.out.le]
    exact H)
  have hV := Differential.Speech.judge (mul_nonneg ((native c).weight_nn ..) hP) ((hi s).sub (hi r)) (C:=M) (by
    intro u hu
    have H := ((tagged (t:=t) (p:=p) (n:=n) hs ha hW he hu.out.le B L r s v h l hl).test i i).1
    rw [Matrix.sub_apply,Cost.weight_self,one_mul,spectral_price] at H
    change _ * |J s u - J r u| ≤ _
    rw [hJ s hu.out.le,hJ r hu.out.le]
    exact H)
  constructor
  · rw [answer,abs_mul,abs_neg,abs_of_nonneg (by norm_num : (0:ℝ)≤1/2)]
    linarith only [hF.2]
  rw [answer,answer,←mul_sub,←integral_sub (hi s) (hi r),abs_mul,abs_neg,
    abs_of_nonneg (by norm_num : (0:ℝ)≤1/2)]
  have hv : (native c).weight d y v * P * |∫ u in Ioi 0, J s u - J r u| ≤ M := hV.2
  linarith only [hv]

open FreeResolvent.Stars

private theorem center_weight {j : ℕ} (d : ℝ) (i : raw G f) (k : Fin j → raw G c) :
    (marks G c d).pay (List.ofFn k) (home S i) =
      Real.exp (d * costs (native c) (home S i) (home S i) (home S i) (hearth ∘ k)) := by
  simpa only [Cost.weight_self, one_mul, mul_one] using
    anchor_weight (native c) (home S) (hearth (G:=G) (r:=1)) i i k d (1:ℝ)

/-- Diagonal entries carry the original fine root and each independent
coarse derivative. The second endpoint repeats the first, so summing it
counts each rooted half-log coefficient exactly once. -/
theorem position_sum (hs : 0 < σ) (ha : 0 ≤ A) (hW : Sheet W σ A) (he : Bid.Larger (G:=G) S)
    (B L : ℕ) (j : ℕ) (hj₀ : 0 < j) (hj : j < n) :
    let γ := together G S.patch S.kernel p n A σ
    let V := totalFoot G S.patch S.kernel p n A σ
    let M := windowPrice G S.patch S.kernel p n A σ 0 B + diminish G S.patch S.kernel p n L A σ 0
    let F (r : Reserve S) (i z : raw G f) (k : Fin j → raw G c) :=
      if i = z then jet (ray G c) (paired B L r t p W i) (List.ofFn k) 0 else 0
    (∀ (r : Reserve S) (v : Site c) (g : raw G f → raw G f → (Fin j → raw G c) → Bool),
      (∀ i z k, g i z k = true → v = home S i ∨ v = home S z ∨ ∃ m, v = hearth (k m)) →
      NearStar j (native c) (home S) (home S) hearth v g γ (crowd j (M/2) V) (F r)) ∧
    ∀ (r s : Reserve S) (v : Site c), (∀ w, w ≠ v → r w = s w) →
      NearStar j (native c) (home S) (home S) hearth v (fun _ _ _ => true) γ (crowd j (M/2) V)
        (fun i z k => F s i z k - F r i z k) := by
  classical
  intro γ V M F
  obtain ⟨hγ,hd,hV,hf,hc⟩ := sum_schedule (G:=G) (S:=S) (p:=p) hj.le hs ha
  have hM : 0 ≤ M / 2 := div_nonneg
    (add_nonneg (window_price_nonneg hs ha (le_refl 0)) (cut_nonneg hs ha (le_refl 0) L))
    (by norm_num)
  have hz (k : Fin j → raw G c) : List.ofFn k ≠ [] := fun h =>
    (Nat.ne_of_gt hj₀) (by simpa using congrArg List.length h)
  have hlen (k : Fin j → raw G c) : (List.ofFn k).length < n := by simpa using hj
  constructor
  · intro r v g hg
    apply sums_no_mark hγ.le hM hd hV _ hg hf hf hc
    intro i z k
    by_cases hiz : i = z
    · subst z
      rw [←center_weight]
      simpa only [F,if_pos rfl] using
        (one_tag (t:=t) (p:=p) hs ha hW he B L r r v (fun _ _ => rfl) i _ (hlen k) (hz k)).1
    simpa only [F,if_neg hiz,abs_zero,mul_zero] using hM
  intro r s v h
  apply sums_tagged hγ.le hM hd hV _ hf hf hc
  intro i z k
  by_cases hiz : i = z
  · subst z
    rw [←center_weight]
    simpa only [F,if_pos rfl] using
      (one_tag (t:=t) (p:=p) hs ha hW he B L r s v h i _ (hlen k) (hz k)).2
  simpa only [F,if_neg hiz,sub_self,abs_zero,mul_zero] using hM

end YM.Integration.ConditionalCovarianceLogarithm

namespace YM.Integration.RunConditionalCovariance
open Function Set Lattice RG Wilson Tree Precision Pressure
  PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Greenbelt FreeResolvent FreeResolvent.TestD FreeResolvent.Affine FreeResolvent.Stars
  ConditionalTreeCovarianceJets ConditionalTreeCovarianceSums ConditionalCovarianceCutoff
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {R : Run G} {N per m : ℕ} {hm : m < N}
  (P : ActualRunSpring.Packet R N per m hm)

include P in
theorem comparison (n j : ℕ) (hj : j < n) (t : (R.alloy.B.a.clock.op m per).Choices) (u : ℝ) (hu : 0 ≤ u)
    (mode : ColumnMode := .symmetric) :
    let p := (R.alloy.B.a.params (m+1)).clip; let A := (R.alloy.B.a.params (m+1)).paths; let σ := (R.alloy.B.a.params (m+1)).width
    let d := width G ((R.alloy.B.a.clock.op m 0).patch) (R.alloy.B.a.clock.kernel) p n A σ
    let γ := together G ((R.alloy.B.a.clock.op m 0).patch) (R.alloy.B.a.clock.kernel) p n A σ
    let Z := totalFoot G ((R.alloy.B.a.clock.op m 0).patch) (R.alloy.B.a.clock.kernel) p n A σ
    let rate := min (((n+1:ℕ):ℝ)*d) (σ/800000)
    let C := ConditionalTreeCovarianceJets.windowPrice G ((R.alloy.B.a.clock.op m 0).patch) (R.alloy.B.a.clock.kernel) p n A σ 0 0 + diminish G ((R.alloy.B.a.clock.op m 0).patch) (R.alloy.B.a.clock.kernel) p n 0 A σ 0
    let K (r : Reserve (R.alloy.B.a.clock.op m per)) (i z : raw G (R.alloy.B.a.S.side (m+1) per)) (l : Fin j → raw G (R.alloy.B.a.S.side m per)) :=
      iteratedFDeriv ℝ j (columns mode (Pressure.radiusB (R.alloy.B.a.clock.hatBeta m)) (Pressure.Stores.till (R.alloy.B.a.clock.hatBeta m))
        r t p (R.alloy.B.kin.path N (m+1)) u) 0 (ray G (R.alloy.B.a.S.side m per) ∘ l) i z
    0 < rate ∧ 0 < γ/4 ∧ (∀ (r : Reserve (R.alloy.B.a.clock.op m per)) (v : Site (R.alloy.B.a.S.side m per)) (g : raw G (R.alloy.B.a.S.side (m+1) per) → raw G (R.alloy.B.a.S.side (m+1) per) → (Fin j → raw G (R.alloy.B.a.S.side m per)) → Bool),
      (∀ i z l, g i z l = true → v = home (R.alloy.B.a.clock.op m per) i ∨ v = home (R.alloy.B.a.clock.op m per) z ∨ ∃ a, v = hearth (l a)) →
      NearStar j (taxi (R.alloy.B.a.S.side m per)) (home (R.alloy.B.a.clock.op m per)) (home (R.alloy.B.a.clock.op m per)) hearth v g (γ/4) (crowd j (C*Real.exp (-rate*(Pressure.radiusB (R.alloy.B.a.clock.hatBeta m)))*drain u^2) Z) (K r)) ∧
    ∀ (r s : Reserve (R.alloy.B.a.clock.op m per)) (v : Site (R.alloy.B.a.S.side m per)), (∀ w, w ≠ v → r w = s w) →
      NearStar j (taxi (R.alloy.B.a.S.side m per)) (home (R.alloy.B.a.clock.op m per)) (home (R.alloy.B.a.clock.op m per)) hearth v (fun _ _ _ => true) (γ/4)
        (crowd j (C*Real.exp (-rate*(Pressure.radiusB (R.alloy.B.a.clock.hatBeta m)))*drain u^2) Z) (fun i z l => K s i z l - K r i z l) := by
  intro p A σ d γ Z rate C K
  have he : Bid.Larger (G:=G) (R.alloy.B.a.clock.op m per) := (P.spring.H.houses P.point).laws.data.room.larger
  have hW := (R.alloy.B.support.cap N (m+1) hm).rows
  have H := position_sum (p:=p) (t:=t) (n:=n) (R.alloy.B.a.params (m+1)).width_pos (R.alloy.B.a.params (m+1)).paths_pos.le hW he hu
    (Pressure.radiusB (R.alloy.B.a.clock.hatBeta m)) (Pressure.Stores.till (R.alloy.B.a.clock.hatBeta m)) j hj mode
  have hB : 100000 ≤ (Pressure.radiusB (R.alloy.B.a.clock.hatBeta m)) := by
    have hb := (P.spring.H.houses P.point).laws.data.room.frame
    omega
  have F := funded_price (S:=(R.alloy.B.a.clock.op m per)) (G:=G) (p:=p) (n:=n) (u:=u) (R.alloy.B.a.params (m+1)).width_pos (R.alloy.B.a.params (m+1)).paths_pos.le (Pressure.radiusB (R.alloy.B.a.clock.hatBeta m)) hB
  have sched := sum_schedule (S:=(R.alloy.B.a.clock.op m per)) (G:=G) (p:=p) hj.le (R.alloy.B.a.params (m+1)).width_pos (R.alloy.B.a.params (m+1)).paths_pos.le
  have hγ : 0 < γ := sched.1
  have hZ : 0 ≤ Z := sched.2.2.1
  have paid := mul_le_mul_of_nonneg_left F.2 (mul_nonneg (mul_nonneg hZ hZ) (pow_nonneg hZ j))
  refine ⟨F.1,div_pos hγ (by norm_num),fun r v g hg =>
    ConditionalCovarianceLayers.nearest_neighbor hγ.le ⟨((H.1 r v g hg).limit).trans paid⟩,?_⟩
  exact fun r s v hh => ConditionalCovarianceLayers.nearest_neighbor hγ.le ⟨((H.2 r s v hh).limit).trans paid⟩

end YM.Integration.RunConditionalCovariance

namespace YM.Integration.ConditionalStationarySlope
open Function Filter Lattice Wilson RG Precision Exterior Tree Bloch Matrix
open Pressure PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Greenbelt Comparison.RG02
open scoped Topology Classical ContDiff

section forest
variable {G : Gauge} {c f : Side} {S : StepData c f}

/-- The tree hike used by the stationary lift only consults the selected
forest at its own true block. Each successive tree step stays there. -/
theorem hikes (r s : Reserve S) (v : Site c) (h : ∀ w, w ≠ v → r w = s w)
    (x : Site f) (hx : S.ratio.parent x ≠ v) : (allot r).hike x = (allot s).hike x := by
  conv_lhs => rw [Forest.hike]
  conv_rhs => rw [Forest.hike]
  by_cases hl : leaf S.ratio x
  · simp only [dif_pos hl]
    have hu : (allot r).up x = (allot s).up x := by
      change (r (S.ratio.parent x)).up x = (s (S.ratio.parent x)).up x
      rw [h _ hx]
    rw [←hu]
    have hp : S.ratio.parent (x + ((allot r).up x).vec) ≠ v := by
      rw [(allot r).stays x hl]
      exact hx
    exact congrArg (List.cons ((allot r).up x)) (hikes r s v h _ hp)
  simp only [dif_neg hl]
termination_by (allot r).height x
decreasing_by exact (allot r).rise x hl

/-- Only the two endpoint blocks of the fine bond can change the stationary
displacement. The genuine gauge-root terms can therefore be removed exactly
away from both, before summing independent coarse inputs. -/
theorem transfer_away (W : Matrix (Body 1 f) (Body 1 c) ℝ) (r s : Reserve S) (v : Site c)
    (h : ∀ w, w ≠ v → r w = s w) (x : Site f) (a : Axis)
    (hx : S.ratio.parent x ≠ v) (hx' : S.ratio.parent (x + step a) ≠ v) (b : form 1 c) :
    (extracted S (allot r) W *ᵥ b) (x,coord a) = (extracted S (allot s) W *ᵥ b) (x,coord a) := by
  have val (z : Site f) (hz : S.ratio.parent z ≠ v) :
      (straighten S (allot r) W *ᵥ b) (z,vac) = (straighten S (allot s) W *ᵥ b) (z,vac) := by
    rw [books,books,hikes r s v h z hz]
  simp only [extracted,Matrix.add_mulVec,←Matrix.mulVec_mulVec,Pi.add_apply,d_sites,
    val _ hx,val _ hx']
end forest

variable {G : Gauge} (R : Run G) (Y : Bulk.Chain R.family.path)
  (N p m : ℕ) (hm : m < N)

/-- Both sides use the original actual forest, before taking its law. -/
theorem relative_slope (r : Reserve (R.family.path.levels.clock.op m p)) (t : (R.family.path.levels.clock.op m p).Choices)
    (b : fieldDir G (R.family.path.levels.S.side m p) 1) :
    fderiv ℝ ((Y.step N m p hm).b (allot r)) 0 b =
      relative (allot r) (installed (R.family.path.levels.clock.op m p).ratio (R.alloy.B.M.towers N m).A0) b := by
  rw [ActualKernelIdentification.stationary_fderiv R Y N p m hm (allot r) t]
  have h := (CommonConstruction.runAlong R).home (allot r) hm
  exact (Push.side _ (h.2.1.2.1.differentiableAt (by simp)) b).unique (h.2.2.2.2.1 b)

/-- Restrict the full response minus the copied coarse field to an actual
live fine link. The known row cancellations for this response are physical. -/
theorem physical (r : Reserve (R.family.path.levels.clock.op m p)) (t : (R.family.path.levels.clock.op m p).Choices)
    (b : fieldDir G (R.family.path.levels.S.side m p) 1) (i : (allot r).Free) :
    (fderiv ℝ ((Y.step N m p hm).b (allot r)) 0 b) i =
      AnalyticNext.ConnectedActivity.Aff.attempt (Push.PriceCompiler.Permit.tube R.alloy.B.M R.alloy.B.kin.path N m p) (allot r) b i.val := by
  rw [relative_slope R Y N p m hm r t b]
  ext color
  rfl

/-- Embed the actual derivative in the common raw link array. The canonical
stationary lift vanishes on the tree and gives the derivative at every
other coordinate with the original sign. -/
theorem completed (r : Reserve (R.family.path.levels.clock.op m p)) (t : (R.family.path.levels.clock.op m p).Choices)
    (b : fieldDir G (R.family.path.levels.S.side m p) 1)
    (i : Edge (Site (R.family.path.levels.S.side (m+1) p))) :
    (if hi : i ∉ (allot r).trunks then
      (fderiv ℝ ((Y.step N m p hm).b (allot r)) 0 b) ⟨i,hi⟩ else 0) =
      AnalyticNext.ConnectedActivity.Aff.attempt (Push.PriceCompiler.Permit.tube R.alloy.B.M R.alloy.B.kin.path N m p) (allot r) b i := by
  by_cases hi : i ∉ (allot r).trunks
  · rw [dif_pos hi]
    exact physical R Y N p m hm r t b ⟨i,hi⟩
  rw [dif_neg hi]
  exact (AnalyticNext.ConnectedActivity.Aff.attempt_root (Push.PriceCompiler.Permit.tube R.alloy.B.M R.alloy.B.kin.path N m p) (allot r) b i (not_not.mp hi)).symm

/-- The one-physical-tag first derivative is supported on the two genuine
endpoint blocks of its fine link, for every independent coarse direction. -/
theorem stationary_away (r s : Reserve (R.family.path.levels.clock.op m p)) (v : Site (R.family.path.levels.S.side m p))
    (h : ∀ w, w ≠ v → r w = s w) (t : (R.family.path.levels.clock.op m p).Choices)
    (b : fieldDir G (R.family.path.levels.S.side m p) 1)
    (x : Site (R.family.path.levels.S.side (m+1) p)) (a : Axis)
    (hx : (R.family.path.levels.clock.op m p).ratio.parent x ≠ v) (hx' : (R.family.path.levels.clock.op m p).ratio.parent (x + step a) ≠ v) :
    (if hi : (x,a) ∉ (allot r).trunks then
      (fderiv ℝ ((Y.step N m p hm).b (allot r)) 0 b) ⟨(x,a),hi⟩ else 0) =
    (if hi : (x,a) ∉ (allot s).trunks then
      (fderiv ℝ ((Y.step N m p hm).b (allot s)) 0 b) ⟨(x,a),hi⟩ else 0) := by
  rw [completed R Y N p m hm r t b,completed R Y N p m hm s t b]
  ext color
  exact congrArg (fun u : ℝ => u - (linearCopy (R.family.path.levels.clock.op m p).ratio (collect G b)) (x,a) color)
    (transfer_away (installed (R.family.path.levels.clock.op m p).ratio (R.alloy.B.M.towers N m).A0) r s v h x a hx hx' (parts G 1 b color))

end YM.Integration.ConditionalStationarySlope

namespace YM.Integration.ConditionalStationaryTagPrice
open Function Filter Lattice Wilson RG Precision Exterior Tree Bloch FreeResolvent
open Pressure PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Greenbelt Comparison.RG02
open Progress.StationaryScenes YM.Next.Free
open scoped Topology Classical BigOperators
variable {G : Gauge} {c f : Side} (S : StepData c f)

/-- Replace the torus distance from a fine link to a coarse seed by the
converted cross weight. The output lies in one of the two endpoint blocks. -/
private lemma weight {η : ℝ} (hη : 0 ≤ η) (v : Site c) (x : Site f) (y : Site c)
    (hx : separation v (S.ratio.parent x) ≤ 1) :
    (native c).weight η v (S.ratio.parent x) * (native c).weight η v y ≤
      (Real.exp (4*η) * (native c).weight (-η) v (S.ratio.parent x)) *
        crossW S.ratio η x y := by
  have hL : 0 < (S.ratio.count.val : ℝ) := by exact_mod_cast S.ratio.count.property
  have hr := Corona.foreshorten S.ratio x (S.ratio.embed y)
  rw [S.ratio.embed_parent] at hr
  have hr' : (separation (S.ratio.parent x) y : ℝ) ≤
      (separation x (S.ratio.embed y) : ℝ)/S.ratio.count.val+1 := by
    have hn : (S.ratio.count.val : ℝ) * separation (S.ratio.parent x) y ≤
        separation x (S.ratio.embed y) + S.ratio.count.val := by exact_mod_cast hr
    calc
      _ ≤ ((separation x (S.ratio.embed y) : ℝ) + S.ratio.count.val)/S.ratio.count.val :=
        (le_div_iff₀ hL).2 (by linarith only [hn])
      _ = _ := by rw [add_div,div_self hL.ne']
  have ht : (separation v y : ℝ) ≤ separation v (S.ratio.parent x) + separation (S.ratio.parent x) y :=
    by exact_mod_cast separation_triangle v (S.ratio.parent x) y
  have hx' : (separation v (S.ratio.parent x) : ℝ) ≤ 1 := by exact_mod_cast hx
  have hz : (separation v (S.ratio.parent x) : ℝ) + separation v y ≤
      4-separation v (S.ratio.parent x) + (separation x (S.ratio.embed y) : ℝ)/S.ratio.count.val := by
    linarith
  change Real.exp _ * Real.exp _ ≤ (Real.exp _ * Real.exp _) * Real.exp _
  rw [← Real.exp_add,← Real.exp_add,← Real.exp_add,Real.exp_le_exp]
  change η * (separation v (S.ratio.parent x) : ℝ) + η * (separation v y : ℝ) ≤
    (4*η+(-η)*(separation v (S.ratio.parent x) : ℝ)) + η*((separation x (S.ratio.embed y) : ℝ)/S.ratio.count.val)
  nlinarith only [mul_le_mul_of_nonneg_left hz hη]

private lemma positions (η : ℝ) (hη : 0 < η) :
    (native c).Volume (fun i : Body 1 f => S.ratio.parent i.1) η
      (torusPay (Co S.patch.L (TypeFace 1)) η) := by
  let E := splitCo S.ratio (TypeFace 1)
  rw [show (fun i : Body 1 f => S.ratio.parent i.1) = Prod.fst ∘ E from
    funext fun i => by simp only [E,Function.comp_apply,split_co]]
  exact (volume c _ _ hη).comp E.injective

/-- One true draw changes only rows within one coarse step of the marked
block. The statement holds before taking any averages. -/
private lemma away (W : Matrix (Body 1 f) (Body 1 c) ℝ) (r s : Reserve S) (v : Site c)
    (h : ∀ w, w ≠ v → r w = s w) (i : Body 1 f) (j : Body 1 c)
    (hi : ¬ separation v (S.ratio.parent i.1) ≤ 1) :
    extracted S (allot r) W i j = extracted S (allot s) W i j := by
  rcases i with ⟨x,i⟩
  obtain ⟨a,rfl⟩ := axisEquiv.surjective i
  have hx : S.ratio.parent x ≠ v := by
    intro e
    apply hi
    simp [e]
  have he : S.ratio.parent (x+step a) ≠ v := by
    intro e
    apply hi
    rw [separation_comm]
    exact e ▸ Work.E03.parent_step S x a
  have H := ConditionalStationarySlope.transfer_away W r s v h x a hx he (Pi.single j 1)
  change extracted S (allot r) W (x,coord a) j=extracted S (allot s) W (x,coord a) j
  simpa only [Matrix.mulVec_single_one,Matrix.col_apply] using H

/-- Retaining the genuine changed block, sum the absolute difference of
the actual stationary transfer over *both* physical positions. The common
physical coarse copy cancels identically between the two forests. -/
theorem one_block (P : Teller G) (T : Tube G S) (hT : P.Funds S T)
    (r s : Reserve S) (v : Site c) (h : ∀ w, w ≠ v → r w = s w) :
    ∑ i : Body 1 f, ∑ j : Body 1 c,
      (native c).weight P.η v (S.ratio.parent i.1) * (native c).weight P.η v j.1 *
        |extracted S (allot r) (installed S.ratio T.R.A0) i j -
          extracted S (allot s) (installed S.ratio T.R.A0) i j| ≤
      (Real.exp (4*P.η) * (2 * Response.total S.patch.J P.η P.C)) *
        torusPay (Co S.patch.L (TypeFace 1)) P.η := by
  classical
  let A (q : Reserve S) := extracted S (allot q) (installed S.ratio T.R.A0)
  let F := Response.total S.patch.J P.η P.C
  have hs : T.R.A0.strip P.η (P.C/(S.ratio.count.val : ℝ)) := by
    simpa [advanceC,StepData.ratio] using (hT.crosses.2.2.2 [] (Nat.zero_le _)).1
  have rows (q : Reserve S) (i : Body 1 f) :
      ∑ j : Body 1 c, crossW S.ratio P.η i.1 j.1 * |A q i j| ≤ F := by
    simpa only [Real.norm_eq_abs] using Response.response_price S P.width.le hs (allot q) i
  have hF : 0 ≤ F := by
    let i : Body 1 f := (0,coord 0)
    refine (Finset.sum_nonneg fun j _ => mul_nonneg (Real.exp_pos _).le (abs_nonneg _)).trans (rows r i)
  have row (i : Body 1 f) :
      ∑ j : Body 1 c, (native c).weight P.η v (S.ratio.parent i.1) * (native c).weight P.η v j.1 *
        |A r i j - A s i j| ≤
      (Real.exp (4*P.η) * (2*F)) * (native c).weight (-P.η) v (S.ratio.parent i.1) := by
    by_cases hi : separation v (S.ratio.parent i.1) ≤ 1
    · let p := Real.exp (4*P.η) * (native c).weight (-P.η) v (S.ratio.parent i.1)
      have hp : 0 ≤ p := mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
      calc
        _ ≤ ∑ j : Body 1 c, p * (crossW S.ratio P.η i.1 j.1 * |A r i j| +
              crossW S.ratio P.η i.1 j.1 * |A s i j|) := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [←mul_add,←mul_assoc]
          exact mul_le_mul (weight S P.width.le v i.1 j.1 hi) (abs_sub _ _) (abs_nonneg _) (mul_nonneg hp (Real.exp_pos _).le)
        _ = p * ((∑ j : Body 1 c, crossW S.ratio P.η i.1 j.1 * |A r i j|) +
             ∑ j : Body 1 c, crossW S.ratio P.η i.1 j.1 * |A s i j|) := by
          rw [←Finset.mul_sum,Finset.sum_add_distrib]
        _ ≤ p * (2*F) := mul_le_mul_of_nonneg_left (by linarith [rows r i,rows s i]) hp
        _ = _ := by unfold p; ring
    · have z (j : Body 1 c) : A r i j = A s i j := away S _ r s v h i j hi
      simp only [z,sub_self,abs_zero,mul_zero,Finset.sum_const_zero]
      exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (by linarith)) (Real.exp_pos _).le
  calc
    _ ≤ ∑ i : Body 1 f, (Real.exp (4*P.η) * (2*F)) * (native c).weight (-P.η) v (S.ratio.parent i.1) :=
      Finset.sum_le_sum fun i _ => row i
    _ ≤ _ := by
      rw [←Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left ((positions S P.η P.width).bound v)
        (mul_nonneg (Real.exp_pos _).le (by linarith))

/-- A genuine single coarse bond and Lie-color direction. -/
def seed (j : Body 1 c) (b : G.ColorIndex) : fieldDir G c 1 := fun k =>
  WithLp.toLp 2 fun a => if k=j ∧ a=b then 1 else 0

private lemma parts_seed (j : Body 1 c) (a : G.ColorIndex) :
    parts G 1 (seed j a) a = Pi.single j 1 := by
  funext k
  by_cases hk : k=j <;> simp [parts,seed,hk,eq_comm]

private theorem attempt_change (T : Tube G S) (F F' : Forest S.ratio) (i : Body 1 f) (j : Body 1 c) (a : G.ColorIndex) :
    (AnalyticNext.ConnectedActivity.Aff.attempt T F (seed j a) (i.1,axisEquiv.symm i.2)) a -
      (AnalyticNext.ConnectedActivity.Aff.attempt T F' (seed j a) (i.1,axisEquiv.symm i.2)) a =
    extracted S F (installed S.ratio T.R.A0) i j - extracted S F' (installed S.ratio T.R.A0) i j := by
  have hh (Y : Forest S.ratio) : (AnalyticNext.ConnectedActivity.Aff.station T Y (seed j a) i) a =
      extracted S Y (installed S.ratio T.R.A0) i j := by
    change Matrix.mulVec (extracted S Y (installed S.ratio T.R.A0)) (parts G 1 (seed j a) a) i = _
    simp only [parts_seed,Matrix.mulVec_single_one,Matrix.col_apply]
  have e : (i.1,coord (axisEquiv.symm i.2))=i := by rw [←coord_map,axisEquiv.apply_symm_apply]
  simp only [AnalyticNext.ConnectedActivity.Aff.attempt,Pi.sub_apply,PiLp.sub_apply,collect,e,hh,sub_sub_sub_cancel_right]

variable (R : Run G) (Y : Bulk.Chain R.family.path) (N p m : ℕ) (hm : m < N)

/-- First derivative of the genuine conditional BB02 stationary point,
completed by zero on its erased tree links. -/
def stationary (r : Reserve (R.family.path.levels.clock.op m p)) (i : Body 1 (R.family.path.levels.S.side (m+1) p)) (j : Body 1 (R.family.path.levels.S.side m p)) (a : G.ColorIndex) : ℝ :=
  let e := (i.1,axisEquiv.symm i.2)
  (if hi : e ∉ (allot r).trunks then
    (fderiv ℝ ((Y.step N m p hm).b (allot r)) 0 (seed j a)) ⟨e,hi⟩ else 0) a

/-- At two genuine forest draws the copied coarse background cancels
exactly. This identifies the transfer estimate with the BB02 stationary
first derivative on the common ambient fine-edge coordinates. -/
theorem stationary_change (r s : Reserve (R.family.path.levels.clock.op m p)) (t : (R.family.path.levels.clock.op m p).Choices)
    (i : Body 1 (R.family.path.levels.S.side (m+1) p)) (j : Body 1 (R.family.path.levels.S.side m p)) (a : G.ColorIndex) :
    stationary R Y N p m hm r i j a - stationary R Y N p m hm s i j a =
      extracted (R.family.path.levels.clock.op m p) (allot r) (installed (R.family.path.levels.clock.op m p).ratio (Push.PriceCompiler.Permit.tube R.alloy.B.M R.alloy.B.kin.path N m p).R.A0) i j -
        extracted (R.family.path.levels.clock.op m p) (allot s) (installed (R.family.path.levels.clock.op m p).ratio (Push.PriceCompiler.Permit.tube R.alloy.B.M R.alloy.B.kin.path N m p).R.A0) i j := by
  let e := (i.1,axisEquiv.symm i.2)
  let T := Push.PriceCompiler.Permit.tube R.alloy.B.M R.alloy.B.kin.path N m p
  have hr : stationary R Y N p m hm r i j a = (AnalyticNext.ConnectedActivity.Aff.attempt T (allot r) (seed j a) e) a :=
    congrArg (fun z : G.Color => z a) (ConditionalStationarySlope.completed R Y N p m hm r t (seed j a) e)
  have hs : stationary R Y N p m hm s i j a = (AnalyticNext.ConnectedActivity.Aff.attempt T (allot s) (seed j a) e) a :=
    congrArg (fun z : G.Color => z a) (ConditionalStationarySlope.completed R Y N p m hm s t (seed j a) e)
  exact (congrArg₂ (fun u v : ℝ => u-v) hr hs).trans (attempt_change _ T (allot r) (allot s) i j a)

/-- One physical tag, one retained position, and every rooted entry of the
actual (forest conditional) first derivative. The Teller is uniform over
all volumes and its full periodized tree-lift rows supply the price. -/
theorem paid_stationary (P : Teller G) (hP : P.Funds (R.family.path.levels.clock.op m p) (Push.PriceCompiler.Permit.tube R.alloy.B.M R.alloy.B.kin.path N m p))
    (r s : Reserve (R.family.path.levels.clock.op m p)) (v : Site (R.family.path.levels.S.side m p)) (h : ∀ w, w ≠ v → r w = s w)
    (t : (R.family.path.levels.clock.op m p).Choices) (a : G.ColorIndex) :
    ∑ i : Body 1 (R.family.path.levels.S.side (m+1) p), ∑ j : Body 1 (R.family.path.levels.S.side m p),
      (native (R.family.path.levels.S.side m p)).weight P.η v ((R.family.path.levels.clock.op m p).ratio.parent i.1) * (native (R.family.path.levels.S.side m p)).weight P.η v j.1 *
      |stationary R Y N p m hm r i j a - stationary R Y N p m hm s i j a| ≤
      (Real.exp (4*P.η) * (2 * Response.total (R.family.path.levels.clock.op m p).patch.J P.η P.C)) *
        torusPay (Co (R.family.path.levels.clock.op m p).patch.L (TypeFace 1)) P.η := by
  simp only [stationary_change R Y N p m hm r s t]
  exact one_block (R.family.path.levels.clock.op m p) P (Push.PriceCompiler.Permit.tube R.alloy.B.M R.alloy.B.kin.path N m p) hP r s v h

end YM.Integration.ConditionalStationaryTagPrice
