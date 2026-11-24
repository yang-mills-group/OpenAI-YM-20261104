import YM.Integration.ConditionalAffineMeanPrice
import YM.Integration.ConditionalAffineRegularMean

/-! Period-uniform ordinary and changed-tree tensors of the full independent affine center. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ConditionalAffineIdealMean
open Function Filter Set Lattice Wilson RG Precision Tree Matrix Bloch
open FreeResolvent FreeResolvent.Affine FreeResolvent.TestD FreeResolvent.Lever FreeResolvent.Mark FreeResolvent.Stars
open Pressure Pressure.Tube Pressure.Stores AnalyticBridge.GaussianFieldAlignment
open Next.Fluctuations.Sector
open Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Gaussian
open PhysicalNext.Repeat.Greenbelt ConditionalTreeCovarianceJets ConditionalTreeCovarianceSums ConditionalCovarianceCutoff
open ConditionalAffineMeanDifference ConditionalAffineLoadPrices ConditionalAffineMeanPrice
open scoped BigOperators Classical Topology ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f} (T : Tube G S) (x : ℝ) (k : S.Choices)
  {σ A Λ δ C : ℝ}
local notation "v₀" => ray G c

theorem flat (F : Forest S.ratio) (h : S.patch.Branches S.kernel G) (hW : T.up.Bounds T.high σ A Λ) :
    fullCenter T x k F 0=0 := by
  rw [(full_center T x k F h hW).eq_of_nhds]
  simp [wholeLoad,PhysicalAffineScalarUncut.offset_zero T k h]

theorem ordinary (F : Forest S.ratio) (he : Bid.Larger (G:=G) S) (hs : 0<σ) (ha : 0≤A)
    (hT : T.up.Bounds T.high σ A Λ) (n : ℕ) (hδ : 0<δ) (hC : 0≤C)
    (hr : ((n+1:ℕ):ℝ)*δ≤width G S.patch S.kernel T.high (n+1) A σ)
    (f : Paid (home S) δ C n (wholeLoad T k)) :
    let N := |earnings G S.patch S.kernel T.high (n+1) A σ|+1
    Paid (home S) δ ((2:ℝ)^n*(C*N)) n (fullCenter T x k F) := by
  intro N
  let d := width G S.patch S.kernel T.high (n+1) A σ
  have hdn : δ≤d := (show δ≤((n+1:ℕ):ℝ)*δ by
    have h₁ : (1:ℝ)≤((n+1:ℕ):ℝ) := by exact_mod_cast (show 1≤n+1 by omega)
    simpa only [one_mul] using mul_le_mul_of_nonneg_right h₁ hδ.le).trans hr
  have hnd : (n:ℝ)*δ≤d := (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ n) hδ.le).trans hr
  have hn : (n:ℝ)*δ≤4*((n+1+1:ℕ):ℝ)*d := hnd.trans (by
    apply le_mul_of_one_le_left (hδ.le.trans hdn)
    push_cast
    linarith [Nat.cast_nonneg (α:=ℝ) n])
  have J := PhysicalAffineScalarWeightChange.covariance_ordinary T k F hs ha (path_sheet T hT) he all (n+1)
  have J' := Paid.matrix_cost (Paid.matrix_weaken J hdn (Nat.le_succ n)) (add_le_add (le_abs_self _) (le_refl (1:ℝ)))
  exact (f.action hC J' (add_nonneg (abs_nonneg _) zero_le_one) hδ.le hn).negative.germ (full_center T x k F he.1 hT)

theorem tagged (r s : Reserve S) (tag : Site c) (hc : ∀ w, w≠tag → r w=s w)
    (he : Bid.Larger (G:=G) S) (hs : 0<σ) (ha : 0≤A) (hT : T.up.Bounds T.high σ A Λ)
    (n : ℕ) (hδ : 0<δ) (hC : 0≤C)
    (hr : ((n+1:ℕ):ℝ)*δ≤width G S.patch S.kernel T.high (n+1) A σ)
    (f : Paid (home S) δ C n (wholeLoad T k)) :
    let N := |earnings G S.patch S.kernel T.high (n+1) A σ|+1
    let V := torusPay (Co S.patch.L (PAC G 1)) δ
    ∀ (l : List (raw G c)), l.length≤n → ∀ i,
      (native c).weight δ (home S i) tag*(marks G c δ).pay l (home S i)*
      |jet v₀ (column (fun B => fullCenter T x k (allot s) B-fullCenter T x k (allot r) B)) l 0 i ()| ≤
        (2:ℝ)^l.length*(N*C*V) := by
  intro N V l hl i
  let K u := PhysicalAffineScalarTreeCovariance.observed (allot u) k T.high T.up all
  let Z := fun B => (K s B-K r B)*column (wholeLoad T k) B
  have hh : column (fun B => fullCenter T x k (allot s) B-fullCenter T x k (allot r) B) =ᶠ[𝓝 0] fun B => -Z B := by
    filter_upwards [full_center T x k (allot s) he.1 hT,full_center T x k (allot r) he.1 hT,
      uncut (T:=T) (k:=k) (allot s) hs ha he hT,uncut (T:=T) (k:=k) (allot r) hs ha he hT] with B h₁ h₂ h₃ h₄
    ext i j
    change (fullCenter T x k (allot s) B-fullCenter T x k (allot r) B) i = -((K s B-K r B)*ᵥ wholeLoad T k B) i
    rw [h₁,h₂,h₃,h₄,Matrix.sub_mulVec]
    simp only [Pi.neg_apply,Pi.sub_apply,K]; abel
  rw [TestD.identical v₀ hh l,minus l,Matrix.neg_apply,abs_neg]
  exact ideal r s tag hc he hs ha hT n hδ hC hr f l hl i

/-- Absolute entrywise jet norms for a matrix on the two original raw
Gaussian addresses and any number of independent coarse field variables. -/
def MatrixNorm (S : StepData c f) (j : ℕ) (γ C : ℝ)
    (F : Reserve S→Vec G c 1→Matrix (raw G f) (raw G f) ℝ) :=
  let J r (i b : raw G f) (q : Fin j→ raw G c) := iteratedFDeriv ℝ j (F r) 0 (ray G c∘q) i b
  (∀ (r : Reserve S) (o : Site c) (v : raw G f→ raw G f→(Fin j→ raw G c)→Bool),
    (∀ i b l, v i b l=true → o=home S i ∨ o=home S b ∨ ∃ t, o=hearth (l t)) →
    ConditionalPhysicalSpan.Rooted j (home S) (home S) hearth o v γ C (J r)) ∧
  ∀ (r s : Reserve S) (o : Site c), (∀ z, z≠o → r z=s z) →
    ConditionalPhysicalSpan.Rooted j (home S) (home S) hearth o (fun _ _ _ => true) γ C
      (fun i b l => J s i b l-J r i b l)

theorem MatrixNorm.increase {F : Reserve S→Vec G c 1→Matrix (raw G f) (raw G f) ℝ}
    {j : ℕ} {γ M N : ℝ} (h : MatrixNorm S j γ M F) (hM : M≤N) : MatrixNorm S j γ N F :=
  ⟨fun r o v hv => ⟨(h.1 r o v hv).limit.trans hM⟩,fun r s o hv => ⟨(h.2 r s o hv).limit.trans hM⟩⟩

theorem MatrixNorm.add {F H : Reserve S→Vec G c 1→Matrix (raw G f) (raw G f) ℝ}
    {j : ℕ} {γ M N : ℝ} (hF : MatrixNorm S j γ M F) (hH : MatrixNorm S j γ N H)
    (smF : ∀ r, ContDiffAt ℝ j (F r) 0) (smH : ∀ r, ContDiffAt ℝ j (H r) 0) :
    MatrixNorm S j γ (M+N) (fun r B => F r B+H r B) := by
  let K (A : Reserve S→Vec G c 1→Matrix (raw G f) (raw G f) ℝ) (r : Reserve S)
      (i b : raw G f) (q : Fin j→ raw G c) := iteratedFDeriv ℝ j (A r) 0 (ray G c∘q) i b
  have hJ (r : Reserve S) (i b : raw G f) (q : Fin j→ raw G c) :
      K (fun r B => F r B+H r B) r i b q = K F r i b q+K H r i b q := by
    have z := TestD.jet_add (ray G c) (List.ofFn q) (by simpa using smF r) (by simpa using smH r)
    rw [Stars.list_result (ray G c) q _ 0,Stars.list_result (ray G c) q _ 0,Stars.list_result (ray G c) q _ 0] at z
    exact congrArg (fun A => A i b) z
  constructor
  · intro r o v hv
    change ConditionalPhysicalSpan.Rooted _ _ _ _ _ _ _ _ (K (fun r B => F r B+H r B) r)
    rw [show K (fun r B => F r B+H r B) r = fun i b q => K F r i b q+K H r i b q from
      funext fun i => funext fun b => funext (hJ r i b)]
    exact (hF.1 r o v hv).add (hH.1 r o v hv)
  intro r s o h
  change ConditionalPhysicalSpan.Rooted _ _ _ _ _ _ _ _
    (fun i b q => K (fun r B => F r B+H r B) s i b q-K (fun r B => F r B+H r B) r i b q)
  rw [show (fun i b q => K (fun r B => F r B+H r B) s i b q-K (fun r B => F r B+H r B) r i b q) =
      fun i b q => (K F s i b q-K F r i b q)+(K H s i b q-K H r i b q) by
    funext i b q; rw [hJ,hJ]; ring]
  exact (hF.2 r s o h).add (hH.2 r s o h)

private theorem endpoint_rate {E τ ι X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]
    {v : τ→E} {D : Cost X} {a : ι→X} {p : τ→X} {d μ γ M N : ℝ} {o : X} {l : List τ}
    {U J : E→Matrix ι ι ℝ} (h : Here v D a p d γ o l M U J) (hγ : μ≤γ) (hm : M≤N) :
    Here v D a p d μ o l N U J := by
  constructor
  intro i j
  have cover (y z : X) {t : ℝ} (ht : 0≤t) :
      D.weight d y o*(positions D p d).pay l y*(D.weight μ y z*t) ≤
      D.weight d y o*(positions D p d).pay l y*(D.weight γ y z*t) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (D.weight_mono hγ _ _) ht)
      (mul_nonneg (D.weight_nn ..) ((positions D p d).pay_pos ..).le)
  exact ⟨(cover _ _ (abs_nonneg _)).trans ((h.test i j).1.trans hm),
    (cover _ _ (abs_nonneg _)).trans ((h.test i j).2.trans hm)⟩

/-- Ordinary and one-physical-tag arrays of the actual full stationary Gram
inverse by itself, including its true change of active coordinate space. -/
theorem inverse_positions (he : Bid.Larger (G:=G) S) (hs : 0<σ) (ha : 0≤A) (hT : T.up.Bounds T.high σ A Λ)
    (n j : ℕ) (hj : j<n) :
    let γ := together G S.patch S.kernel T.high n A σ/4
    let M := crowd j (|earnings G S.patch S.kernel T.high n A σ|+1) (totalFoot G S.patch S.kernel T.high n A σ)
    MatrixNorm S j γ M (fun r => PhysicalAffineScalarGaussianWeights.covariance T k (allot r) all) := by
  intro γ M
  let d := width G S.patch S.kernel T.high n A σ
  let N := |earnings G S.patch S.kernel T.high n A σ|+1
  let K (r : Reserve S) := PhysicalAffineScalarTreeCovariance.observed (allot r) k T.high T.up all
  have hW := path_sheet T hT
  have hd : 0<d := (gauged G S.patch S.kernel T.high n hs ha).pos
  have hr : d≤4*(n+1:ℕ)*d := by
    apply le_mul_of_one_le_left hd.le
    push_cast
    linarith [Nat.cast_nonneg (α:=ℝ) n]
  have hN : 0≤N := add_nonneg (abs_nonneg _) zero_le_one
  have one (r s : Reserve S) (z : Site c) (hz : ∀ o, o≠z → r o=s o) (l : List (raw G c)) (hl : l.length<n) :
      Here v₀ (native c) (home S) hearth d d z l N (K r) (K s) := by
    by_cases hl₀ : l=[]
    · subst l
      exact endpoint_rate (PhysicalAffineScalarTreeCovariance.flat (n:=n) (t:=k) (p:=T.high) hs ha hW he
        (change_draw r s z hz) all (by omega)) hr (add_le_add (le_abs_self _) (le_refl (1:ℝ)))
    exact endpoint_rate (PhysicalAffineScalarTreeCovariance.positive (n:=n) (t:=k) (p:=T.high) hs ha hW he
      (change_draw r s z hz) all l hl₀ hl) hr ((le_abs_self _).trans (le_add_of_nonneg_right zero_le_one))
  have pay := ConditionalTreeCovarianceSums.summed (S:=S) (p:=T.high) hj hs ha hN K
    (fun r _ => ⟨(PhysicalAffineScalarTreeCovariance.ordinary (n:=n) (t:=k) (p:=T.high) hs ha hW he (allot r) all).smooth,
      fun l hl => ((PhysicalAffineScalarTreeCovariance.ordinary (n:=n) (t:=k) (p:=T.high) hs ha hW he (allot r) all).bound l hl).mono hr
        (add_le_add (le_abs_self _) (le_refl (1:ℝ)))⟩) one
  have hδ : 0<together G S.patch S.kernel T.high n A σ := div_pos hd (by positivity)
  have hγ : 0≤γ := div_nonneg hδ.le (by norm_num)
  have hE (r : Reserve S) (q : Fin j→ raw G c) : iteratedFDeriv ℝ j (PhysicalAffineScalarGaussianWeights.covariance T k (allot r) all) 0 (ray G c∘q) =
      iteratedFDeriv ℝ j (K r) 0 (ray G c∘q) := by
    have H := TestD.identical (ray G c) (uncut (T:=T) (k:=k) (allot r) hs ha he hT) (List.ofFn q)
    rwa [Stars.list_result (ray G c) q _ 0,Stars.list_result (ray G c) q _ 0] at H
  constructor
  · intro r o v hv
    have hh := ConditionalPhysicalSpan.original hγ (ConditionalCovarianceLayers.nearest_neighbor hδ.le (pay.1 r o v hv))
    constructor
    simp_rw [hE]; exact hh.limit
  intro r s o hc
  have hh := ConditionalPhysicalSpan.original hγ (ConditionalCovarianceLayers.nearest_neighbor hδ.le (pay.2 r s o hc))
  constructor
  simp_rw [hE]; exact hh.limit

/-- Fixed true original chart and every one-site physical alternative. -/
def Positions {c f : Side} (S : StepData c f) (T : Tube G S) (n : ℕ) (x γ C : ℝ) :=
  ∀ (k : S.Choices) (r s : Site c→Reserve S) (_hc : ∀ z w, w≠z → r z w=s z w) (o : Site c),
    (∀ j : ℕ, j≤n → ConditionalPhysicalSpan.Rooted j (home S) id hearth o (visitors S o) γ C
      (fun i z l => iteratedFDeriv ℝ j
        (column (fun B => fullCenter T x k (allot (s z)) B-fullCenter T x k (allot (r z)) B))
        0 (ray G c∘l) i ())) ∧
    (∀ j : ℕ, j+1≤n → ConditionalPhysicalSpan.Rooted j (home S) hearth hearth o (ConditionalAffineRegularMean.visit S o) γ C
      (fun i a l => iteratedFDeriv ℝ (j+1) (column (fullCenter T x k (allot (r o)))) 0 (ray G c∘Fin.cons a l) i ())) ∧
    fullCenter T x k (allot (r o)) 0=0

/-- All stage prices and the necessary smallest side are fixed before the actual
period, cutoff temperature, original chosen tree or independent field directions. -/
theorem purchased (G : Gauge) (P : Patch) (Pt : Teller G) (hp : P.Branches Pt.bind G) (n : ℕ) :
    ∃ (γ C : ℝ) (R₀ : ℕ), 0<γ ∧ 0<C ∧
      ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch=P → Pt.Funds S T →
        100*(1+R₀)≤c.val → ∀ x, Positions S T n x γ C := by
  obtain ⟨u,D,R,hu,hD,H⟩ := whole_ordinary G P Pt hp n
  let w := width G P Pt.bind Pt.top.clip (n+1) Pt.top.paths Pt.top.width
  have hw : 0<w := (gauged G P Pt.bind Pt.top.clip (n+1) Pt.top.width_pos Pt.top.paths_pos.le).pos
  let δ := min u (w/(n+1:ℕ))
  have hδ : 0<δ := lt_min hu (div_pos hw (by positivity))
  have hr : ((n+1:ℕ):ℝ)*δ≤w := by
    rw [mul_comm]; exact (le_div_iff₀ (by positivity)).mp (min_le_right ..)
  let μ := δ/(2*((n+3:ℕ):ℝ))
  have hμ : 0<μ := div_pos hδ (by positivity)
  let V := torusPay (Co P.L (PAC G 1)) δ
  let A := census G P.L μ
  let Q := max 1 A
  let N := |earnings G P Pt.bind Pt.top.clip (n+1) Pt.top.paths Pt.top.width|+1
  let C := Q*Q*Q^n*((2:ℝ)^n*((D*N)*(1+V)))
  have hV : 0≤V := torusPay_nn _ _ hδ
  have hA : 0≤A := (torusPay_nn (Co P.L (PAC G 1)) μ hμ).trans (le_max_left ..)
  have hQ : 1≤Q := le_max_left ..
  have hN : 0<N := add_pos_of_nonneg_of_pos (abs_nonneg _) zero_lt_one
  have hC : 0<C := by dsimp only [C]; positivity
  let R₀ := max R (macroR P)
  refine ⟨μ/4,C,R₀,div_pos hμ (by norm_num),hC,?_⟩
  intro c f S T hS hT hsize x k r s hc o
  have hR : 100*(1+R)≤c.val := le_trans (by dsimp only [R₀]; gcongr; exact le_max_left ..) hsize
  have hm : 100*macroR P≤c.val := by have H : macroR P≤R₀ := le_max_right ..; omega
  have he : Bid.Larger (G:=G) S := ⟨hT.knobs.symm ▸ hT.kernel,by
    rw [hS,S.ratio.exact_size]; exact hm.trans (Nat.le_mul_of_pos_right _ S.ratio.count.property),by omega⟩
  obtain ⟨b,_,hW,_⟩ := hT.feeds
  have hB : T.up.Bounds T.high Pt.top.width Pt.top.paths b := by rw [hT.high]; exact hW
  have hrate : ((n+1:ℕ):ℝ)*δ≤width G S.patch S.kernel T.high (n+1) Pt.top.paths Pt.top.width := by
    rw [hS,hT.knobs,hT.high]; exact hr
  have hf := ((H S T hS hT hR (allot (r o)) k).2).weaken (min_le_left u (w/(n+1:ℕ))) (le_refl D)
  have hpos : 0≤torusPay (Co S.patch.L (PAC G 1)) δ := torusPay_nn _ _ hδ
  have hN' : 0≤|earnings G S.patch S.kernel T.high (n+1) Pt.top.paths Pt.top.width|+1 := by positivity
  refine ⟨?_,?_,flat T x k (allot (r o)) he.1 hB⟩
  · intro j hj
    have Htag := retain_tags hδ (mul_nonneg (mul_nonneg hN' hD.le) hpos)
      (fun z B => fullCenter T x k (allot (s z)) B-fullCenter T x k (allot (r z)) B)
      (fun z => tagged T x k (r z) (s z) z (hc z) he Pt.top.width_pos Pt.top.paths_pos.le hB n hδ hD.le hrate hf) j hj o
    apply ConditionalPhysicalSpan.original (by positivity : 0≤μ/4)
    refine ⟨Htag.limit.trans ?_⟩
    rw [hS,hT.knobs,hT.high]
    change A*A*A^j*((2:ℝ)^j*(N*D*V)) ≤ Q*Q*Q^n*((2:ℝ)^n*((D*N)*(1+V)))
    rw [mul_comm N D]
    have hpower : A^j ≤ Q^n := (pow_le_pow_left₀ hA (le_max_right 1 A) j).trans
      (pow_le_pow_right₀ hQ hj)
    gcongr <;> first | exact le_max_right .. | exact hj | exact hpower | linarith
  · intro j hj
    have Hpaid := ordinary T x k (allot (r o)) he Pt.top.width_pos Pt.top.paths_pos.le hB n hδ hD.le hrate hf
    have Hg := ConditionalAffineRegularMean.positions hδ (mul_nonneg (by positivity) (mul_nonneg hD.le hN')) Hpaid j hj o
    apply ConditionalPhysicalSpan.original (by positivity : 0≤μ/4)
    refine ⟨Hg.limit.trans ?_⟩
    rw [hS,hT.knobs,hT.high]
    let Z := max (torusPay (Co P.L (PAC G 1)) μ) (torusPay (PAC G 1) μ)
    have hz : Z≤A := max_le (le_max_left ..) ((le_max_right ..).trans (le_max_right ..))
    change Z*Z*Z^j*((2:ℝ)^n*(D*N)) ≤ Q*Q*Q^n*((2:ℝ)^n*((D*N)*(1+V)))
    have hzq : Z≤Q := hz.trans (le_max_right ..)
    have hp : Z^j≤Q^n := (pow_le_pow_left₀ ((torusPay_nn (Co P.L (PAC G 1)) μ hμ).trans (le_max_left ..)) hzq j).trans
      (pow_le_pow_right₀ hQ (by omega))
    have hz₀ : 0 ≤ Z := (torusPay_nn (Co P.L (PAC G 1)) μ hμ).trans (le_max_left ..)
    have hq₀ : 0 ≤ Q := hz₀.trans hzq
    have leading : Z*Z*Z^j ≤ Q*Q*Q^n :=
      mul_le_mul (mul_le_mul hzq hzq hz₀ hq₀) hp (pow_nonneg hz₀ j) (mul_nonneg hq₀ hq₀)
    have fee : D*N ≤ D*N*(1+V) :=
      le_mul_of_one_le_right (mul_nonneg hD.le hN.le) (le_add_of_nonneg_right hV)
    exact mul_le_mul leading (mul_le_mul_of_nonneg_left fee (by positivity))
      (by positivity) (by positivity)

end YM.Integration.ConditionalAffineIdealMean
