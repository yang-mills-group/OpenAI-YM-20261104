import YM.Integration.ConditionalAffineLoadPrices
import YM.Integration.PhysicalAffineScalarTreeCovariance

/-! All mixed field entries and one retained physical tree site for the actual affine mean discrepancy. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ConditionalAffineMeanPrice
open Function Filter Set Lattice Wilson RG Precision Tree Matrix Bloch Push.SectorMeasure
open FreeResolvent FreeResolvent.Affine FreeResolvent.TestD FreeResolvent.Lever FreeResolvent.Mark
open Pressure Pressure.Tube Pressure.Stores AnalyticBridge.GaussianFieldAlignment
open Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Gaussian Next.Fluctuations.Sector
open PhysicalNext.Repeat.Greenbelt ConditionalTreeCovarianceJets ConditionalTreeCovarianceSums
open ConditionalCovarianceCutoff
open PhysicalAffineScalarAperture (noHole)
open ConditionalAffineMeanDifference (error shortLoad wholeLoad)
open ConditionalAffineLoadPrices (Paid column)
open scoped BigOperators Classical ContDiff Topology Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f} {σ A Λ : ℝ} {n : ℕ}
variable {T : Tube G S} {k : S.Choices} {x : ℝ}
local notation "E" => Vec G c 1
local notation "v₀" => ray G c
local notation "q₀" => shorter (till x)

theorem uncut (F : Forest S.ratio) (hs : 0<σ) (ha : 0≤A) (he : Bid.Larger (G:=G) S)
    (hT : T.up.Bounds T.high σ A Λ) :
    PhysicalAffineScalarGaussianWeights.covariance T k F all =ᶠ[𝓝 0]
      PhysicalAffineScalarTreeCovariance.observed F k T.high T.up all := by
  let η := headGap G S.patch S.kernel T.high
  have hη : 0<η := headGap_pos ..
  have H := knows F k hs ha (path_sheet T hT) he T.high 0 all
  have hh := AnalyticBridge.RelativeLogdet.Differential.holds H.smooth.continuousAt H.gap (η/2)
    (by dsimp [η]; linarith) (native c) (theta S.ratio F)
  filter_upwards [hh] with B hB
  exact PhysicalAffineScalarGaussianWeights.spectral T k F all B (hB.unit_det (half_pos hη))

private theorem more {V₀ τ ι X : Type*} [NormedAddCommGroup V₀] [NormedSpace ℝ V₀] [Fintype ι]
    {v : τ→V₀} {D : Cost X} {a : ι→X} {p : τ→X} {δ γ M N : ℝ} {o : X} {l : List τ}
    {U J : V₀→Matrix ι ι ℝ} (h : Here v D a p δ γ o l M U J) (hm : M≤N) :
    Here v D a p δ γ o l N U J :=
  ⟨fun i j => ⟨(h.test i j).1.trans hm,(h.test i j).2.trans hm⟩⟩

theorem ideal (r s : Reserve S) (tag : Site c) (hc : ∀ w, w≠tag → r w=s w)
    (he : Bid.Larger (G:=G) S) (hs : 0<σ) (ha : 0≤A) (hT : T.up.Bounds T.high σ A Λ)
    (n : ℕ) {δ C : ℝ} (hδ : 0<δ) (hC : 0≤C)
    (hr : ((n+1:ℕ):ℝ)*δ≤width G S.patch S.kernel T.high (n+1) A σ)
    {f₀ : E→ raw G f→ℝ} (hF : Paid (home S) δ C n f₀) :
    let K u := PhysicalAffineScalarTreeCovariance.observed (allot u) k T.high T.up all
    let N := |earnings G S.patch S.kernel T.high (n+1) A σ|+1
    ∀ (l : List (raw G c)), l.length≤n → ∀ i, (native c).weight δ (home S i) tag*(marks G c δ).pay l (home S i)*
      |jet v₀ (fun B => (K s B-K r B)*column f₀ B) l 0 i ()| ≤
      2^l.length*(N*C*torusPay (Co S.patch.L (PAC G 1)) δ) := by
  intro K N l hl i
  let d := width G S.patch S.kernel T.high (n+1) A σ
  have hW := path_sheet T hT
  have hd : 0<d := (gauged G S.patch S.kernel T.high (n+1) hs ha).pos
  have hle : δ≤d := by
    have hn : (1:ℝ)≤(n+1:ℕ) := by exact_mod_cast (show 1≤n+1 by omega)
    nlinarith only [mul_le_mul_of_nonneg_right hn hδ.le,hr]
  have hroom : ((n+1:ℕ):ℝ)*δ ≤ 4*((n+1+1:ℕ):ℝ)*d := by
    apply hr.trans
    have h₁ : (1:ℝ)≤4*((n+1+1:ℕ):ℝ) := by push_cast;linarith only [Nat.cast_nonneg (α:=ℝ) n]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right h₁ hd.le
  have smooth (u : Reserve S) : ContDiffAt ℝ n (K u) 0 :=
    (PhysicalAffineScalarTreeCovariance.smooth (n:=n) (t:=k) (p:=T.high) hs ha hW he (allot u) all).sub contDiffAt_const
  apply ConditionalAffineRootContraction.apply_column hδ.le hle hroom (show 0≤N by dsimp [N]; positivity) hC
    (home_volume (G:=G) S 1 _ hδ) (smooth r) (smooth s) hF.smooth _ hF.rows l hl i
  intro u hu
  by_cases hz : u=[]
  · subst u
    apply more (PhysicalAffineScalarTreeCovariance.flat (n:=n+1) (t:=k) (p:=T.high) hs ha hW he
      (change_draw r s tag hc) all (by omega))
    dsimp only [N];linarith only [le_abs_self (earnings G S.patch S.kernel T.high (n+1) A σ)]
  · apply more (PhysicalAffineScalarTreeCovariance.positive (n:=n+1) (t:=k) (p:=T.high) hs ha hW he
      (change_draw r s tag hc) all u hz (by omega))
    exact (le_abs_self _).trans (le_add_of_nonneg_right zero_le_one)

theorem minus {A : E→Matrix (raw G f) Unit ℝ} (l : List (raw G c)) :
    jet v₀ (fun B => -A B) l 0 = -jet v₀ A l 0 :=
  DFunLike.congr_fun (iteratedFDeriv_neg_apply (𝕜:=ℝ) (f:=A) (i:=l.length) (x:=0)) (v₀ ∘ l.get)

/-- A price for the actual conditional mean, with its independent directions and
its changed physical tree co-root. Both loads are literal vectors from the true curved rows. -/
theorem measured (r s : Reserve S) (tag : Site c) (hc : ∀ w, w≠tag → r w=s w)
    (q : Chi) (ε : ℝ) (Y : LinkArray G (Frozen (noHole S) x (allot r))) (Z : LinkArray G (Frozen (noHole S) x (allot s)))
    (he : Bid.Larger (G:=G) S) (hs : 0<σ) (ha : 0≤A) (hT : T.up.Bounds T.high σ A Λ)
    (hx : 120≤radiusB x) (n : ℕ) {δ C D : ℝ} (hδ : 0<δ) (hC : 0≤C) (hD : 0≤D)
    (hr : ((n+1:ℕ):ℝ)*δ≤width G S.patch S.kernel T.high (n+1) A σ)
    (hF : Paid (home S) δ C n (shortLoad T x k))
    (hDtrue : Paid (home S) δ D n (fun B => shortLoad T x k B-wholeLoad T k B)) :
    let M := windowPrice G S.patch S.kernel T.high (n+1) A σ 0 (radiusB x/60:ℕ) +
      diminish G S.patch S.kernel T.high (n+1) (till x) A σ 0
    let N := |earnings G S.patch S.kernel T.high (n+1) A σ|+1
    let V := torusPay (Co S.patch.L (PAC G 1)) δ
    ∀ (l : List (raw G c)), l.length≤n → ∀ i, (native c).weight δ (home S i) tag*(marks G c δ).pay l (home S i)*
      |jet v₀ (column (fun B => error T x k s q ε Z B-error T x k r q ε Y B)) l 0 i ()| ≤
      2^l.length*(M*C*V+N*D*V) := by
  intro M N V l hl i
  let P u := ConditionalAffinePanelWindow.columns .adjoint x hx (till x) u k T.high T.up 0
  let K u := PhysicalAffineScalarTreeCovariance.observed (allot u) k T.high T.up all
  let X := fun B => (P s B-P r B)*column (shortLoad T x k) B
  let U := fun B => (K s B-K r B)*column (fun y => shortLoad T x k y-wholeLoad T k y) B
  have hW := path_sheet T hT
  have psm (u : Reserve S) := (ConditionalAffinePanelWindow.regular (t:=k) (p:=T.high) (n:=n) hs ha hW he (le_refl 0)
    x hx (till x) u .adjoint).smooth
  have ksm (u : Reserve S) : ContDiffAt ℝ n (K u) 0 :=
    (PhysicalAffineScalarTreeCovariance.smooth (n:=n) (t:=k) (p:=T.high) hs ha hW he (allot u) all).sub contDiffAt_const
  have smX : ContDiffAt ℝ n X 0 := prod_smooth ((psm s).sub (psm r)) hF.smooth
  have smU : ContDiffAt ℝ n U 0 := prod_smooth ((ksm s).sub (ksm r)) hDtrue.smooth
  have eq : column (fun B => error T x k s q ε Z B-error T x k r q ε Y B) =ᶠ[𝓝 0] fun B => -X B-U B := by
    filter_upwards [ConditionalAffineMeanDifference.one_tag T x k r s hx q ε Y Z he.1 he hs ha hT,
      uncut (allot r) hs ha he hT,uncut (allot s) hs ha he hT] with B h hR hS
    ext i j; cases j
    change (error T x k s q ε Z B-error T x k r q ε Y B) i = _
    rw [h,hR,hS]; rfl
  let t := (native c).weight δ (home S i) tag*(marks G c δ).pay l (home S i)
  have ht : 0≤t := mul_nonneg ((native c).weight_nn ..) ((marks G c δ).pay_pos ..).le
  have hx := ConditionalAffineRootContraction.panel (t:=k) hs ha hW he x hx r s tag hc n δ C hδ hC hr
    (column (shortLoad T x k)) hF.smooth hF.rows l hl i
  have hu := ideal (T:=T) (k:=k) r s tag hc he hs ha hT n hδ hD hr hDtrue l hl i
  rw [TestD.identical v₀ eq l,jet_sub v₀ l (smooth_of_le smX.neg hl) (smooth_of_le smU hl),
    minus (A:=X) l,Matrix.sub_apply,Matrix.neg_apply]
  change t*|-jet v₀ X l 0 i ()-jet v₀ U l 0 i ()|≤_
  calc
    _ ≤ t*(|jet v₀ X l 0 i ()|+|jet v₀ U l 0 i ()|) := by
      apply mul_le_mul_of_nonneg_left _ ht
      simpa only [sub_zero,zero_sub,abs_neg] using abs_sub_le (-jet v₀ X l 0 i ()) 0 (jet v₀ U l 0 i ())
    _ ≤ _ := by rw [mul_add]; exact (add_le_add hx hu).trans_eq (mul_add ..).symm

open FreeResolvent.Stars

def visitors {j : ℕ} (S : StepData c f) (y : Site c) (i : raw G f) (tag : Site c) (l : Fin j→ raw G c) : Bool :=
  decide (y=home S i ∨ y=tag ∨ ∃ m, y=hearth (l m))

def census (G : Gauge) (L : Side) (δ : ℝ) :=
  max (torusPay (Co L (PAC G 1)) δ) (max (torusPay Unit δ) (torusPay (PAC G 1) δ))

/-- Sum every genuine tag choice along with all the free and external coordinates,
retaining whichever one of those physical positions is prescribed. -/
theorem retain_tags {n : ℕ} {δ C : ℝ} (hδ : 0<δ) (hC : 0≤C) (F : Site c→E→ raw G f→ℝ)
    (H : ∀ z (l : List (raw G c)), l.length≤n → ∀ i,
      (native c).weight δ (home S i) z*(marks G c δ).pay l (home S i)*|jet v₀ (column (F z)) l 0 i ()|≤
        (2:ℝ)^l.length*C) (j : ℕ) (hj : j≤n) (o : Site c) :
    let μ := δ/(2*((n+3:ℕ):ℝ))
    let K (i : raw G f) (z : Site c) (l : Fin j→ raw G c) := iteratedFDeriv ℝ j (column (F z)) 0 (ray G c∘l) i ()
    NearStar j (taxi c) (home S) id hearth o (visitors (G:=G) (j:=j) S o) (μ/4) (crowd j ((2:ℝ)^j*C) (census G S.patch.L μ)) K := by
  intro μ K
  have hμ : 0<μ := div_pos hδ (by positivity)
  let A₁ := census G S.patch.L μ
  have hA : 0≤A₁ := (torusPay_nn (Co S.patch.L (PAC G 1)) μ hμ).trans (le_max_left ..)
  have hu : 2*(j+3:ℕ)*μ≤δ := by
    have hpos : 0<(2*((n+3:ℕ):ℝ)) := by positivity
    rw [show δ=(2*((n+3:ℕ):ℝ))*μ by dsimp only [μ]; field_simp]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast (show 2*(j+3)≤2*(n+3) by omega)) hμ.le
  apply ConditionalCovarianceLayers.nearest_neighbor hμ.le
  apply sums_no_mark hμ.le (by positivity) hu hA _ _
    ((home_volume (G:=G) S 1 μ hμ).le (le_max_left ..)) _
    ((volume c (PAC G 1) μ hμ).le ((le_max_right ..).trans (le_max_right ..)))
  · intro i z l
    have hh := H z (List.ofFn l) (by simpa using hj) i
    rw [Stars.pays (native c) _ _ (hearth (G:=G) (r:=1)) l,Stars.list_result v₀ l _ 0] at hh
    simp only [Stars.costs,Cost.self,zero_add,Cost.weight,id,List.length_ofFn,mul_add,
      Real.exp_add,mul_assoc,K] at hh ⊢
    exact hh
  · intro i z l h
    simpa only [visitors,decide_eq_true_eq,id,hearth] using h
  · let e (z : Site c) : Site c×Unit := (z,())
    have hi : Function.Injective e := fun a b h => congrArg Prod.fst h
    exact ((volume c Unit μ hμ).comp hi).le ((le_max_left ..).trans (le_max_right ..))

/-- Sum the actual varied-site position, independent external field addresses and fine output,
retaining any single physical hit. The two legitimate forest draws may depend on the varied site. -/
theorem positions (r s : Site c→Reserve S) (hc : ∀ z w, w≠z → r z w=s z w)
    (q : Chi) (ε : ℝ) (Y : ∀ z, LinkArray G (Frozen (noHole S) x (allot (r z))))
    (Z : ∀ z, LinkArray G (Frozen (noHole S) x (allot (s z))))
    (he : Bid.Larger (G:=G) S) (hs : 0<σ) (ha : 0≤A) (hT : T.up.Bounds T.high σ A Λ)
    (hx : 120≤radiusB x) (n : ℕ) {δ C D : ℝ} (hδ : 0<δ) (hC : 0≤C) (hD : 0≤D)
    (hr : ((n+1:ℕ):ℝ)*δ≤width G S.patch S.kernel T.high (n+1) A σ)
    (hF : Paid (home S) δ C n (shortLoad T x k))
    (hDtrue : Paid (home S) δ D n (fun B => shortLoad T x k B-wholeLoad T k B))
    (j : ℕ) (hj : j≤n) (y : Site c) :
    let μ := δ/(2*((n+3:ℕ):ℝ))
    let M := windowPrice G S.patch S.kernel T.high (n+1) A σ 0 (radiusB x/60:ℕ) +
      diminish G S.patch S.kernel T.high (n+1) (till x) A σ 0
    let N := |earnings G S.patch S.kernel T.high (n+1) A σ|+1
    let V := torusPay (Co S.patch.L (PAC G 1)) δ
    let K (i : raw G f) (z : Site c) (l : Fin j→ raw G c) :=
      iteratedFDeriv ℝ j (column (fun B => error T x k (s z) q ε (Z z) B-error T x k (r z) q ε (Y z) B))
        0 (v₀ ∘ l) i ()
    NearStar j (taxi c) (home S) id hearth y (visitors (G:=G) (j:=j) S y) (μ/4)
      (crowd j (2^j*(M*C*V+N*D*V)) (census G S.patch.L μ)) K := by
  intro μ M N V K
  have hM : 0≤M := add_nonneg (window_price_nonneg hs ha (le_refl 0)) (cut_nonneg hs ha (le_refl 0) (till x))
  have hV : 0≤V := torusPay_nn _ _ hδ
  have hN : 0≤N := add_nonneg (abs_nonneg _) zero_le_one
  refine retain_tags hδ (add_nonneg (mul_nonneg (mul_nonneg hM hC) hV) (mul_nonneg (mul_nonneg hN hD) hV))
    (fun z B => error T x k (s z) q ε (Z z) B-error T x k (r z) q ε (Y z) B) ?_ j hj y
  intro z
  exact measured (T:=T) (k:=k) (r z) (s z) z (hc z) q ε (Y z) (Z z) he hs ha hT hx n hδ hC hD hr hF hDtrue

end YM.Integration.ConditionalAffineMeanPrice
