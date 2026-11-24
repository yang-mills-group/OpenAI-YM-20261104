import YM.Integration.ConditionalAffineLoadPrices
import YM.Integration.PhysicalAffineScalarWeightChange

/-! The fixed-forest flat-position estimate of the original physical mean. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ConditionalAffineRegularMean
open Function Filter Set Lattice Wilson RG Precision Tree Matrix Bloch Push.SectorMeasure
open Pressure Pressure.Tube Pressure.Stores FreeResolvent FreeResolvent.Affine FreeResolvent.TestD FreeResolvent.Stars
open PhysicalNext.Repeat.Greenbelt ConditionalTreeCovarianceJets ConditionalTreeCovarianceSums ConditionalCovarianceCutoff
open ConditionalAffineLoadPrices ConditionalAffineLoadPrices.Paid PhysicalAffineScalarAperture
open PhysicalAffineScalarGaussianWeights ConditionalAffineMeanDifference AnalyticBridge.GaussianFieldAlignment
open Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Gaussian Next.Fluctuations.Sector
open scoped BigOperators Classical ContDiff Topology Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f} (T : Tube G S) (k : S.Choices)
variable {x a b Λ δ C D : ℝ}

theorem flat (r : Reserve S) (q : Chi) (ε : ℝ)
    (Y : LinkArray G (Frozen (noHole S) x (allot r))) (he : Bid.Larger (G:=G) S)
    (hs : 0<b) (ha : 0≤a) (hW : T.up.Bounds T.high b a Λ) (hx : 120≤radiusB x) :
    error T x k r q ε Y 0 = 0 := by
  have hf := PhysicalAffineScalarUncut.offset_zero T k he.1
  have h₀ : PhysicalAffineScalarCutWeights.sourceTail T x (0:Vec G c 1) = 0 := by
    apply tape.injective
    funext i
    simp [PhysicalAffineScalarCutWeights.sourceTail,ConditionalAffineSourceSplit.flat T x,tape]
  have h := PhysicalAffineScalarRetainedSource.full_decomposition T x k (0:Vec G c 1)
  rw [hf,h₀,sub_zero] at h
  have short₀ : shortLoad T x k (0:Vec G c 1)=0 := by
    unfold shortLoad
    rw [←h,Matrix.mulVec_zero]
  have whole₀ : wholeLoad T k (0:Vec G c 1)=0 := by
    unfold wholeLoad
    rw [hf,Matrix.mulVec_zero]
  have eq := (ConditionalAffineMeanDifference.original T x k r hx q ε Y he.1 he hs ha hW).self_of_nhds
  simpa only [short₀,whole₀,sub_zero,Matrix.mulVec_zero,neg_zero] using eq

/-- The same native panel and full stationary inverse multiply their respective
honest ordinary and single-small source. Each external coarse-field address
retains its own mark in the output. -/
theorem charged (r : Reserve S) (q : Chi) (ε : ℝ)
    (Y : LinkArray G (Frozen (noHole S) x (allot r))) (he : Bid.Larger (G:=G) S)
    (hs : 0<b) (ha : 0≤a) (hW : T.up.Bounds T.high b a Λ) (hx : 120≤radiusB x)
    (n : ℕ) (hδ : 0<δ) (hC : 0≤C) (hD : 0≤D)
    (hw : ((n+1:ℕ):ℝ)*δ≤width G S.patch S.kernel T.high (n+1) a b)
    (hc : Paid (home S) δ C n (shortLoad T x k))
    (hd : Paid (home S) δ D n (fun B => shortLoad T x k B-wholeLoad T k B)) :
    let M := windowPrice G S.patch S.kernel T.high (n+1) a b 0 (radiusB x/60:ℕ) +
      diminish G S.patch S.kernel T.high (n+1) (till x) a b 0
    let N := |earnings G S.patch S.kernel T.high (n+1) a b|+1
    Paid (home S) δ ((2:ℝ)^n*(M*C+N*D)) n (error T x k r q ε Y) := by
  intro M N
  let d := width G S.patch S.kernel T.high (n+1) a b
  have hdn : δ≤d := by
    apply le_trans _ hw
    have h₁ : (1:ℝ)≤(n+1:ℕ) := by exact_mod_cast (show 1≤n+1 by omega)
    simpa only [one_mul] using mul_le_mul_of_nonneg_right h₁ hδ.le
  have hnd : (n:ℝ)*δ≤d := (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ n) hδ.le).trans hw
  have hp := ConditionalAffinePanelWindow.regular (n:=n+1) (t:=k) (p:=T.high)
    hs ha (path_sheet T hW) he (le_refl 0) x hx (till x) r .adjoint
  have hi := PhysicalAffineScalarWeightChange.covariance_ordinary T k (allot r) hs ha (path_sheet T hW) he all (n+1)
  have hother : (n:ℝ)*δ≤4*((n+1+1:ℕ):ℝ)*d := hnd.trans (by
    have dd := hδ.le.trans hdn
    have h₁ : (1:ℝ)≤4*((n+1+1:ℕ):ℝ) := by push_cast;linarith only [Nat.cast_nonneg (α:=ℝ) n]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right h₁ dd)
  have hM : 0≤M := add_nonneg (window_price_nonneg hs ha (le_refl 0)) (cut_nonneg hs ha (le_refl 0) (till x))
  have hN : 0≤N := add_nonneg (abs_nonneg _) zero_le_one
  have p₁ := hc.action hC (matrix_weaken hp hdn (Nat.le_succ n)) hM hδ.le hnd
  have wallet : earnings G S.patch S.kernel T.high (n+1) a b+1≤N := by
    dsimp only [N];linarith only [le_abs_self (earnings G S.patch S.kernel T.high (n+1) a b)]
  have p₂ := hd.action hD (matrix_cost (matrix_weaken hi hdn (Nat.le_succ n)) wallet) hN hδ.le hother
  have hp' : Paid (home S) δ ((2:ℝ)^n*(C*M)+(2:ℝ)^n*(D*N)) n _ := p₁.negative.diff p₂
  have heq := ConditionalAffineMeanDifference.original T x k r hx q ε Y he.1 he hs ha hW
  apply germ (he:=heq)
  convert hp' using 1
  ring

def visit (S : StepData c f) (o : Site c) {n : ℕ} (i : raw G f) (j : raw G c) (l : Fin n → raw G c) : Bool :=
  decide (o=home S i ∨ o=hearth j ∨ ∃ u, o=hearth (l u))

/-- At positive order the second endpoint is the first original field. There
is no freely added spectator site or volume. -/
theorem positions {F : Vec G c 1→ raw G f→ℝ}
    {n : ℕ} (hδ : 0<δ) (hC : 0≤C) (hF : Paid (home S) δ C n F)
    (j : ℕ) (hj : j+1≤n) (o : Site c) :
    let γ := δ/(2*((n+3:ℕ):ℝ))
    let V := max (torusPay (Co S.patch.L (PAC G 1)) γ) (torusPay (PAC G 1) γ)
    NearStar j (taxi c) (home S) hearth hearth o (visit S o) (γ/4) (crowd j C V)
      (fun i k l => iteratedFDeriv ℝ (j+1) (column F) 0 (ray G c ∘ Fin.cons k l) i ()) := by
  intro γ V
  have hγ : 0<γ := div_pos hδ (by positivity)
  have hH := (home_volume (G:=G) S 1 γ hγ).le (le_max_left _ (torusPay (PAC G 1) γ))
  have hC₁ := (volume c (PAC G 1) γ hγ).le (le_max_right (torusPay (Co S.patch.L (PAC G 1)) γ) _)
  have hV : 0≤V := (torusPay_nn (PAC G 1) γ hγ).trans (le_max_right ..)
  have hh : 2*(j+3:ℕ)*γ≤δ := by
    rw [show δ=(2*((n+3:ℕ):ℝ))*γ by dsimp only [γ]; field_simp]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast (show 2*(j+3)≤2*(n+3) by omega)) hγ.le
  apply ConditionalCovarianceLayers.nearest_neighbor hγ.le
  refine sums_no_mark hγ.le hC hh hV ?_ ?_ hH hC₁ hC₁
  · intro i k l
    let ss : Fin (j+1) → raw G c := Fin.cons (α:=fun _ => raw G c) k l
    have hz := hF.rows (List.ofFn ss) (by simpa using hj) i
    have eq : Stars.costs (native c) (home S i) (home S i) (hearth k) (hearth∘l) =
        Stars.rays (native c) (home S i) (hearth ∘ ss) := by
      unfold Stars.costs Stars.rays; rw [(native c).self,zero_add,Fin.sum_univ_succ]; rfl
    rw [Stars.pays (native c) _ _ (hearth (G:=G) (r:=1)) ss,Stars.list_result (ray G c) ss _ 0] at hz
    simpa only [eq,ss] using hz
  · intro i k l h
    simpa only [visit,decide_eq_true_eq] using h

end YM.Integration.ConditionalAffineRegularMean
