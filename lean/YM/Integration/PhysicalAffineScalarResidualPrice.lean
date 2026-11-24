import YM.Integration.PhysicalAffineScalarChangedFields
import YM.Integration.PhysicalAffineScalarResidualVectors

/-! Numeric transfer through the two actual Gaussian residual equations.
Every term in the marked root price retains its original cutoff factor. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.PhysicalAffineScalarResidualPrice
open Filter Function Set Matrix Lattice FreeResolvent FreeResolvent.Affine FreeResolvent.TestD FreeResolvent.Mark
open ConditionalAffineLoadPrices PhysicalAffineScalarRootContraction PhysicalAffineScalarChangedFields
open PhysicalAffineScalarResidualVectors
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {c : Side}
local notation "E" => Vec G c 1
local notation "ray₀" => ray G c
local notation "D₀" => native c

section Operators
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- An actual raw physical matrix acts on two different forest endpoints,
retaining the genuine common changed site. -/
def Acts (p : ι→Site c) (q : κ→Site c) (z : Site c) (δ fee : ℝ) (n : ℕ)
    (A B : E→Matrix κ ι ℝ) : Prop := ∀ {F U : E→ι→ℝ} {C : ℝ}, 0≤C →
    Pair p z δ C n F U → Pair q z δ (fee*C) n (fun b => A b*ᵥ F b) (fun b => B b*ᵥ U b)

namespace Acts
variable {p : ι→Site c} {q : κ→Site c} {z : Site c} {δ d γ M N V : ℝ} {n : ℕ}

theorem ordinary {J : E→Matrix κ ι ℝ} (hJ : Bundle ray₀ (marks G c δ) D₀ q p J 0 n γ M)
    (hM : 0≤M) (hδ : 0≤δ) (hγ : δ+n*δ≤γ) : Acts p q z δ (2^n*M) n J J := by
  intro F U C hC hF
  convert hF.action hC hJ hM hδ hγ using 1
  ring

theorem inverse {A B : E→Matrix ι ι ℝ} (hA : Bundle ray₀ (marks G c δ) D₀ p p A 0 n γ M)
    (hB : Bundle ray₀ (marks G c δ) D₀ p p B 0 n γ M)
    (hH : ∀ l : List (raw G c), l.length≤n → Lever.Here ray₀ D₀ p hearth d γ z l N A B)
    (hM : 0≤M) (hN : 0≤N) (hδ : 0≤δ) (hd : δ≤d) (hγ : δ+n*δ≤γ)
    (hV : (native c).Volume p δ V) (hv : 0≤V) : Acts p p z δ (2^n*(M+N*V)) n A B := by
  intro F U C hC hF
  convert hF.inverse hC hA hB hH hM hN hδ hd hγ hV hv using 1
  ring

theorem mono_fee {A B : E→Matrix κ ι ℝ} {K : ℝ} (h : Acts p q z δ M n A B) (hMK : M≤K) :
    Acts p q z δ K n A B := fun hC hF => (h hC hF).mono_fee (mul_le_mul_of_nonneg_right hMK hC)
end Acts
end Operators

/-- Numerical costs before the cutoff exponential or Gaussian normalization. -/
def centerFee (J C f : ℝ) := C*(J*f)
def residualFee (J C f : ℝ) := f+J*centerFee J C f
def forcingFee (J C T u e : ℝ) := e+T*centerFee J C u
def remainderFee (J C T u e : ℝ) :=
  forcingFee J C T u e +J*(C*(J*forcingFee J C T u e+T*residualFee J C u))
def price (n : ℕ) (J C T v u e : ℝ) :=
  let s := residualFee J C v+residualFee J C u
  let t := remainderFee J C T u e
  2^n*(t*s)+2^n*(s*t)

section Residual
variable {ι κ : Type} [Fintype ι] [Fintype κ]
variable {p : ι→Site c} {q : κ→Site c} {z : Site c} {δ j h t v₀ u₀ e₀ ε : ℝ} {n : ℕ}
    {J L D : FreeResolvent.Vec G c 1 → Matrix ι κ ℝ} {C C' H H' : FreeResolvent.Vec G c 1 → Matrix κ κ ℝ} {v u e : FreeResolvent.Vec G c 1 → ι→ℝ}
    (hJ : Acts q p z δ j n J J) (hJt : Acts p q z δ j n (fun b => (J b).transpose) (fun b => (J b).transpose))
    (hL : Acts q p z δ j n L L) (hLt : Acts p q z δ j n (fun b => (L b).transpose) (fun b => (L b).transpose))
    (hD : Acts q p z δ (ε*t) n D D) (hDt : Acts p q z δ (ε*t) n (fun b => (D b).transpose) (fun b => (D b).transpose))
    (hC : Acts q q z δ h n C C') (hH : Acts q q z δ h n H H')
    (hS : Paid p δ v₀ n v) (hU : Paid p δ u₀ n u) (hE : Paid p δ (ε*e₀) n e)
    (hj : 0≤j) (hh : 0≤h) (ht : 0≤t) (hv : 0≤v₀) (hu : 0≤u₀) (he : 0≤e₀) (hε : 0≤ε)
include hJ hJt hL hLt hD hDt hC hH hS hU hE hj hh ht hv hu he hε

/-- Apply each purchased common or one-tree matrix only to its real load.
The resulting actual difference of physical rooted integrands has cost
`ε * price`. Here `ε` is the single original exponential cutoff, already
present in both removed genuine inputs. -/
theorem integrand : Paid p δ (ε*price n j h t v₀ u₀ e₀) n (fun b i =>
    small (J b) (L b) (D b) (C b) (H b) (u b) (e b) i *
      (residual (J b) (C b) (v b) i+residual (L b) (H b) (u b) i)) ∧
    Rooted p z δ (ε*price n j h t v₀ u₀ e₀) n (fun b i =>
    small (J b) (L b) (D b) (C' b) (H' b) (u b) (e b) i *
      (residual (J b) (C' b) (v b) i+residual (L b) (H' b) (u b) i) -
    small (J b) (L b) (D b) (C b) (H b) (u b) (e b) i *
      (residual (J b) (C b) (v b) i+residual (L b) (H b) (u b) i)) := by
  let T := forcingFee j h t u₀ e₀
  let A := residualFee j h v₀
  let B := residualFee j h u₀
  let Z := remainderFee j h t u₀ e₀
  have hUt := hLt hu (Pair.same (z:=z) hU hu)
  have hUm := hH (mul_nonneg hj hu) hUt
  have hVt := hJt hv (Pair.same (z:=z) hS hv)
  have hVm := hC (mul_nonneg hj hv) hVt
  have huM : Pair q z δ (centerFee j h u₀) n (fun b => loadCenter (L b) (H b) (u b))
      (fun b => loadCenter (L b) (H' b) (u b)) := hUm
  have huR : Pair p z δ B n (fun b => residual (L b) (H b) (u b)) (fun b => residual (L b) (H' b) (u b)) :=
    (Pair.same (z:=z) hU hu).diff (hL (mul_nonneg hh (mul_nonneg hj hu)) hUm)
  have hvR : Pair p z δ A n (fun b => residual (J b) (C b) (v b)) (fun b => residual (J b) (C' b) (v b)) :=
    (Pair.same (z:=z) hS hv).diff (hJ (mul_nonneg hh (mul_nonneg hj hv)) hVm)
  have hY : Pair p z δ (ε*T) n (fun b => forcing (L b) (D b) (H b) (u b) (e b))
      (fun b => forcing (L b) (D b) (H' b) (u b) (e b)) := by
    convert (Pair.same (z:=z) hE (mul_nonneg hε he)).diff (hD (by unfold centerFee; positivity) huM) using 1 <;>
      simp only [T,forcingFee,centerFee,forcing]
    all_goals ring
  have hT : 0≤T := by dsimp [T,forcingFee,centerFee]; positivity
  have hB : 0≤B := by dsimp [B,residualFee,centerFee]; positivity
  have hK := (hJt (mul_nonneg hε hT) hY).sum (hDt hB huR)
  have hK₀ : 0≤j*(ε*T)+(ε*t)*B := by positivity
  have hW := hC hK₀ hK
  have hDifference : Pair p z δ (ε*Z) n (fun b => small (J b) (L b) (D b) (C b) (H b) (u b) (e b))
      (fun b => small (J b) (L b) (D b) (C' b) (H' b) (u b) (e b)) := by
    convert hY.diff (hJ (mul_nonneg hh hK₀) hW) using 1 <;> simp only [small,Z,remainderFee,T,B]
    all_goals ring
  have hSum := hvR.sum huR
  have hA : 0≤A := by dsimp [A,residualFee,centerFee]; positivity
  have hZ : 0≤Z := by dsimp [Z,remainderFee,forcingFee,residualFee,centerFee]; positivity
  constructor
  · apply Paid.weaken (d:=δ) (Rooted.ordinary_product hDifference.left hSum.left (mul_nonneg hε hZ) (add_nonneg hA hB)) le_rfl
    change 2^n*((ε*Z)*(A+B))≤ε*(2^n*(Z*(A+B))+2^n*((A+B)*Z))
    nlinarith only [mul_nonneg (mul_nonneg hε (by positivity : (0:ℝ)≤2^n)) (mul_nonneg (add_nonneg hA hB) hZ)]
  · convert hDifference.changed_product hSum (mul_nonneg hε hZ) (add_nonneg hA hB) using 1 <;>
      simp only [price,Z,A,B,Pi.add_apply]
    all_goals ring

end Residual
end YM.Integration.PhysicalAffineScalarResidualPrice
