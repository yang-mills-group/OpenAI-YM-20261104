import YM.Integration.WilsonRootedKioskOccupiedSlip
import YM.QuadraticLocal.Class.Spill
import YM.QuadraticLocal.Shelter.Animal

/-! Every deposited analytic slot, including those off its angular mask, at its original root. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCoherentMayerPublishedGross
open Function Finset Lattice Wilson RG Marker Ac Push QuadraticLocal QuadraticLocal.Earn
open Push.AbsoluteSums QuadraticLocal.Sunrise QuadraticLocal.Poetry
open scoped Classical BigOperators

variable {G:Gauge} {n c:Side} {V α ι:Type} [DecidableEq V]
  {P:Passport n V} {R:Census V} (X:ι→Row P R G α) (w:V→ℝ) (t:V→ℕ)
  {σ b g a U ξ:ℝ} {j k l:ℕ} (B:BudgetPoint)
local notation "fields" => (j+l+1)
local notation "gross" => ((Spill.allOver B)^fields)
local notation "income" => (Invoice.price B U fields k a ξ G)

theorem landed (L:Scene.Armada X w t σ b j k l)
    (funded:Invoice.Supports B U a g σ ξ):
    WilsonRootedKioskOccupiedSlip.Gross (rendered X B g) w B.B a (gross*(income*b)):=by
  let f i:=gross*(X i).charge B g
  have h:0≤gross:=pow_nonneg (zero_le_one.trans (Spill.allOver_ge B)) _
  have positive (i:ι):0≤f i:=mul_nonneg h
    (mul_nonneg (mul_nonneg (by positivity) ((X i).real_quote B g).1) (X i).sound.le)
  refine ⟨f,positive,?_,?_⟩
  · intro i v W
    exact Spill.nominal_price B g _ v (X i) (L.honor i)
      (Scene.Armada.degreeR _ L.toMinistry (X i) (L.purchases.usable i)).2.2 W
  · change Hit (fun i=>(X i).ground B) B.B (fun i=>Poly.toll w (X i).mode*f i) a _
    intro x
    convert budget_scale h (Scene.Armada.hits X w t L B funded x) using 1
    ext i
    by_cases hi:x∈(X i).ground B
    · simp only [hi,if_true,Invoice.income,f]
      ring
    · simp only [hi,if_false,mul_zero]

variable (q:Ratio c n) (S:Press X j) {z d τ:ℝ} (book:Press.Receipt X S z d)
  (pad:ℝ)

/-- The landed certificate for the complete rendered `Width.treasured` family. -/
theorem original (L:Scene.Armada X w t σ b j k l)(dpos:0≤d)(small:b≤1)
    (wages:Width.Memento k q.count σ pad z)
    (safe:Invoice.Supports B U a g pad ξ):
    WilsonRootedKioskOccupiedSlip.Gross (Width.treasured X q S book B pad g) w B.B a
      (gross*(income*(Scene.productivity q.count z pad d k j*b))):=by
  exact landed (Scene.letters X q S book pad) w t B
    (Scene.lit X q w t S book L dpos small wages) safe

end YM.Integration.WilsonCoherentMayerPublishedGross
