import YM.Integration.WilsonOriginalPointCompactFaces
import YM.Extra.MULTISOURCE_TRAJECTORIES.Algebra

/-! The unmasked three-color income factors on one configuration before any conditional average. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalThreeCompactProduct
open Function Finset Lattice Laurent RG Wilson Marker Gauge
open Push Push.AbsoluteSums Paths Animals ConnectedActivityE6 QuadraticLocal QuadraticLocal.Sunrise
open QuadraticLocal.Poetry QuadraticLocal.Earn QuadraticLocal.Mentor AllOrder AllOrder.Ink QuadraticLocal.Affinity
open WilsonOriginalPointCompactRoster WilsonOriginalPointCompactFaces
open scoped Classical BigOperators

variable {I:Type} [Fintype I] (owner:I→Fin 3)
local notation "J" => Stock.census (Fin 3)

def value (f:I→ℂ) (v:Fin 3) : ℂ := ∑i,if owner i=v then f i else 0

theorem grouped (f:I→ℂ) :
    (∑i:I,Poly.send ((J).fire (owner i)) (f i))=
      ∑v:Fin 3,Poly.send ((J).fire v) (value owner f v) := by
  classical
  ext s
  simp only [Poly.part_sum,Poly.part_send,value]
  trans ∑i:I,∑v:Fin 3,if s=(J).fire v then (if owner i=v then f i else 0) else 0
  · apply Finset.sum_congr rfl
    intro i _
    have swap (v:Fin 3) :
        (if s=(J).fire v then (if owner i=v then f i else 0) else 0)=
        if owner i=v then (if s=(J).fire (owner i) then f i else 0) else 0 := by
      by_cases eq:owner i=v
      · simp [eq]
      · simp [eq]
    simp_rw [swap]
    simp
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v _
    by_cases h:s=(J).fire v <;> simp [h]

variable {G:Gauge} {n:Side} {q:ℕ} {σ:ℝ}
  (grades:Fin 3→ℕ) (sites:Fin 3→Site n)
  (T:(i:I)→WilsonOlderFreshGraphSlate.Copy G (grades (owner i)) q σ)
  (A:Fin 3→Set ℂ) (charge:I→ℂ)
local notation "M" => rows owner grades sites T A charge
local notation "own" i:max => (T i).rows (home sites (owner i)) (alone A (owner i))

theorem original (g:ℝ) (t:Wallet A) (U:Config G n)
    (shared:Summable (fun k=>Spill.raw M g t k U))
    (held:∀i:I,Summable (fun z=>Spill.raw (own i) g (subject A (owner i) t) z U)) :
    Poly.pass (Spill.Foundry.uncut M g t U)=
      ∏v:Fin 3,(1+Poly.send ((J).fire v) (value owner (fun i=>amount owner grades sites T A charge i g t U) v)) := by
  rw [WilsonOriginalPointCompactFaces.original owner grades sites T A charge g t U shared held,grouped]
  exact Extra.Trajectories.pass_sum univ (J).fire (fun i _=>singleton_nonempty i) _

end YM.Integration.WilsonOriginalThreeCompactProduct
