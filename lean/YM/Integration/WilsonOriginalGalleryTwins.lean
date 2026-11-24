import YM.Lodestar.Unfold
import YM.Integration.WilsonPhysicalHistoryGroupedGas
import YM.Integration.WilsonPhysicalHistoryGroupedHealthy
import YM.Integration.WilsonPhysicalHistoryGroupedEligibility

/-! Double the charged labels of one actual gallery on its own quiet representation. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalGalleryTwins
open Finset Function Lattice Wilson RG Ac Marker Push GridApprox.Nil QuadraticLocal MergeProof MergeProof.Accent
open Extra.Histories Extra.Trajectories QuadraticLocal.Fusion.Attached Lodestar
open scoped BigOperators Classical

variable {V T I : Type} [DecidableEq V] [Fintype V] [Countable I]
  {G : Gauge} {n : Side} {P : Rep G n} {o : V → Site n}
local notation "J₀" => Marks V
local notation "J₁" => Marks (V×Bool)
variable (A:Gallery T I o P (Stock.census V))

def clear (x:T) : Poly (Stock.census V) := WilsonPhysicalHistoryGroupedClear.constant A.E x
def soft (x:T) : Support n → Config G n → Poly (Stock.census V) := WilsonPhysicalHistoryGroupedLamps.grouped A.E {j | ¬ A.E.clear j} x
def hard (x:T) : Box n → Config G n → Poly (Stock.census V) := WilsonPhysicalHistoryGroupedHard.grouped P o A.K
  (univ.erase (Stock.census V).quiet) x

def entered (x:T) := restore P (0 : V×Bool → Config G n → ℂ)
  (0 : V×Bool → Box n → Config G n → ℂ) (fun c => duplicate V ∘ soft A x c)
  (fun c => duplicate V ∘ hard A x c)

theorem paid (x:T)(w:V→ℝ)(pos:∀i,0<w i){a q k:ℝ}(expo:0≤a)
    (reg:A.E.Paid (fun j=>w j^2) P.p.B a q)
    (forced:A.K.Paid (fun j=>w j^2) P.p.B a k)(cost:q≤1)(fee:k≤1):
    Served P 0 0 (entered A x) (o ∘ Prod.fst) (w ∘ Prod.fst) a 1:=by
  let w₂:V→ℝ:=fun j=>w j^2
  have wp(j:V):0<w₂ j:=pow_pos (pos j) _
  have r:=Lamps.loan_monotone A.E reg cost
  have f:=Hard.mono A.K forced fee
  refine ⟨_,_,⟨fun c=>burns_duplicate (WilsonPhysicalHistoryGroupedHealthy.fields A.E w₂ wp _
    expo r (fun _ hi=>hi) x c),fun c=>⟨flow_duplicate (WilsonPhysicalHistoryGroupedEligibility.physical
    P o A.K w₂ wp _ expo f x c),fun U=>large_duplicate ?_⟩⟩,?_,?_,rfl⟩
  · rw [WilsonPhysicalHistoryGroupedEligibility.coefficient P o A.K w₂ wp _ expo f]
    simp
  · exact towed_duplicate w (WilsonPhysicalHistoryGroupedLamps.original A.E w₂ wp _ expo r x)
  · exact towed_duplicate w (WilsonPhysicalHistoryGroupedHard.original P o A.K w₂ wp _ expo f x)

end YM.Integration.WilsonOriginalGalleryTwins
end
