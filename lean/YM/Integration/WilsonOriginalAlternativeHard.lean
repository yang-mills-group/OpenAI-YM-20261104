import YM.Integration.WilsonOriginalAlternativePurse
import YM.QuadraticLocal.Lamps
import YM.QuadraticLocal.Tariff.Measure

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalAlternativeHard
open Function Finset Lattice Wilson RG Ac Marker QuadraticLocal Push.Corrected Push.AbsoluteSums MeasureTheory
open Push RG3 RG3.Ink Ovens Ovens.Pipes Progress.DirectedRecipe Fusion Attached
open WilsonOriginalAlternativeNames WilsonOriginalAlternativePurse
open scoped Classical BigOperators Topology
variable {V:Type} [DecidableEq V] [Fintype V] {R:Census V}
variable {G:Gauge} {n:Side} {T I:Type} {o:V→Site n} {p:BudgetPoint}
variable {F:ℕ→ForcedAddress G n} {K:Code G n}

def linear : Poly R →L[ℂ] Poly (board R) :=
  (inheritAll R).toLinearMap.toContinuousLinearMap

def issued (H:Hard T p F K o R) : Hard T p F K (o ∘ Prod.fst) (board R) where
  hard t i U:=inheritAll R (H.hard t i U)
  locality t i:=by
    refine ⟨fun g U=>congrArg (inheritAll R) ((H.locality t i).gauge g U),
      (linear (R:=R)).continuous.measurable.comp (H.locality t i).borel,
      fun U U' hd hf=>congrArg (inheritAll R) ((H.locality t i).reads U U' hd hf),?_⟩
    intro U s live j hj
    apply (H.locality t i).carry U (base R s) _ j.1 (Finset.mem_image_of_mem Prod.fst hj)
    intro vanish
    apply live
    rw [inherited,vanish,mul_zero]
  charged t i U live:=H.charged t i U (fun h=>live (by rw [h,map_zero]))
  quiet t i U:=(quiet R _).trans (H.quiet t i U)

theorem paid (H:Hard T p F K o R) {w:V→ℝ} (wp:∀i,0<w i) {B:ℕ} {a k:ℝ}
    (fund:H.Paid w B a k) : (issued H).Paid (wallet R w) B a k := by
  obtain ⟨f,major,fees⟩:=fund.wages
  refine ⟨fun i=>inheritAll R (f i),?_,?_⟩
  · intro i t U s
    change ‖(inheritAll R (H.hard t i U)).part s‖ ≤((inheritAll R (f i)).part s).re ∧
      ((inheritAll R (f i)).part s).im=0
    simp only [part]
    split
    · exact major i t U (base R s)
    · simp
  intro x
  apply budget_mono (fees x)
  · intro i; split
    · exact mul_nonneg (Poly.nonnegative (positive R wp) _) (Real.exp_nonneg _)
    · exact le_rfl
  · intro i; split
    · exact mul_le_mul_of_nonneg_right (total R wp (f i)) (Real.exp_nonneg _)
    · exact le_rfl

variable {P:Rep G n}

theorem lot (H:Hard T P.p P.activities.forced P.activities.K o R) (s:Finset ℕ) (t:T) (U:Config G n) :
    packet P.activities P.p ((issued H).hard t) U s =
      inheritAll R (packet P.activities P.p (H.hard t) U s) := by
  unfold packet
  split
  · rw [map_prod];rfl
  · exact (map_zero _).symm

theorem entire (H:Hard T P.p P.activities.forced P.activities.K o R) {w:V→ℝ} (wp:∀i,0<w i)
    {a k:ℝ} (ha:0≤a) (fund:H.Paid w P.p.B a k) (t:T) (U:Config G n) :
    (∑' s,packet P.activities P.p ((issued H).hard t) U s)=
      inheritAll R (∑' s,packet P.activities P.p (H.hard t) U s) := by
  change _=linear (∑' s,packet P.activities P.p (H.hard t) U s)
  rw [(linear (R:=R)).map_tsum (H.packet_summing fund ha wp t U)]
  exact tsum_congr fun s=>lot H s t U

end YM.Integration.WilsonOriginalAlternativeHard
