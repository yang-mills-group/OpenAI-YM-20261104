import YM.Integration.WilsonPositionProgramCells
import YM.Integration.WilsonPositionHomogeneousComparison

/-! Convert the canonical MS components of the independently computed position program
with the one filed continuum coupling and field series. Their finite coefficient fees are
fixed before the physical radius and both regulators. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionProgramFixedFrame
open Filter Function Set Finset Maxwell XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open FVA2 FVA2.Register FVA2.Scale FVA2.Arrival MS MS.Land MS.Book.Program MS.Fleet
open scoped Topology BigOperators Classical
variable {G : Gauge} (Z : WilsonPrescription G)
    {g : G.Simple} {M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}
    {T : Prescription (Press.portDeck G)} {dial : Bool} (H : Main.Match Z g M T dial)
    (μ : ℝ) {d n : ℕ} (v : Tags G d n) (k : ℕ)
local notation "F" => Measure.f Z.criterion μ M
local notation "Q" => Measure.Z Z.scheme Z.criterion μ M d

def factor (a : Days n) (j : ℕ) (t : Fin n → Dframe.Toon G d) : ℂ :=
  cut F j (a none) * Dframe.each t (pulseU a Q v)

def value (r : (Fin n → Dframe.Toon G d) → ℕ → ℂ) : ℂ :=
  ∑ a∈tally k n, ∑ j∈Iic (a none), ∑ t, factor Z (M:=M) μ v a j t * r t j

def fee : ℝ := ∑ a∈tally k n, ∑ j∈Iic (a none), ∑ t, ‖factor Z (M:=M) μ v a j t‖

theorem priced {A B : (Fin n → Dframe.Toon G d) → ℕ → ℂ} {E : ℝ}
    (prices : ∀ t (j : ℕ), j≤k → ‖A t j-B t j‖≤E) :
    ‖value Z (M:=M) μ v k A - value Z (M:=M) μ v k B‖ ≤ fee Z (M:=M) μ v k*E := by
  unfold value fee
  simp_rw [Finset.sum_mul,←sum_sub_distrib,←mul_sub]
  refine (norm_sum_le ..).trans (sum_le_sum (fun a ha=>?_))
  refine (norm_sum_le ..).trans (sum_le_sum (fun j hj=>?_))
  refine (norm_sum_le ..).trans (sum_le_sum (fun t _=>?_))
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact prices t j ((mem_Iic.mp hj).trans (((totaled a).mp ha) ▸ single_le_sum
    (f:=fun p=>a p) (fun _ _=>Nat.zero_le _) (mem_univ none)))

include H in
theorem output (x : Scale.Stage n) :
    value Z (M:=M) μ v k (fun t j=>Dframe.meteor μ M d x j (Dframe.fill t)) =
      Measure.outlook Z.scheme Z.criterion d n x k v := by
  rw [←WilsonPositionHomogeneousComparison.filed Z M H μ d x v k]
  unfold WilsonPositionHomogeneousComparison.coefficient Facets.actMark
  rw [Dframe.seen]
  unfold Facets.couple Equator.wave
  simp only [rules, _root_.sum_apply, _root_.smul_apply,smul_eq_mul]
  unfold value factor
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro j _
  rw [Dframe.stencil_he (Dframe.meteor μ M d x j) (pulseU a Q v),Finset.mul_sum]
  exact sum_congr rfl fun t _=>by ring

include H in
theorem auxiliary (K : Set (Points n)) (compact : IsCompact K) (sep : K ⊆ conf n) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ i:ℕ in atTop, ∀ B (P:Handoff.Directory Z i B),
      Handoff.Directory.budget G n d+k ≤ B → ∀ x (hx : x∈K),
      ‖value Z (M:=M) μ v k (fun t j=>WilsonPositionProgramPoint.entry Z (T:=T) P d μ
        (draw x (Z.run.step i) (river (Z.run.step i))) (Dframe.fill t) j) -
        Measure.outlook Z.scheme Z.criterion d n ⟨x,sep hx⟩ k v‖ ≤
        C*(Speed.chip (Z.run.step i)+(Z.run.step i).spacing) := by
  choose C pos estimates using fun (t:Fin n → Dframe.Toon G d) (s:Fin (k+1))=>
    WilsonPositionProgramCells.compact Z H d μ (Dframe.fill t) s K compact sep
  let W := ∑ t, ∑ s, C t s
  have wpos : 0≤W := sum_nonneg fun t _=>sum_nonneg fun s _=>(pos t s).le
  have bounds (t) (s) : C t s ≤ W :=
    (single_le_sum (f:=C t) (fun j _=>(pos t j).le) (mem_univ s)).trans
      (single_le_sum (f:=fun u=>∑ j,C u j) (fun u _=>sum_nonneg fun j _=>(pos u j).le) (mem_univ t))
  have charge : 0≤fee Z (M:=M) μ v k := sum_nonneg fun _ _=>sum_nonneg fun _ _=>sum_nonneg fun _ _=>norm_nonneg _
  refine ⟨1+fee Z (M:=M) μ v k*W,by positivity,?_⟩
  filter_upwards [eventually_all.mpr (fun t=>eventually_all.mpr (fun s=>estimates t s))] with i all
  intro B P cap x hx
  let m := Z.run.step i
  have price : 0≤Speed.chip m+m.spacing := add_nonneg (Real.rpow_nonneg m.positive.le _) m.positive.le
  rw [←output Z H μ v k ⟨x,sep hx⟩]
  refine (priced Z (M:=M) μ v k (E:=W*(Speed.chip m+m.spacing)) ?_).trans ?_
  · intro t j hj
    have hs : j < k+1 := by omega
    exact ((all t ⟨j,hs⟩) B P (by omega) x hx).trans (mul_le_mul_of_nonneg_right (bounds t ⟨j,hs⟩) price)
  · rw [←mul_assoc]
    exact mul_le_mul_of_nonneg_right (by linarith) price

end YM.Integration.WilsonPositionProgramFixedFrame
