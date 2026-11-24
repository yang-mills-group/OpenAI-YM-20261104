import YangMills.WilsonProof.NativeSupport.Commissioned259.Origin.Object
import YangMills.WilsonProof.NativeSupport.Commissioned259.ScaleCost.Inverse
/-! # Apply the calculation of the G.1 growing step and G.2 basis costs

In this place *relative to the G.1 compact-ratio comparison*. No need for asymptotic
scale-adjusted identities on vertices other than that comparison. Track the extra
hypotheses (PoseFit/Calibration conclusion on same t, actual hierarchy from §A-B on
these F,H). For Flash259HorizonFork even the weaker merits suffice (`pricing` with Leading).
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar259.Original
open Function Filter Set MeasureTheory Asymptotics Lattice Wilson RG Source Extraction Table Spec
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open Climb Maxwell XSpace XSpace.Normalize XSpace.Structure1 OPE OPE.Orbits PhysMS
open FVA2.Scale Comparing O.Score O.Enh Dframe ScaleCost
open scoped Topology BigOperators Classical
local notation "late" => 𝓝[>] (0:ℝ)
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    {F : Final C f S} (Z : ℝ→PhysMS.tower S) {sim : G.Simple} {d e : ℕ}
lemma shift (v : Sec G d) (r s : ℝ) : via Z r s d v=(frame Z r d).symm (frame Z s d v) := rfl
lemma checks : Balances (via Z) := fun r s u d=> LinearMap.ext fun v=> by rw [Module.End.mul_apply]; simp_rw [shift, LinearEquiv.apply_symm_apply]
lemma reflexive : selfCharge (via Z) := fun r d=> LinearMap.ext fun v=> by rw [shift]; simp

def heights (F:Final C f S) (Z:ℝ→PhysMS.tower S) (s:ℝ) (d:ℕ) := ∀ (e:ℕ) (h:e ≤ d) v,
    frame Z s d (up h v)=F.sector.derivatives.rise h (frame Z s e v)
lemma height {Z : ℝ→tower S} (H : Leading F Z) (d : ℕ) : ∀ᶠ s in late, heights F Z s d := by
  have hp (e:↥(Finset.Iic d)) := H.raised (show e.val≤d from Finset.mem_Iic.mp e.property)
  filter_upwards [Filter.eventually_all.mpr hp] with s h
  intro e he v
  specialize h ⟨e,Finset.mem_Iic.mpr he⟩ ((Maxwell.Free.fields C.labels e).symm v)
  change Z s d ((Maxwell.Free.fields C.labels d).symm (up he v)) = _
  refine Eq.trans (congr_arg (Z s d) ?_) h
  -- trivial by definition of scheme.rise
  simp only [Maxwell.Free.scheme,LinearMap.comp_apply, LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply]

variable {N : WilsonPrescription G} {ν : ℝ}
    {M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}
    {σ : MS.Land.Prescription (Press.portDeck G)} {dial : Bool} (H : Main.Match N sim M σ dial)
    {t : ℝ→ℝ} {a b : ℝ} (W : ℝ) (hW : 1 ≤ W) (hb : 0 < b)
local notation "Vx" => Scale.Measure.outlook N.scheme N.criterion
local notation "Bx" => GroupS.gaugeN N.scheme N.criterion M ν
local notation "Rx" => GroupS.ψ N.criterion M ν
-- don't use local notation in variable (macro hole). hypothesis StepCost wrt those frame fields
variable (ht : t=O[𝓝[>] 0] (g0 G))
    (q : StepCost G (GroupS.ψ N.criterion M ν) (GroupS.gaugeN N.scheme N.criterion M ν) t (via Z))
include q ht hb H
lemma price : ∀ (d : ℕ) (n : ℕ), ∀ᶠ p in atTop, ∃ C : ℝ, 0<C ∧ ∀ᶠ r in late,
    ∀ T ≥ 1, T ≤ a*g0 G r ^ (-b) →
      paired (via Z) Bx Rx t p d r T ≤ C*g0 G r ^ n := fun d n=> movement ((H.dilation ν).check) sim ht hb n (checks Z) q d
lemma weighing (d : ℕ) : ∃ C : ℝ, 0<C ∧ ∀ᶠ r in late, ∀ T ≥ 1, T ≤ a*g0 G r^(-b) →
    stiffness (actual (via Z) d r T) ≤ C * T^d ∧ stiffness (columns (via Z (r*T) r d)) ≤ C :=
  ScaleCost.budget ((H.dilation ν).check) sim ht hb (checks Z) q (reflexive Z) d

include hW in
lemma milestone : Mileage G Bx t (via Z) a b W :=
  mile ((H.dilation ν).check) sim ht hb (checks Z) q hW (reflexive Z)

omit q ht hb
/-- anchor for fixed filtration basis at some late a' ; actually any late enough such anchor
may be used. Not varying in the calculation or altering the measured reader. Uses only compact
ratios of G.1 in forward direction and Match on the first nonlinear coefficients! -/
lemma before (HJ : Leading F Z) (fields : ∀ d : ℕ, FieldQuote G Bx t (via Z) d 1)
    (d : ℕ) : ∀ᶠ a in late, Income (fun i=>stiffness (value (via Z) d a i)) ∧
      Income (fun i=> stiffness (value (via Z) d a i)⁻¹) := by
  filter_upwards [height HJ d] with s h
  apply physical_basis sim (checks Z) ((H.dilation ν).check) t (fun d _=> ScaleCost.linear sim N ν M H _) fields
  intro e he
  refine (height HJ d).mono fun i hi v=>?_
  apply (frame Z i d).injective; rw [shift, LinearEquiv.apply_symm_apply, hi e, shift, LinearEquiv.apply_symm_apply, h e]
end YM.FVA2.GradedFar259.Original
