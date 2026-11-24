import YM.PertExtension.MatrixFreeLeaf
import YM.PertExtension.CurlSymbol
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! Original infinite-volume slot symbol and scaling chart. Cube volume
uses planar momentum coordinates $p=2π x$. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
namespace YM.PertExtension.LatticePT
namespace Converter
open MeasureTheory Filter Topology Analysis Maxwell Asymptotics Next.Rank Next.Rank.Radian Set Real Metric Lattice Beamer CellsInt Wall Band
open Configuration Air Orb Orbit GaussianScore Function Finset Projection
open scoped ContDiff Topology BigOperators Classical NNReal ENNReal
local notation "ℑ" => Complex.I

def radius : ℝ :=2*π
lemma radius_pos:0<radius:=by unfold radius; positivity
def unitbox : Set E4:={z | ∀ i, -(1:ℝ)/2 < z i ∧ z i ≤ 1/2}
def opencube : Set E4:={z | ∀ i, -(1:ℝ)/2 < z i ∧ z i < 1/2}
def closedunit : Set E4:={z | ∀ i, -(1:ℝ)/2 ≤ z i ∧ z i≤1/2}
def rawAxis : E4 ≃ᵐ Momentum := (PiLp.homeomorph 2 (fun _:Axis=>ℝ)).toMeasurableEquiv
lemma cube_meas : MeasurableSet cube:=isClosed_set_pi (fun i _=>isClosed_Icc)|>.measurableSet
lemma chart (z:E4) : (rawAxis (radius • z)∈ cube ↔ z∈closedunit) := by
  constructor
  · intro h; intro i
    obtain ⟨hh,hh'⟩:=h i (show i∈Set.univ from Set.mem_univ _)
    have hp:0<π:=Real.pi_pos
    change (2*π)*z i≥ -π at hh
    change (2*π)*(z i) ≤ π at hh'
    change -(1:ℝ)/2 ≤ z i ∧ z i ≤ (1:ℝ)/2
    constructor <;> nlinarith
  intro h i h';obtain ⟨hl,hu⟩ := h i; have hp:0<π:=Real.pi_pos
  change (2*π)*(z i) ≥ -π ∧ 2*π * z i ≤ π; constructor <;> nlinarith
lemma cube_eq (z:E4):WithLp.ofLp (radius • z)∈cube ↔ z∈closedunit:=chart ..

lemma not_hyperplane (k:Axis)(r:ℝ):∀ᵐ z:E4,z k≠r:=by
  have hs := PiLp.volume_preserving_ofLp Axis
  rw [ae_iff, show {z:E4 | ¬z k≠r}=rawAxis ⁻¹' Set.pi Set.univ (fun j:Axis=>if j=k then {r} else univ) from ?_]
  · rw [(show MeasurePreserving rawAxis volume volume from hs).measure_preimage (MeasurableSet.nullMeasurableSet (MeasurableSet.pi (Set.countable_univ) (fun i _=>?_))),show (volume :Measure Momentum)=Measure.pi fun _ : Axis=>volume from rfl,Measure.pi_pi]
    exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp)
    split_ifs <;> simp
  ext z; constructor
  · intro hz i _; change ¬z k≠r at hz
    change rawAxis z i ∈ if i=k then {r} else Set.univ
    by_cases h:i=k
    · rw [if_pos h];subst i; exact (not_not.mp hz : z k=r)
    simp only [if_neg h]; exact Set.mem_univ _
  intro h he
  apply he
  have ht := h (i:=k) (Set.mem_univ _)
  simp at ht
  exact ht
lemma same_ae : ∀ᵐ z:E4,z∈closedunit ↔ z∈unitbox:= by
  filter_upwards [MeasureTheory.ae_all_iff.mpr (fun i:Axis => not_hyperplane i (-1/2))] with x hx
  exact ⟨fun h i=>⟨lt_of_le_of_ne (h i).1 (by exact Ne.symm (hx i)),(h i).2⟩,fun h i=>⟨(h i).1.le,(h i).2⟩⟩

def pointAt (z : E4):Momentum := WithLp.ofLp (radius • z)
def packet (p s:RG.Slot)(z:E4):= unitbox.indicator (fun z=>bubble p s (pointAt z)) z

theorem convert_int (p s:RG.Slot) : kernelEntry p s = ∫ z:E4, packet p s z :=by
   let f:=cube.indicator (bubble p s)
   have ht:= (Measure.integral_comp_smul_of_nonneg (volume:Measure E4) (f:=f ∘ rawAxis) radius (hR:=radius_pos.le))
   have h:= (PiLp.volume_preserving_ofLp Axis).integral_comp rawAxis.measurableEmbedding f
   have h' : Module.finrank ℝ E4=4:=spaceD
   unfold kernelEntry
   rw [← integral_indicator cube_meas, div_eq_inv_mul]
   change (radius^4)⁻¹ * (∫ z:Momentum, f z)= _
   rw [← h]
   change (radius^4)⁻¹ • (∫ z:E4, (f ∘ rawAxis) z)= _
   rw [h'] at ht
   rw [← ht] -- ht rewrite wrong
   apply integral_congr_ae
   exact same_ae.mono fun z hz=> by
      change f (rawAxis (radius • z))= _
      have h : rawAxis (radius • z)=pointAt z:=rfl
      unfold f; by_cases hx:z∈unitbox
      · rw [indicator_of_mem ((chart z).mpr (hz.mpr hx)) .., h,packet,indicator_of_mem hx]
      rw [indicator_of_notMem (by intro h; exact hx (hz.mp ((chart z).mp h))),packet,indicator_of_notMem hx]

end Converter
end YM.PertExtension.LatticePT

