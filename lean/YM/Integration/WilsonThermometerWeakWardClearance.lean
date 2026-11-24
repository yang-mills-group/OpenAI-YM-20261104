import YM.Integration.WilsonThermometerWeakMovedCovers
import YM.Integration.WilsonThermometerWeakWardExterior
import YM.Integration.WilsonThermometerWeakPanelBorn

/-! The genuine right cutoff arm lies outside the finite Haar stencil after
the two independent charged residues have been moved to their elected cells. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakWardClearance
open RG05Readout Native Address Many Records Harvest Push.GridApprox MergeProof
open Function Filter Set Lattice RG Wilson Labels Push Source Next.Extract PhysicalNext.Repeat.Legato Cells
open WilsonThermometerWeakMovedCovers WilsonThermometerWeakPanelBorn WilsonThermometerOffsetTrajectory
open scoped Topology Classical
variable {G:Gauge} (R:Run G)
local notation "C" => R.family
local notation "S" => R.family.S

theorem original (d radius k:ℕ) (positive:0<k):∀ᶠ N:ℕ in atTop,
    ∀ (p m:ℕ) (_placed:m<k) (hk:k≤N) (z:Fin 2→Site ((C).side N p)) (b:Fin 2→Lattice.Cover),
    (∃j:Axis,(S).a m+(S).a k≤|(S).gridPoint k (b 0) j-(S).gridPoint k (b 1) j|) →
    (∀j:Axis,2*(|(S).gridPoint k (b 0) j-(S).gridPoint k (b 1) j|+(S).a k+(S).a m)<
       ((C).side m p).val*(S).a m) →
    let w:=fun i=>move (S) p hk (z i) (wrap ((C).side k p) (b i))
    ∀(t:Site ((C).side N p))(r:Emblems C d)(v:(C).label d),
    LocalOn (Mark.Outer radius (w 0+t)) (arm R r hk (w 1+t) v):=by
  let K:=radius+WilsonThermometerWeakWardExterior.stencil R d
  have small:Tendsto (fun N:ℕ=>(K:ℝ)*(S).a N) atTop (𝓝 0):=by
    simpa only [mul_zero] using (S).shrinks.const_mul (K:ℝ)
  have margin:0<(S).a (k-1)-(S).a k:=sub_pos.mpr ((S).strictAnti (by omega))
  filter_upwards [small.eventually_lt_const margin] with N enough
  intro p m placed hk z b far period w t r v
  obtain ⟨u₀,at₀,low⟩:=letter (S) p hk (z 0) (b 0)
  obtain ⟨u₁,at₁,high⟩:=letter (S) p hk (z 1) (b 1)
  let B:=fun i j=>(S).gridPoint k (b i) j
  let U:=fun (i:Fin 2) j=>(S).gridPoint N (![u₀,u₁] i) j
  have near (j:Axis): |U 0 j-U 1 j|≤|B 0 j-B 1 j|+2*(S).a k ∧
        |B 0 j-B 1 j|≤|U 0 j-U 1 j|+2*(S).a k:=by
    have a:|U 0 j-B 0 j|≤(S).a k:=low j
    have e:|U 1 j-B 1 j|≤(S).a k:=high j
    have x:=abs_sub_le (U 0 j) (B 0 j) (U 1 j)
    have y:=abs_sub_le (B 0 j) (B 1 j) (U 1 j)
    have f:=abs_sub_le (B 0 j) (U 0 j) (B 1 j)
    have g:=abs_sub_le (U 0 j) (U 1 j) (B 1 j)
    rw [abs_sub_comm (B 1 j) (U 1 j)] at y
    rw [abs_sub_comm (B 0 j) (U 0 j)] at f
    constructor <;> linarith
  have same:∀j:Axis,2*|(S).gridPoint N u₀ j-(S).gridPoint N u₁ j|<((C).side N p).val*(S).a N:=by
    intro j
    have side:(((C).side m p).val:ℝ)*(S).a m=(((C).side N p).val:ℝ)*(S).a N:=by
      rw [mul_comm _ ((S).a m),mul_comm _ ((S).a N),(S).span_side,(S).span_side]
    have pair:=period j
    rw [side] at pair
    change 2*|U 0 j-U 1 j|<_
    change 2*(|B 0 j-B 1 j|+_+_)<_ at pair
    linarith only [pair,(near j).1,(S).strictAnti.antitone placed.le]
  obtain ⟨i,dist⟩:=far
  have farN:(K:ℝ)*(S).a N < |(S).gridPoint N u₀ i-(S).gridPoint N u₁ i|:=by
    have km: (S).a (k-1)≤(S).a m:=(S).strictAnti.antitone (by omega)
    change (S).a m+(S).a k≤|B 0 i-B 1 i| at dist
    change _ < |U 0 i-U 1 i|
    linarith only [enough,km,dist,(near i).2]
  have sep:=WilsonThermometerWeakWardExterior.grid N p u₀ u₁ K same ⟨i,farN⟩
  have sep':K<separation (w 1+t) (w 0+t):=by
    rw [separation_comm, separation,add_sub_add_right_eq_sub]
    change K < separation (w 0) (w 1)
    simpa only [at₀,at₁] using sep
  exact WilsonThermometerWeakWardExterior.original R d N p _ _ _ _ radius sep'

end YM.Integration.WilsonThermometerWeakWardClearance
end
