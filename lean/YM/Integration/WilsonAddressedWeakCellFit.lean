import YM.Integration.WilsonAddressedWeakShapeFees
import YM.Integration.WilsonAddressedWeakTilingCourse

/-! The joint weak placement at its actual plateau span, uniformly over every submitted shape and physical side. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonAddressedWeakCellFit
open Filter Function Set MeasureTheory Metric Lattice Wilson RG Source Cells RG12 Extra.Histories
open RG05Readout Native Address Many Records Harvest Push.GridApprox PhysicalNext.Repeat.Legato
open MergeProof Accent Motion Bandage Extra.Multi Menu
open FVA2 FVA2.ColorCode Pert.Position MS MS.Land MS.Menus MS.Rake MS.Tone
open Extraction Table Spec OPE OPE.Orbits PhysMS XSpace XSpace.Normalize Trace Trace.Pilot
open WilsonThermometerOffsetTrajectory WilsonAddressedWeakPointCells
open scoped Classical BigOperators Topology

private theorem shape (φ:Test 2) :
    ∃ M δ:ℝ,1≤M ∧ 0<δ ∧ δ≤1 ∧ ∀x∈tsupport φ,(∀i,‖x i‖≤M) ∧ δ≤dist (x 0) (x 1) := by
  obtain ⟨b,bound⟩:=φ.hasCompactSupport.isBounded.exists_norm_le
  let M:=max 1 b
  have norm' {x:Points 2} (hx:x∈tsupport φ) (i:Fin 2) : ‖x i‖≤M :=
    (PiLp.norm_apply_le x i).trans ((bound x hx).trans (le_max_right ..))
  by_cases ne:(tsupport φ).Nonempty
  · have f : Continuous (fun x:Points 2=>dist (x 0) (x 1)) := by fun_prop
    obtain ⟨x,hx,hm⟩:=φ.hasCompactSupport.exists_isMinOn ne f.continuousOn
    have sep : x 0≠x 1 := (φ.tsupport_subset hx).ne (by decide)
    refine ⟨M,min 1 (dist (x 0) (x 1)),le_max_left ..,lt_min zero_lt_one (dist_pos.mpr sep),min_le_left ..,?_⟩
    exact fun u hu=>⟨norm' hu,(min_le_right ..).trans (hm hu)⟩
  · exact ⟨M,1,le_max_left ..,zero_lt_one,le_rfl,fun x hx=>(ne ⟨x,hx⟩).elim⟩

variable {G:Gauge} (R:Run G)
local notation "L" => R.family.path.levels

/-- The two stage inequalities use only the saved physical budget factor and its true ratio to the reflected date. -/
theorem original (φ:Test 2) :
    ∃ M δ:ℝ,1≤M ∧ 0<δ ∧ δ≤1 ∧
    ∀ {χ k N p:ℕ} (gr:χ≤k) (_:k≤N) (distanceScale:ℝ),
      32+4*(((L).budget k).B^2:ℕ) < distanceScale*δ →
      (4*M+8)*distanceScale ≤ ((R.family.S.toDepth gr p).count.val:ℝ) →
      let ρ:=R.family.S.a k*distanceScale
      ∃ Q:ℕ,0<ρ ∧ (((L).budget k).B^2+2*Q < (R.family.S.toDepth gr p).count.val) ∧
        ∀ x∈tsupport φ,
        (32+4*(((L).budget k).B^2:ℕ))*(R.family.S.a k/ρ) < dist (x 0) (x 1) ∧
        2*(dist (x 0) (x 1)+32*(R.family.S.a k/ρ)) < (R.family.side k p:ℝ)*(R.family.S.a k/ρ) ∧
        (∀ i,‖x i‖+16*(R.family.S.a k/ρ) ≤ (R.family.S.a k/ρ)*Q) ∧
        (∀ i,ρ*‖x i‖+R.family.S.a N≤R.family.S.a χ/4) := by
  obtain ⟨M,δ,hM,hδ,hδ',fees⟩:=shape φ
  refine ⟨M,δ,hM,hδ,hδ',?_⟩
  intro χ k N p gr live distanceScale fine span
  let b:=(((L).budget k).B^2:ℕ)
  let g:=R.family.S.toDepth gr p
  have mk:=R.family.S.a_pos k
  have bpos : (0:ℝ)≤b:=by positivity
  have f' : (32:ℝ)+4*b<distanceScale*δ:=fine
  have pos : 0<distanceScale := pos_of_mul_pos_left (by linarith only [bpos,f']) hδ.le
  have f1 : (32:ℝ)+4*b<distanceScale:=f'.trans_le (by nlinarith only [mul_le_mul_of_nonneg_left hδ' pos.le])
  let Q:=⌈M*distanceScale+16⌉₊
  have qlo : M*distanceScale+16≤(Q:ℝ):=Nat.le_ceil _
  have qhi : (Q:ℝ)<M*distanceScale+17:=by
    have h:=Nat.ceil_lt_add_one (show 0≤M*distanceScale+16 by positivity)
    linarith only [h]
  have ratio : R.family.S.a k/(R.family.S.a k*distanceScale)=distanceScale⁻¹:=by field_simp
  have gside : (g.count.val:ℝ) ≤ (R.family.side k p:ℝ) := by
    exact_mod_cast (show g.count.val ≤ (R.family.side k p).val by
      rw [g.exact_size]
      exact Nat.le_mul_of_pos_left _ (R.family.side χ p).property)
  have span' : (4*M+8)*distanceScale≤(g.count.val:ℝ):=span
  have Mpos : 0≤M:=by linarith only [hM]
  have mulpos:=mul_nonneg Mpos pos.le
  have center : (b:ℝ)+2*(Q:ℝ)<g.count.val:=by nlinarith only [span',f1,bpos,qhi,mulpos]
  refine ⟨Q,mul_pos mk pos,by exact_mod_cast center,?_⟩
  intro x hx
  obtain ⟨bound,gap⟩:=fees x hx
  dsimp only
  rw [ratio]
  have far : dist (x 0) (x 1)≤2*M:=by
    calc _ ≤ ‖x 0‖+‖x 1‖ := dist_le_norm_add_norm _ _
         _ ≤ 2*M := by linarith only [bound 0,bound 1]
  refine ⟨?_,?_,?_,?_⟩
  · rw [← div_eq_mul_inv]
    exact ((div_lt_iff₀ pos).mpr (by simpa only [mul_comm] using f')).trans_le gap
  · have two : 2*(dist (x 0) (x 1)*distanceScale+32)<(R.family.side k p:ℝ) := by
      nlinarith only [span',gside,mul_le_mul_of_nonneg_right far pos.le,f1,bpos]
    convert mul_lt_mul_of_pos_right two (inv_pos.mpr pos) using 1 <;> first | rfl | field_simp [pos.ne']
  · intro i
    have cost : ‖x i‖*distanceScale+16≤(Q:ℝ):=by nlinarith only [mul_le_mul_of_nonneg_right (bound i) pos.le,qlo]
    convert mul_le_mul_of_nonneg_right cost (inv_nonneg.mpr pos.le) using 1 <;> first | rfl | field_simp [pos.ne']
  · intro i
    have units : R.family.S.a k*(g.count.val:ℝ)=R.family.S.a χ:=R.family.S.embeds_scale g
    have back:=R.family.S.strictAnti.antitone live
    have fee : 4*(distanceScale*‖x i‖+1)≤(g.count.val:ℝ):=by
      nlinarith only [span',mul_le_mul_of_nonneg_left (bound i) pos.le,f1,bpos]
    have paid:=mul_le_mul_of_nonneg_left fee mk.le
    nlinarith only [units,back,paid]

end YM.Integration.WilsonAddressedWeakCellFit
