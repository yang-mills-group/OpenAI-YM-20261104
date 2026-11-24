import YM.LocalLTE.Sail.Tunes
import YM.LocalLTE.Sail.Allocation
/-! Physical issued top projection. Including (possibly rotated) explicit address hulls. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Sail
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open PhysicalNext.Repeat
open Next.Foundations YM.MergeProof Planned.GuardedAtom Motion Guard
open MeasureTheory Pressure ConnectedActivityE6
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge} (P:History G) (N p:ℕ)
variable {d:ℕ} (v:((Labels.frames G).level d).Coeff)
    (M:Motion) (o:∀ i,Site (P.S.side i p))
variable (A:Extra.Histories.Music ((Labels.frames G).level d) P N p)
variable {W:Bid.Worth} {m i j r0 :ℕ}
set_option quotPrecheck false
local notation "F"=> ((Labels.frames G).level d)
local notation "B"=> (localSection G d)
local notation "Z"=> P.rep N p N
noncomputable abbrev zone := upwards M (o N) (booster B (P.rep N p N) 0 v)
noncomputable abbrev window (d:ℕ) := sky M (o N) ((localSection G d).footprint (0:Site (P.S.side N p)))
local notation "Z₀"=> zone P N p v M o
local notation "X"=> window P N p M o d
variable (K:Guard.Keeper ((P.rep N p N).p) ((P.rep N p N).activities))(hs:∀ s,(P.rep N p N).activities.K (K.code s)=0)
    (hx:P.Selected)(hr:A.tone N=summit ((Labels.frames G).level d) (localSection G d) P N p K hs d)(he:Sung (localSection G d) P N p (hol G) W r0 A)(hv: ((Labels.frames G).level d).coeffSize v≤1)
open MergeProof.Accent Push.Local
local notation "Pt"=> (P.rep N p N).p
local notation "B0"=> P.levels.clock.hatBeta N
open Doors
noncomputable def zoneFee (G:Gauge)(d:ℕ)(y:ℝ):ℝ:= (Doors.cameras G d) * y^(Extra.Histories.degree ((Labels.frames G).level d))
lemma placed_window : window P N p M o d = (localSection G d).footprint (o N):=by
    unfold window; rw [shading]; exact (footprint_turn (sound G d) M.1 (0:Site _) (o N)|>.symm).trans (congr_arg _ (by change affine M.1 (o N) 0=o N; simp [affine]))
include hv hx hr he
local notation "O"=> o N
lemma rays_paid (π: (P.rep N p N).activities.Moves M.1 (o N))(hQ:minSide G d≤(P.levels.budget N).B): let X':=window P N p M o d; let Y':= zoneFee G d (P.levels.clock.hatBeta N);
    let q:= zone P N p v M o; let p':=(P.rep N p N).p; hook ((P.rep N p N).activities) ((P.rep N p N).p.threshold) q= profile (P.rep N p N).activities (imprint P N p v M o A π).forced ∧
    (∀ i, q i≠0→ i=X') ∧ Attainment p' (o N) q (Real.exp (p'.supportExponent+2)*Y') ∧ (∀ U,‖q X' U‖ ≤ Y') ∧ X'.card≤ (localSection G d).stencil.card∧ coverNumber (P.levels.budget N).B X'≤1 :=by
    intro x y q p'; let z:= p'; let T₀:=B; let u:=(B).footprint (0:Site (P.S.side N p)); let b:= booster T₀ (P.rep N p N) 0 v
    have hι:= he.head.heard.earns v
    have hh : profile (Z).activities ((A.tone N|>.plays v).forced)= hook (Z).activities z.threshold b:=by
       rw [hr] at hι ⊢; exact onRise (localSection G d) P N p K hs d v (rem_dominated hι.2) -- edit
    refine ⟨?_,?_,?_,?_,?_,?_⟩
    · rw [← Sail.sunny_color]; unfold glyphK; rw [sample_top]; unfold q zone; rw [hooked M (o N) π]; unfold sunny; rw [one_smul]; exact congr_arg _ hh.symm -- b vs φ form
    · intro i hi; obtain ⟨i,rfl⟩:= (sky M (o N)).surjective i
      by_contra hz; have hp:b i=0:= Pi.single_eq_of_ne (show i≠ u from fun h=>hz (congr_arg _ h)) _; apply hi; funext j; unfold q zone upwards; rw [Equiv.symm_apply_apply]; change scalar M (b i _)=0; rw [hp]; exact scalar_z _ -- find
    · have hp:= (P.levels.fits.delayed N).le; let s:= fullCost F (Z).p (Doors.cameras G d); have hδ:0≤ s:=by unfold s fullCost; have ht:=(Z).p.threshold_pos; apply mul_nonneg (zero_le_one.trans (Doors.cameras_ge ..)) (by positivity)
      have hz₀:(F).coeffSize ((F).core v) ≤1:= (Work.G08.size_core ..).trans hv
      have hL:z=P.levels.budget N:= (hx.represents N p N le_rfl).vac; have he':s ≤ y:=by unfold s y zoneFee; rw [show _=fullCost F z _ from rfl,hL]; exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (show 0≤(P.levels.budget N).threshold⁻¹ from inv_nonneg.mpr (P.levels.budget N).threshold_pos.le) (Doors.temp_cheap hp) (Extra.Histories.degree F)) (zero_le_one.trans (Doors.cameras_ge ..))
      let D:=(Labels.frames G).level d; have hwU U:‖supplement (localSection G d) (P.rep N p N) 0 v U‖ ≤ s:= (supplement_bound _ _ (0:Site (P.S.side N p)) (sound G d) (Doors.cameras_ge ..) (fun i=> Doors.cameras_holds G d _ i 0) v _).trans (mul_le_of_le_one_right hδ hz₀)
      let c:Support (P.S.side N p)→ℝ:=Pi.single u s; have hs (i:Support (P.S.side N p)): 0≤ c i:=by by_cases hi:i=u; rw [hi]; rw [show c u=s from Pi.single_eq_same ..]; exact hδ; unfold c; simp [Pi.single_eq_of_ne hi]
      have hz: Attainment z 0 b (Real.exp (z.supportExponent+2)*s) :=by
          refine ⟨fun i=> ?_,fun i h=>?_ ,c, ⟨fun i=> mul_nonneg (Real.exp_nonneg _) (hs i), Summable.of_finite,?_⟩,fun i=>⟨hs i,fun U=>?_⟩⟩
          · by_cases he:i=u
            · rw [he]; unfold b booster; rw [show Pi.single _ _ u = _ from Pi.single_eq_same ..]; exact ⟨supplement_read T₀ (Z) 0 v,supplement_gauge T₀ (Z) 0 (sound G d) v,supplement_meas T₀ (Z) 0 v,healthy_supplement T₀ (Z) 0 (sound G d) v⟩
            rw [show b i=0 from Pi.single_eq_of_ne he _]; exact Attaches.zero ..
          · rw [show i=u from not_not.mp (fun he=> h (Pi.single_eq_of_ne he _))]; exact Finset.mem_image.mpr ⟨0,(sound G d).anchored, by simp⟩
          · have hh: (coverNumber z.B u:ℝ)≤1:=by rw [hL]; exact_mod_cast Doors.close_stencil G d _ (P.S.side N p) hQ 0
            rw [tsum_fintype,Finset.sum_eq_single u,show c u=s from Pi.single_eq_same ..]; exact mul_le_mul_of_nonneg_right (Real.exp_monotone (mul_le_of_le_one_right (add_nonneg z.exponent_pos.le zero_le_two) hh)) hδ
            intro j _ he; rw [show c j=0 from by simp [c,he, Pi.single_eq_of_ne]]; unfold reservedMass; rw [mul_zero]
            simp
          by_cases h:i=u; rw [h,show b u=supplement T₀ (P.rep N p N) 0 v from Pi.single_eq_same .. , show c u=s from Pi.single_eq_same ..]; exact hwU U
          rw [show c i=0 from Pi.single_eq_of_ne h _,show b i=0 from Pi.single_eq_of_ne h _]; simp
      have ht:= rise M (o N) hz; rw [show affine M.1 (o N) (0:Site (P.S.side N p))=o N from by simp [affine]] at ht; exact stackFee ht (mul_le_mul_of_nonneg_left he' (Real.exp_nonneg _))
    · intro U; have hL:z=P.levels.budget N:= (hx.represents N p N le_rfl).vac; have hp:= (P.levels.fits.delayed N).le
      let t:= fullCost F (Z).p (Doors.cameras G d); have ht: 0≤ t:=by unfold t fullCost; have ht:=(Z).p.threshold_pos; apply mul_nonneg (zero_le_one.trans (Doors.cameras_ge ..)) (by positivity)
      have he':t≤ y:=by unfold t y zoneFee; rw [show (Z).p=z from rfl,hL]; exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (show 0≤(P.levels.budget N).threshold⁻¹ from inv_nonneg.mpr (P.levels.budget N).threshold_pos.le) (Doors.temp_cheap hp) (Extra.Histories.degree F)) (zero_le_one.trans (Doors.cameras_ge ..))
      unfold q zone upwards x window; rw [Equiv.symm_apply_apply]; unfold booster stepUp; rw [Pi.single_eq_same, Motion.norm_scalar]
      exact ((supplement_bound _ _ _ (sound G d) (Doors.cameras_ge ..) (fun i=> Doors.cameras_holds G d _ i 0) v _).trans (mul_le_of_le_one_right ht ((Work.G08.size_core ..).trans hv))).trans he'
    · rw [show x=T₀.footprint (o N) from placed_window ..]; exact Finset.card_image_le
    rw [show x=T₀.footprint (o N) from placed_window ..]; exact Doors.close_stencil G d _ _ hQ _
end YM.LocalLTE.Sail
