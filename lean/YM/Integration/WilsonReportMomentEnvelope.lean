import YM.Integration.WilsonReportPrescribedFrame

/-! Absolute ordinary moment bills for the genuine independently prescribed
class fields. These pay the unchanged factors of a disconnected partition. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportMomentEnvelope
open Function Finset Filter Set Metric MeasureTheory Lattice Wilson RG Source Extraction Spec
open PhysicalNext.Repeat.Legato RG17 FullVolume Table Climb Next.UVStress
open scoped Classical BigOperators Topology ContDiff
variable {G : Gauge} {R : Run G} {n : ℕ}
    {f : Extraction.Order} {S : Table R.family.book} (F : Spec.Final R.family f S)

theorem purchased (J : ℝ→PhysMS.tower S) (H : PhysMS.Leading F J)
    {B : (Bel R.family.book).Hierarchy}
    (paid : ∀ d : ℕ,∀ᶠ r in Trace.Pilot.trail,PhysMS.Frame.obedient F B (J r) d)
    (d : Caps n) (K : Set (Points n)) (hk : IsCompact K) (sep : K ⊆ conf n) :
    ∃ M : ℝ,0<M ∧ ∀ᶠ r in Trace.Pilot.trail,∀ x∈K,∀ v : (i:Fin n)→RG17.Free R.family (d i),
      ‖S.classMoment S d (r • x) (fun j=>J r (d j) (v j))‖ ≤ M*∏ j,‖v j‖ := by
  let C := R.family; let T := Bel C.book
  let p (i : Fin n) := T.Field (d i)
  have P := WilsonReportPrescribedFrame.present F J H paid
  have fixed (a : Code p) : ∃ M : ℝ,0≤M ∧ ∀ᶠ r in Trace.Pilot.trail,∀ x∈K,
      ‖S.classMoment S d (r • x) (fun j=>J r (d j) (combination p a j))‖ ≤ M := by
    let v := combination p a
    have h := P.runs F J (fun _=>v) v (fun _=>tendsto_const_nhds) K hk sep 1 one_pos
    have cv : ContinuousOn (fun x=>T.classMoment T d x v) (conf n) :=
      (smoothDisc (Maxwell.Free.hierarchy C.labels).smooth (hang d v)).continuousOn
    obtain ⟨A,hA⟩:=hk.exists_bound_of_continuousOn (cv.mono sep)
    refine ⟨1+|A|,by positivity,?_⟩
    filter_upwards [h] with r hr x hx
    have a := hr x hx
    have b := norm_le_norm_sub_add (S.classMoment S d (r • x) (fun j=>J r (d j) (v j))) (T.classMoment T d x v)
    exact b.trans (add_le_add a ((hA x hx).trans (le_abs_self _)))
  choose M hM all using fixed
  let Z (a : Code p) (i : Fin n) := LinearMap.toContinuousLinearMap ((Module.finBasis ℂ (p i)).coord (a i))
  let size (a : Code p) := ∏ i,‖Z a i‖
  have sn (a : Code p) : 0 ≤ size a := prod_nonneg fun i _=>norm_nonneg (Z a i)
  have price (a : Code p) (v : (i:Fin n)→p i) :
      ‖coords p a v‖ ≤ size a * ∏ i,‖v i‖ := by
    unfold coords size; rw [norm_prod,←prod_mul_distrib]
    exact prod_le_prod (fun i _=>norm_nonneg _) (fun i _=>(Z a i).le_opNorm _)
  let total := ∑ a : Code p, size a*M a
  have ht : 0≤total := sum_nonneg fun a _ => mul_nonneg (sn a) (hM a)
  refine ⟨total+1,by positivity,?_⟩
  filter_upwards [eventually_all.mpr all] with r rows x hx v
  let m := (S.classMoment S d (r • x)).compLinearMap (fun i=>(J r (d i)).toLinearMap)
  let b := ∏ j:Fin n,‖v j‖
  have hb : 0≤b := prod_nonneg fun i _=>norm_nonneg _
  change ‖m v‖ ≤ (total+1)*b
  rw [basis_tuple p v m]
  calc _ ≤ ∑ a:Code p, ‖coords p a v * m (combination p a)‖ := norm_sum_le _ _
       _ ≤ ∑ a:Code p, (size a*M a)*b := sum_le_sum fun a _=>by
         rw [norm_mul]
         exact (mul_le_mul (price a v) (rows a x hx) (norm_nonneg _)
           (mul_nonneg (sn a) hb)).trans_eq (by dsimp [b]; ring)
       _ = total*b := (sum_mul ..).symm
       _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hb

end YM.Integration.WilsonReportMomentEnvelope
