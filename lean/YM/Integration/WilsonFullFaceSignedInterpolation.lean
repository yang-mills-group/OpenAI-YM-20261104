import YM.Integration.WilsonCapturedPrimarySoftLoad
import YM.Integration.WilsonFullFaceSignedHard
import YM.Extra.SOURCE_HISTORIES.Pencil

/-! Interpolate only the finitely many old regular occurrences in the
three occupied source names. The genuine Wilson fields and the entire
quiet law are fixed at every interpolation node. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonFullFaceSignedInterpolation
open Finset Lattice RG Wilson Marker Multi QuadraticLocal Source Labels Extra.Histories Next.Foundations
open Push.Local Planned.GuardedAtom WilsonCenteredFiledAtoms
open WilsonCapturedPrimarySoftPartition Comparison.RG02.Cumulants
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} {V X ι : Type} [DecidableEq V] {R : Census V}
    {o : V→Site n} {p : BudgetPoint}

def scale (L : Lamps X ι G p o R) (c : ℂ) : Lamps X ι G p o R :=
  { L with
    nominal := fun x j=>c • L.nominal x j
    legal := fun x j=>regular_smul c (L.legal x j)
    pure := fun x j U h=>congrArg (c*·) (L.pure x j U h) }

theorem paid (L : Lamps X ι G p o R) (c : ℂ) (w : V→ℝ) {B : ℕ} {a E : ℝ}
    (fare : L.Paid w B a E) : (scale L c).Paid w B a (‖c‖*E) :=by
  obtain ⟨f,pos,law,res⟩:=fare.budget
  refine ⟨fun i=>‖c‖*f i,fun i=>mul_nonneg (norm_nonneg _) (pos _),
    fun i x y hy=>bound_smul _ (law i x y hy),fun y=>?_⟩
  convert Push.AbsoluteSums.budget_scale (norm_nonneg c) (res y) using 1
  funext i
  change (if y∈L.ground i then Poly.toll w (L.mode i)*(‖c‖*f i)*Real.exp (a*coverNumber B (L.ground i)) else 0)=
    ‖c‖*(if y∈L.ground i then Poly.toll w (L.mode i)*f i*Real.exp (a*coverNumber B (L.ground i)) else 0)
  by_cases h:y∈L.ground i
  · rw [if_pos h,if_pos h];ring
  · simp only [h,if_false,mul_zero]

theorem reading (L : Lamps X ι G p o R) (c : ℂ) (x : X) (U : Config G n) :
    (scale L c).log x U=c • L.log x U :=by
  have frame (i:ι) : (scale L c).frame i x U=c • L.frame i x U :=by
    apply Marker.Poly.ext
    intro s
    change (Poly.send (L.mode i) ((scale L c).light x i U)).part s=(c • Poly.send (L.mode i) (L.light x i U)).part s
    rw [Poly.part_send,Poly.part_smul,Poly.part_send]
    by_cases id:s=L.mode i
    · rw [if_pos id,if_pos id]
      by_cases h:L.clear i
      · simp [Lamps.light,scale,h]
      · change (if L.clear i then _ else masked p.threshold (L.ground i) (c • L.nominal x i) U)=
          c*(if L.clear i then _ else masked p.threshold (L.ground i) (L.nominal x i) U)
        rw [if_neg h,if_neg h]
        by_cases good:Healthy p.threshold (L.ground i) U
        · rw [masked_eq _ _ _ _ good,masked_eq _ _ _ _ good];rfl
        · rw [masked_ne _ _ _ _ good,masked_ne _ _ _ _ good,mul_zero]
    · simp only [id,if_false,mul_zero]
  unfold Lamps.log
  simp_rw [frame]
  rw [tsum_const_smul'']

/-- The four coefficients are divided by the single old error before use. -/
def coins (z : ℂ) : Fin 4 → ℂ :=
  ![(-z^2+6*z-11)/6,(z-2)*(z-3)/2,-(z-1)*(z-3)/2,(z-1)*(z-2)/6]

private theorem cubic {k : ℕ} (bound : k≤3) (a b : Fin k→ℂ) (z : ℂ) :
    (∏ j,(a j+z*b j))-(∏ j,a j)=z*∑j:Fin 4,coins z j*∏l,(a l+(j.val:ℂ)*b l) :=by
  interval_cases k <;> simp [coins,Fin.sum_univ_succ,Fin.prod_univ_succ] <;> ring <;> simp

theorem table [Fintype V] (s : R.Mode) (load : s.val.card≤3) (a b : Poly R) (z : ℂ)
    (quietA : a.part R.quiet=0) (quietB : b.part R.quiet=0) :
    (Poly.pass (a+z • b)).part s-(Poly.pass a).part s=
      z*∑j:Fin 4,coins z j*(Poly.pass (a+(j.val:ℂ) • b)).part s :=by
  have blank (t:ℂ) : (a+t • b).part R.quiet=0 :=by simp only [Marker.Poly.part_plus,Poly.part_smul,quietA,quietB,mul_zero,add_zero]
  rw [pass_partition _ (blank z),pass_partition _ quietA,←sum_sub_distrib]
  simp_rw [pass_partition _ (blank _)]
  simp_rw [mul_sum]
  rw [sum_comm]
  simp_rw [←mul_sum]
  rw [mul_sum]
  apply sum_congr rfl
  intro q allowed
  simp_rw [←enumerate q]
  simpa only [Marker.Poly.part_plus,Poly.part_smul] using
    cubic ((WilsonCapturedPrimarySoftLoad.size allowed).trans load)
      (fun j=>a.part (block q j)) (fun j=>b.part (block q j)) z

variable {P : Rep G n} {d : ℕ} {F : Frame G d}

theorem painted (S : SectionData F) (Y : Hol G) (y : Site n) {κ f : ℝ} (c : ℂ) {v : Config G n→ℂ}
    (issued : Store P S Y y κ f v) : Store P S Y y κ (‖c‖*f) (fun U=>c*v U) := by
  obtain ⟨r,fmt,cost,val⟩:=issued
  exact ⟨stretch c r,stretch_format c fmt,stretch_rem c cost,fun U=>
    (stretch_density S P y c r U).trans (congrArg (c*·) (val U))⟩

end YM.Integration.WilsonFullFaceSignedInterpolation
