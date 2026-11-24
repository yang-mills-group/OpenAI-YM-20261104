import YM.Integration.WilsonIndependentCollarSelfSalary
import YM.Integration.WilsonIndependentCollarFirstRung

/-! The complete first nonconstant finite-board heat row on the original
posted packet, with a rooted wage for each incoming marked subset. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentCollarFirstStudent
open Finset Function Lattice Laurent Bloch Metric Precision RG Work.F08 Wilson FormalBulk08
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Winding
open WilsonCoeffUV.Soil WilsonCoeffUV.Mer WilsonCoeffUV.Cosmos WilsonCoeffUV.Blue WilsonCoeffUV.Embroider
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open scoped Classical BigOperators

private def measure {U E : Type} [Fintype U] [NormedAddCommGroup E] (w:U→ℝ) (F:U→E) :=
  ∑ x,w x*‖F x‖

private theorem two {U E : Type} [Fintype U] [NormedAddCommGroup E] (w:U→ℝ) (hw:∀x,0≤w x)
    (f h : U→E) : measure w (f+h)≤ measure w f+measure w h := by
  simp only [measure,←sum_add_distrib,←mul_add]
  exact sum_le_sum fun x _=>mul_le_mul_of_nonneg_left (norm_add_le _ _) (hw x)

private theorem many {U E β : Type} [Fintype U] [NormedAddCommGroup E]
    (w:U→ℝ) (hw:∀x,0≤w x) (s:Finset β) (f:β→U→E) :
    measure w (∑j∈s,f j)≤∑j∈s,measure w (f j) := by
  simp only [measure,Finset.sum_apply]
  calc
    _ ≤ ∑ x,w x*∑ j∈s,‖f j x‖ :=
      sum_le_sum fun x _=>mul_le_mul_of_nonneg_left (norm_sum_le ..) (hw x)
    _ = _ := by simp only [mul_sum]; rw [sum_comm]

private theorem shift {U β : Type} {r:ℕ} (d:Distance U) (o w:U) (x:dock U β r) :
    tread d o x ≤ tread d w x + d.gap o w := by
  apply league_le
  refine Fin.cases ?_ (fun i=>?_)
  · refine Fin.cases ?_ (fun j=>?_)
    · simpa only [stud,Fin.cons_zero,d.self] using Nat.zero_le (tread d w x+d.gap o w)
    · have h := leg_le d (stud w x) 0 j.succ
      have t := d.tri o w (x j).1
      change d.gap o (x j).1≤_
      change d.gap w (x j).1≤tread d w x at h
      omega
  · refine Fin.cases ?_ (fun j=>?_)
    · have h := leg_le d (stud w x) i.succ 0
      have t := d.tri (x i).1 w o
      rw [d.swap w o] at t
      change d.gap (x i).1 o≤_
      change d.gap (x i).1 w≤tread d w x at h
      omega
    · exact (leg_le d (stud w x) i.succ j.succ).trans (Nat.le_add_right ..)

variable {G : Gauge} {I : Arch G} {e : ℕ} {ι : Type} [DecidableEq ι] {D k : ι→ℕ} {Z : Finset ι}

def wage (p : PackOne Z D k e I) (S:Finset ι) (o:Site p.V.n) (r:ℕ) :=
  ∑ x,Real.exp (I.s*tread (tor p.V.n) o x)*‖p.surfU S 0 0 r x‖

theorem original (p : PackOne Z D k e I) (S : Finset ι) (r : ℕ)
    (o : Site p.V.n) (l u : Finset ι→Site p.V.n) (front : ∀T∈S.powerset,o=l T ∨ o=u T) :
    ∑ x,Real.exp ((I.s/2)*tread (tor p.V.n) o x)*‖p.surfU S 1 0 r x‖ ≤
      WilsonIndependentCollarSelfSalary.coefficient r I.mass * wage p S o (r+2) +
      ∑ T∈S.powerset,∑ a∈antidiagonal r,
        (sealM a.1 a.2*I.mass) * (wage p T (l T) (a.1+1) * wage p (S\T) (u T) (a.2+1)) := by
  let d:=tor p.V.n
  let w (x : dock (Site p.V.n) I.dial r) := Real.exp ((I.s/2)*tread d o x)
  have hw (x) : 0≤w x := (Real.exp_pos _).le
  change measure w (p.surfU S 1 0 r) ≤ _
  rw [WilsonIndependentCollarFirstRung.original]
  apply (two w hw _ _).trans
  apply add_le_add
  · apply le_trans _ (WilsonIndependentCollarSelfSalary.posted (S:=S) p o 0 0 r)
    apply sum_le_sum; intro x _
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
    linarith [I.h]
  · apply (many w hw _ _).trans
    apply sum_le_sum;intro T hT
    have sub : T⊆S := mem_powerset.mp hT
    simp only [dif_pos sub]
    apply (many w hw _ _).trans
    apply sum_le_sum;intro a ha
    obtain ⟨i,j⟩:=a
    have eq : i+j=r := mem_antidiagonal.mp ha
    subst r
    apply le_trans _ (WilsonIndependentCollarBinarySalary.posted p sub 0 0 0 0 i j (l T) (u T))
    apply sum_le_sum; intro x _
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply Real.exp_le_exp.mpr
    let M : ℝ := max (tread d (u T) x) (d.gap (l T) (u T))
    have h : (tread d o x:ℝ)≤2*M := by
      change _ ≤ 2*max (tread d (u T) x:ℝ) (d.gap (l T) (u T))
      have h₁ := le_max_left (tread d (u T) x:ℝ) (d.gap (l T) (u T))
      have h₂ := le_max_right (tread d (u T) x:ℝ) (d.gap (l T) (u T))
      rcases front T hT with ho|ho
      · rw [ho]
        have hc : (tread d (l T) x:ℝ)≤tread d (u T) x+d.gap (l T) (u T) := by
          exact_mod_cast shift d (l T) (u T) x
        linarith
      · rw [ho]; linarith [Nat.cast_nonneg (d.gap (l T) (u T)) (α:=ℝ)]
    have hh:=mul_le_mul_of_nonneg_left h I.h.le
    rw [Nat.cast_max]
    change I.s/2*tread d o x ≤ I.s*M
    linarith

end YM.Integration.WilsonIndependentCollarFirstStudent
