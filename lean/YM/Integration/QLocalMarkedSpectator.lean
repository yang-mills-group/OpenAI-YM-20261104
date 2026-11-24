import YM.Extra.MULTISOURCE_TRAJECTORIES.Algebra
import YM.Integration.LocalComparisonUniformModelPrice

/-! The nonlinear change in a full marked density with its genuine spectator.
The norm on the marked ring sums every mode at its own specified radius. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QLocalMarkedSpectator

open Finset Marker LocalComparison
open scoped Classical BigOperators
variable {V:Type} [DecidableEq V] [Fintype V] {Γ:Census V}

omit [Fintype V] in
theorem normalized_price (w:V→ℝ) (a:Poly Γ) (one:a.part Γ.quiet=1) :
    Poly.price w (a-1)=Poly.price w a-1 := by
  apply (eq_sub_iff_add_eq).mpr
  let f i:=Poly.toll w i*‖(a-1).part i‖
  let g i:=Poly.toll w i*‖a.part i‖
  change (∑ i,f i)+1=∑ i,g i
  rw [←Finset.sum_erase_add _ f (Finset.mem_univ Γ.quiet),
    ←Finset.sum_erase_add _ g (Finset.mem_univ Γ.quiet)]
  have hf:f Γ.quiet=0:=by simp [f,one]
  have hg:g Γ.quiet=1:=by simp [g,one]
  rw [hf,hg,add_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  simp [f,g,Finset.ne_of_mem_erase hi]

theorem relative {w:V→ℝ} (hw:∀v,0<w v) (z:Poly Γ) (hz:z.part Γ.quiet=0)
    {δ:ℝ} (paid:Poly.price w z≤δ) (small:δ≤1) :
    Poly.price w (Poly.pass z-1)≤2*δ := by
  rw [normalized_price w _ (Poly.pass_part z hz)]
  have hn:=Poly.nonnegative hw z
  calc
    _≤Real.exp (Poly.price w z)-1:=sub_le_sub_right (Poly.pass_budget hw z) _
    _≤|Real.exp (Poly.price w z)-1|:=le_abs_self _
    _≤2*|Poly.price w z|:=Real.abs_exp_sub_one_le (by simpa only [abs_of_nonneg hn] using paid.trans small)
    _≤2*δ:=by rw [abs_of_nonneg hn]; linarith

theorem multiply (a b z spectator:Poly Γ) (eq:z=a-b)
    (hb:b.part Γ.quiet=0) (hz:z.part Γ.quiet=0) :
    Poly.pass a*spectator=Poly.pass z*(Poly.pass b*spectator) := by
  have h:a=z+b:=by rw [eq]; abel
  rw [h,Extra.Trajectories.pass_add hz hb,mul_assoc]

theorem charge {w:V→ℝ} (hw:∀ v,0<w v) (a b z spectator:Poly Γ)
    (eq:z=a-b) (hb:b.part Γ.quiet=0) (hz:z.part Γ.quiet=0)
    {δ:ℝ} (paid:Poly.price w z≤δ) (small:δ≤1) :
    Poly.price w (Poly.pass a*spectator-Poly.pass b*spectator)≤
      2*δ*Poly.price w (Poly.pass b*spectator) := by
  rw [multiply a b z spectator eq hb hz,←sub_one_mul]
  exact (Poly.multiplication hw ..).trans (mul_le_mul_of_nonneg_right
    (relative hw z hz paid small) (Poly.nonnegative hw _))

end YM.Integration.QLocalMarkedSpectator
