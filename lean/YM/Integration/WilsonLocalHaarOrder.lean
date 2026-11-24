import YM.Integration.WilsonConditionalTaylorThermalLocalHaar

/-! All genuine Taylor coefficients of the original local logarithmic Haar
density and a finite-coupling bound summed only over the charted bonds. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonLocalHaarOrder
open Function Filter Finset Lattice RG Tree Wilson Precision Push.BetaTransport
open PertExtension PertExtension.Series Radial WilsonConditionalTaylorThermalLocalHaar
open scoped Classical BigOperators Topology ContDiff
variable {G:Gauge} (P:ChartRatio G) (R:LocalRatio P)
def logarithm (z:G.Color):ℝ:=Real.log (Chart.fee P z/P.scale)
def row (k:ℕ) (z:G.Color):ℝ:=jet (logarithm P) k z
def polynomial (p:ℕ) (t:ℝ) (z:G.Color):ℝ:=Zone.eval (row P) p t z

include R

theorem smooth : ContDiffAt ℝ ∞ (logarithm P) 0 := by
  have sm : ContDiffAt ℝ ∞ (Chart.fee P) 0 := (Chart.Ratio.fee_smooth R).of_le (by simp)
  apply (sm.div_const P.scale).log
  rw [anchor P R,div_self R.scale.ne'];exact one_ne_zero

theorem even {k:ℕ} (h:Odd k) (z:G.Color) : row P k z=0 := by
  apply WilsonConditionalTaylorThermalHaarOdd.diagonal (smooth P R) _ h z
  filter_upwards [WilsonConditionalTaylorThermalHaarOdd.mirror P R] with x hx
  simp only [logarithm,hx]

theorem oneBond (p:ℕ) : ∃δ C:ℝ,0<δ ∧ 0≤C ∧ ∀z:G.Color,∀t:ℝ,0<t→t*‖z‖≤δ→
    0<Chart.fee P (t•z) ∧ |logarithm P (t•z)-polynomial P p t z|≤C*t^(p+1)*‖z‖^(p+1) := by
  obtain ⟨δ,C,hδ,hC,bill⟩:=deposition (logarithm P) p (smooth P R)
  obtain ⟨η,A,hη,_,positive⟩:=WilsonConditionalTaylorThermalLocalHaar.original P R
  refine ⟨min δ η,C,lt_min hδ hη,hC,?_⟩
  intro z t ht room
  have hz : ‖t•z‖≤η := by
    simpa only [norm_smul,Real.norm_eq_abs,abs_of_pos ht] using room.trans (min_le_right δ η)
  refine ⟨(positive (t•z) hz).1,?_⟩
  change |logarithm P (t•z)-Zone.eval (jet (logarithm P)) p t z|≤_
  simpa only [Real.norm_eq_abs,mul_right_comm] using
    bill z t ht (room.trans (min_le_left δ η))

theorem original (p:ℕ) : ∃δ C:ℝ,0<δ ∧ 0≤C ∧ ∀(ι:Type) [Fintype ι] (X Y:ι→G.Color) (g:ℝ),0<g→
    (∀i,g*‖X i‖≤δ ∧ g*‖Y i‖≤δ)→
    0<Chart.jacobian P (g•X) ∧ 0<Chart.jacobian P (g•Y) ∧
    |Real.log (Chart.jacobian P (g•X)/Chart.jacobian P (g•Y))-
      ∑i,(polynomial P p g (X i)-polynomial P p g (Y i))|≤
      C*g^(p+1)*∑i,(‖X i‖^(p+1)+‖Y i‖^(p+1)) := by
  obtain ⟨δ,C,hδ,hC,bill⟩:=oneBond P R p
  refine ⟨δ,C,hδ,hC,?_⟩;intro ι _ X Y g hg room
  have fx (i:ι):=bill (X i) g hg (room i).1
  have fy (i:ι):=bill (Y i) g hg (room i).2
  have posX : 0<Chart.jacobian P (g•X) := Finset.prod_pos (fun i _=>(fx i).1)
  have posY : 0<Chart.jacobian P (g•Y) := Finset.prod_pos (fun i _=>(fy i).1)
  refine ⟨posX,posY,?_⟩
  have logs : Real.log (Chart.jacobian P (g•X)/Chart.jacobian P (g•Y))=
      ∑i,(logarithm P (g•X i)-logarithm P (g•Y i)) := by
    rw [Real.log_div posX.ne' posY.ne'];unfold Chart.jacobian
    simp only [Pi.smul_apply]
    rw [Real.log_prod (fun i _=>(fx i).1.ne'),Real.log_prod (fun i _=>(fy i).1.ne'),←sum_sub_distrib]
    apply sum_congr rfl;intro i _
    simp only [logarithm,Real.log_div (fx i).1.ne' R.scale.ne',Real.log_div (fy i).1.ne' R.scale.ne']
    ring
  rw [logs,←sum_sub_distrib,Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _=>?_ )
  calc
    _= |(logarithm P (g•X i)-polynomial P p g (X i))-(logarithm P (g•Y i)-polynomial P p g (Y i))| := by congr 1;ring
    _≤ _ := (abs_sub _ _).trans (by rw [mul_add];exact add_le_add (fx i).2 (fy i).2)

end YM.Integration.WilsonLocalHaarOrder
