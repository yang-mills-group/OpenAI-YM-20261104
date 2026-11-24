import YM.Integration.WilsonPositionProgramCurvedAngularPrice
import YM.Comparison.RG02.Assembly.Contact

/-! All-order complex marked jets in the actual receiving forest chart, including the root's scalar. -/
noncomputable section
namespace YM.Integration.WilsonPositionProgramCurvedOccupiedPrice
open Function Filter Finset Lattice Wilson Exterior Tree Work.F03 Comparison.RG02 Comparison.RG02.Assembly
open WilsonPositionProgramAngularChart
open scoped Classical BigOperators ContDiff Topology

section
variable {B E U:Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup U] [NormedSpace ℝ U]

theorem legal (g:B→E) (hg:ContDiffAt ℝ ω g 0)(zero:g 0=0)
    (h:ℝ×E→U)(hh:ContDiffAt ℝ ω h 0):ContDiffAt ℝ ω (h ∘ chart g) 0 := by
  have inner:ContDiffAt ℝ ω (chart g) 0 := contDiffAt_fst.prodMk (hg.comp (0:ℝ×B) contDiffAt_snd)
  have atzero : chart g (0:ℝ×B)=0 := by ext <;> simp [chart,zero]
  exact ((atzero.symm ▸ hh) : ContDiffAt ℝ ω h (chart g (0:ℝ×B))).comp _ inner

theorem base (g:B→E)(hg:ContDiffAt ℝ ω g 0)(zero:g 0=0)
    (h:ℝ×E→U)(hh:ContDiffAt ℝ ω h 0)(k:ℕ):
    jet (h ∘ chart g) k (1,0)=jet h k (1,0) := by
  let iB:=ContinuousLinearMap.inl ℝ ℝ B
  let iE:=ContinuousLinearMap.inl ℝ ℝ E
  have same:(h ∘ chart g) ∘ iB = h ∘ iE := by
    funext t
    simp [iB,iE,chart,zero]
  calc
    _ = jet ((h ∘ chart g) ∘ iB) k 1 := (jet_continuous_right iB ((legal g hg zero h hh).of_le le_top) 1).symm
    _ = jet (h ∘ iE) k 1 := by rw [same]
    _ = _ := jet_continuous_right iE (hh.of_le le_top) 1

end

variable {G:Gauge} {c f:Side} {g:Ratio c f}

theorem real (F:Forest g)(h:ℝ×fieldDir G f 1→ℝ)(hh:ContDiffAt ℝ ω h 0)
    (k v:ℕ)(ε:ℝ)(he:0≤ε)(bound:∀d≤k,∀x,|jet h d (1,x)| ≤ ε*(1+‖x‖)^v)(b:ChartVars F G):
    |jet (h ∘ chart (axisLog F)) k (1,b)| ≤
      (2*WilsonPositionProgramCurvedAngularPrice.price G k v+1)*(ε*(1+‖b‖)^(k*v)) := by
  have pair d (hd:d≤k) (x y:fieldDir G f 1) :
      |jet h d (1,x)-jet h d (1,y)| ≤ (2*ε)*(1+max ‖x‖ ‖y‖)^v := by
    have hx := (bound d hd x).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (show 1+‖x‖ ≤ 1+max ‖x‖ ‖y‖ by linarith [le_max_left ‖x‖ ‖y‖]) v) he)
    have hy := (bound d hd y).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (show 1+‖y‖ ≤ 1+max ‖x‖ ‖y‖ by linarith [le_max_right ‖x‖ ‖y‖]) v) he)
    exact (abs_sub _ _).trans (by linarith)
  have hg : ContDiffAt ℝ ω (axisLog (G:=G) F) 0 := (Work.F03.inclusion_smooth F).snd
  have zero : (axisLog (G:=G) F) 0=0 := congrArg Prod.snd (Work.F03.inclusion_zero F)
  have price:=WilsonPositionProgramCurvedAngularPrice.original F h k v (2*ε) (by positivity) pair b 0
  rw [← WilsonPositionProgramAngularChart.centered _ hg zero h hh k b 0,base _ hg zero h hh,
    norm_zero,max_eq_left (norm_nonneg _)] at price
  have atzero:=bound k le_rfl 0
  simp only [norm_zero,add_zero,one_pow,mul_one] at atzero
  have one : 1 ≤ (1+‖b‖)^(k*v) := one_le_pow₀ (by linarith [norm_nonneg b])
  have mass:= mul_le_mul_of_nonneg_left one he
  calc
    _ ≤ |jet (h ∘ chart (axisLog F)) k (1,b)-jet h k (1,0)| + |jet h k (1,0)| := by
      simpa only [sub_add_cancel] using abs_add_le (jet (h ∘ chart (axisLog F)) k (1,b)-jet h k (1,0)) (jet h k (1,0))
    _ ≤ _ := by nlinarith only [price,atzero,mass]

theorem original (F:Forest g)(h:ℝ×fieldDir G f 1→ℂ)(hh:ContDiffAt ℝ ω h 0)
    (k v:ℕ)(ε:ℝ)(he:0≤ε)(bound:∀d≤k,∀x,‖jet h d (1,x)‖ ≤ ε*(1+‖x‖)^v)(b:ChartVars F G):
    ‖jet (h ∘ chart (axisLog F)) k (1,b)‖ ≤
      2*(2*WilsonPositionProgramCurvedAngularPrice.price G k v+1)*(ε*(1+‖b‖)^(k*v)) := by
  have hg : ContDiffAt ℝ ω (axisLog (G:=G) F) 0 := (Work.F03.inclusion_smooth F).snd
  have zero : (axisLog (G:=G) F) 0=0 := congrArg Prod.snd (Work.F03.inclusion_zero F)
  have projected (L:ℂ→L[ℝ]ℝ)(contract:∀z,|L z| ≤ ‖z‖) :
      |L (jet (h ∘ chart (axisLog F)) k (1,b))| ≤
      (2*WilsonPositionProgramCurvedAngularPrice.price G k v+1)*(ε*(1+‖b‖)^(k*v)) := by
    rw [jet_apply_left L _ k ((legal _ hg zero h hh).of_le le_top)]
    apply real F (L ∘ h) (L.contDiff.comp_contDiffAt 0 hh) k v ε he _ b
    intro d hd x
    rw [← jet_apply_left L h d (hh.of_le le_top)]
    exact (contract _).trans (bound d hd x)
  have re:=projected Complex.reCLM Complex.abs_re_le_norm
  have im:=projected Complex.imCLM Complex.abs_im_le_norm
  exact (Complex.norm_le_abs_re_add_abs_im _).trans ((add_le_add re im).trans_eq (by ring))

end YM.Integration.WilsonPositionProgramCurvedOccupiedPrice
end
