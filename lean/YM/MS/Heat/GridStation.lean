import YM.MS.Heat.Build
/-!
# Place read at conservation. `reflections` elsewhere.

Result used exact at origin and each time point. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Heat
open Function Filter Set Finset Plane Koszul Flux MeasureTheory Book Convolve Base Signal
variable {P I A : Type} {E:Type*}[MeasurableSpace P][AddCommGroup P][Fintype A]
   {p: Sector A} {F H:T (Row A P ℂ)} {K L : Flux A P ℂ}{Q: Charge p P ℂ} {l:Legs (Mode A P)} {k:ℕ}
-- generic commute when reading PM unity
omit [MeasurableSpace P] in
lemma plan_comm (K:Flux A P ℂ) (h:∀ i j, tree p K (F i) (H j) l=tree p K (H j) (F i) l) : promote (point l) (pairW (boulevard p K) F H)=promote (point l) (pairW (boulevard p K) H F):= by
   funext n; simp only [promised,paired, point,LinearMap.proj_apply,Finset.sum_apply,blvd]; simp_rw [h]; rw [← Finset.Nat.sum_antidiagonal_swap]; rfl
variable (μ:Measure P)
local notation "R" => rack K L Q μ
lemma point_mat [SigmaFinite μ](h:Pieces K L Q μ F F)(hw:net l=0):
    (promote (point l) (promote (R).J ((R).grow F) + promote (R).L F + (2:ℂ)⁻¹ • (pairW (R).D F F+pairW (R).C F ((R).grow F)+pairW (R).C ((R).grow F) F)))=(promote (point l) ((R).lives F ((R).matCont F))):= by
   apply GridR.bright_mat (elementary μ h (point l)); swap
   · refine plan_comm L (p:=p) ?_; intro i j; refine axis_comm h.cl (h.vital _) ?_ hw; exact Pure.sum (antidiagonal j) (fun k _=> tree_pure h.ck (h.vital k.1) (h.vital k.2)) -- defeq PairW
   all_goals refine plan_comm K (p:=p) (fun i j=> (axis_even h.ck (h.vital i) hw).symm)
lemma point_sole [SigmaFinite μ](h:Pieces K L Q μ F H):
   (R).res F ((R).lives F H) + promote (R).L H + pairW (R).D F H + pairW (R).C ((R).grow F) H = (R).lives F ((R).res F H) + pairW (R).X ((R).matCont F) H := (elementary μ h (LinearMap.id)).lights
end YM.MS.Heat
