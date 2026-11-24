import YM.Next.FOUNDATIONS.LinkBounds
import YM.Work.F03

/-! Each actual relative forest edge uses a common two-link logarithm after
two projections of norm at most one. All higher derivatives are purchased
before the forest, both torus sizes, the physical directions and the sites. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMarkedRelativeForestChart
open Function Filter Finset Lattice Tree RG Wilson Precision Exterior Bid Work.F03
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

variable {G:Gauge} {c f:Side} {g:Ratio c f}

def localLog (G:Gauge) (z:G.Color×G.Color):G.Color :=
  G.plog (G.mat (G.lieExp z.1*G.lieExp z.2))

theorem regular (G:Gauge):ContDiffAt ℝ ω (localLog G) 0:=by
  have exp (i:G.Color×G.Color→L[ℝ]G.Color):
      ContDiffAt ℝ ω (fun z=>G.mat (G.lieExp (i z))) 0:=(G.exp_jet.contDiffAt.comp 0 i.contDiff.contDiffAt)
  have both:ContDiffAt ℝ ω (fun z:G.Color×G.Color=>G.mat (G.lieExp z.1)*G.mat (G.lieExp z.2)) 0:=
    (exp (ContinuousLinearMap.fst ℝ _ _)).mul (exp (ContinuousLinearMap.snd ℝ _ _))
  have head:(fun z:G.Color×G.Color=>G.mat (G.lieExp z.1)*G.mat (G.lieExp z.2)) 0=1:=by simp
  have changed:localLog G=G.plog ∘ (fun z:G.Color×G.Color=>G.mat (G.lieExp z.1)*G.mat (G.lieExp z.2)):=by
    funext z;unfold localLog;rw [G.mat_mul];rfl
  rw [changed];apply ContDiffAt.comp (g:=G.plog) 0 _ both
  dsimp only at head;rw [head];exact G.plog_diff

def reading (F:Forest g) (e:Edge (Site f)) (z:ChartVars F G):G.Color:=
  G.plog (G.mat (live F z e))

def right (F:Forest g) (e:Edge (Site f)):ChartVars F G→L[ℝ]G.Color:=
  if g.parent (e.1+step e.2)=g.parent e.1 then 0 else
    (ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _=>G.Color) (g.parent e.1,coord e.2)).comp
      (ContinuousLinearMap.fst ℝ _ _)

def left (F:Forest g) (e:F.Free):ChartVars F G→L[ℝ]G.Color:=
  (ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _=>G.Color) e).comp (ContinuousLinearMap.snd ℝ _ _)

def pair (F:Forest g) (e:Edge (Site f)):ChartVars F G→L[ℝ](G.Color×G.Color):=
  if h:e∈F.trunks then 0 else (left F ⟨e,h⟩).prod (right F e)

theorem price (F:Forest g) (e:Edge (Site f)) (z:ChartVars F G): ‖pair F e z‖ ≤ ‖z‖ :=by
  by_cases tree:e∈F.trunks
  · simp [pair,tree]
  rw [pair,dif_neg tree]
  apply max_le
  · exact (norm_le_pi_norm z.2 ⟨e,tree⟩).trans (le_max_right _ _)
  · unfold right
    split
    · exact norm_zero.le.trans (norm_nonneg z)
    · exact (norm_le_pi_norm z.1 _).trans (le_max_left _ _)

theorem edge (F:Forest g) (e:Edge (Site f)):reading (G:=G) F e=localLog G ∘ pair F e:=by
  funext z
  by_cases ht:e∈F.trunks
  · have h:live F z e=1:=F.on_tree _ ⟨e,ht⟩
    simp [reading,h,pair,ht,localLog]
  · have h:live F z e=G.lieExp (z.2 ⟨e,ht⟩)*replica g (represent z.1) e:=F.off_tree _ ⟨e,ht⟩
    by_cases h₂:g.parent (e.1+step e.2)=g.parent e.1
    · simp [reading,h,replica,h₂,pair,ht,right,left,localLog]
    · simp [reading,h,replica,h₂,pair,ht,right,left,localLog,represent_link]

theorem derivative (F:Forest g) (e:Edge (Site f)) (r:ℕ) (v:Fin r→ChartVars F G) :
    ‖iteratedFDeriv ℝ r (reading F e) 0 v‖ ≤
      ‖iteratedFDeriv ℝ r (localLog G) 0‖ * ∏i:Fin r,‖v i‖ := by
  rw [edge,Next.Foundations.jets_linear _ ((regular G).of_le le_top),
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  refine ((iteratedFDeriv ℝ r (localLog G) 0).le_opNorm _).trans ?_
  exact mul_le_mul_of_nonneg_left (prod_le_prod (fun i _=>norm_nonneg _) (fun i _=>price F e (v i))) (norm_nonneg _)

theorem axis (F:Forest g) (e:Body 1 f) :
    (fun z:ChartVars F G=>(axisLog F z) e) = localLog G ∘ pair F (e.1,axisEquiv.symm e.2):=
  edge F _

theorem full (F:Forest g)(r:ℕ)(v:Fin r→ChartVars F G):
    ‖iteratedFDeriv ℝ r (axisLog (G:=G) F) 0 v‖≤
    ‖iteratedFDeriv ℝ r (localLog G) 0‖*∏i,‖v i‖:=by
  have nn:0≤‖iteratedFDeriv ℝ r (localLog G) 0‖*∏i,‖v i‖:=
    mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun i _=>norm_nonneg (v i))
  apply (pi_norm_le_iff_of_nonneg nn).2
  intro i
  let L:Bid.Dir G f→L[ℝ]G.Color:=ContinuousLinearMap.proj i
  have h:ContDiffAt ℝ ∞ (axisLog (G:=G) F) 0:=((inclusion_smooth F (G:=G)).snd).of_le le_top
  have out:=DFunLike.congr_fun (L.iteratedFDeriv_comp_left h (by exact_mod_cast le_top)) v
  have native:=derivative F (i.1,axisEquiv.symm i.2) r v
  change ‖iteratedFDeriv ℝ r (fun z:ChartVars F G=>(axisLog F z) i) 0 v‖≤_ at native
  exact (congrArg norm out).symm.le.trans native

theorem bound (F:Forest g)(r:ℕ):
    ‖iteratedFDeriv ℝ r (axisLog (G:=G) F) 0‖ ≤ ‖iteratedFDeriv ℝ r (localLog G) 0‖:=
  ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _) (full F r)

end YM.Integration.WilsonMarkedRelativeForestChart
end
