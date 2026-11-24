import YM.Pert.First.Season
/-! Jointly realize all remaining linear curvature letters at the first order with their own private variables, before large-mesh limits. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Pert.First
open Filter MeasureTheory ProbabilityTheory Lattice Function Full Orb Warp
open scoped Topology Classical
variable {G : Gauge} {N : Side} {d r : ℕ} {I : Type} [Fintype I] [DecidableEq I]
variable (h : ℝ) (o : Grid N r) (tag : I→Fin r) (code : I→CosKey G d) (s : Finset I)
local notation "fmark" => root tag code
local notation "finit" => tube o h (fun _=>d) ∘ fmark
def chandelier (P : Coords G N→ℂ) := ∫ z, P z.fst * (∏ a∈s,node h o (tag a) (code a) z) ∂hall G N r d h
lemma evaluation (i : Fin r) (x : Coords G N) : finit s x i = ∫ u : Aux G d, ∏ a∈s with tag a=i, node h o i (code a) (x,fun _=>u) ∂auxLaw G d h := by
  exact post_zero h o tag code s i x
lemma chandelier_eq (P : Coords G N→ℂ) (hP : Tame P) : chandelier h o tag code s P = ∫ x,P x * line Finset.univ o h (fun _=>d) (fmark s) x ∂data G N := by
  letI := isLaw (G:=G) (n:=N)
  letI := auxGaussian (G:=G) (d:=d) h
  letI := hall_G G N r d h
  let M := hall G N r d h
  let v (i : I) := node h o (tag i) (code i)
  let A := Coords G N
  let Z := A × (Fin r→Aux G d)
  have he : Tame (P ∘ (Prod.fst : Z→A)) := by
    obtain ⟨C,hC,k,hc⟩ := hP.2
    refine ⟨hP.1.comp continuous_fst,C,hC,k,fun x=>?_⟩
    change ‖P _‖ ≤ _; grw [hc]
    gcongr; exact le_max_left ..
  have hv := integral_prod (μ:=data G N) (ν:=Measure.pi (fun _ : Fin r=>auxLaw G d h)) (f:=fun z => P z.fst * ∏ i∈s,v i z) (price_tame M (Tame.mul he (prod_tame (fun i _=>Orb.Tame.clm (v i)))))
  apply hv.trans
  congr 1; funext x
  dsimp only [Prod.fst]; rw [integral_const_mul]; congr 1
  unfold line;
  let F (i : Fin r) (u) := ∏ a∈s with tag a=i, v a (x,fun _=>u)
  have hx (i) :  tube o h (fun _=>d) (fmark s) x i = ∫ u, F i u ∂auxLaw G d h := (evaluation _ _ _ _ _ i x).trans (congrArg (fun f : Aux G d →ℂ=>∫ u,f u ∂auxLaw G d h) (funext (fun u => Finset.prod_congr rfl (fun a ha=> by rw [show v a _ = (node h o (tag a) (code a)) _ from rfl, (Finset.mem_filter.mp ha).2])))) -- rw earlier unnecessary
  have hi := integral_fintype_prod_eq_prod (μ:=fun _=>auxLaw G d h) F
  simp_rw [hx]; rw [← hi]
  exact congrArg (fun f : (Fin r→Aux G d)→ℂ=>∫ u,f u ∂Measure.pi (fun _ : Fin r=>auxLaw G d h)) (funext (fun u=>(by
    unfold F v; exact (joint_prod h o tag code s (x,u)).symm.trans (Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl (fun a ha=> by dsimp only [Prod.fst,Prod.snd]; rw [(Finset.mem_filter.mp ha).2]))
    /-refine Finset.prod_congr rfl fun i _=> Finset.prod_congr rfl fun a ha=>?_ ;simp only [v,(Finset.mem_filter.mp ha).2] -/)))
def totalize := chandelier h o tag code s cubic + ∑ i∈s,chandelier h o tag code (s.erase i) (fun x=>linkChange h o tag code x i)
lemma guests_first (hg : G.Simple) : first (amplitude (fun _=>d) h Finset.univ o (fmark s))=totalize h o tag code s := by
  rw [first_amplitude _ _ _ _ _ hg,exposed,season_applies,totalize,chandelier_eq _ _ _ _ _ _ cubic_tame]
  exact congrArg _ (Finset.sum_congr rfl fun i _=> (chandelier_eq _ _ _ _ _ _ (brush_tame ..)).symm)
end YM.Pert.First
