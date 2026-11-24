import YM.Integration.WilsonPhysicalChiralNonfreeCartanColor

/-! Numerical sign on the actual nominal Cartan color orientation. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPhysicalChiralNonfreeCartanOrientation
open Finset RG Labels Lattice Maxwell Maxwell.Free XSpace XSpace.Chiral
open WilsonPhysicalChiralNonfreeCurvatureTest WilsonPhysicalChiralNonfreeCartanColor
open WilsonPositionThermometerGradedSource Next.Rank.Price Next.Rank.Atlas Further.CorrectedLift
open Tensor Analysis
open scoped Classical BigOperators Topology InnerProductSpace
variable {G:Gauge}

def signCode (i j k:Fin 3):ℤ:=
  if i+1=j ∧ j+1=k then 1 else if j+1=i ∧ i+1=k then -1 else 0

theorem signTable (i j k:Fin 3):liftedSign i j k=(signCode i j k:ℝ):=by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> rfl

def form (a b c:G.Color):ℝ:=⟪a,G.ad b c⟫_ℝ

theorem turn (a b c:G.Color):form a b c=form b c a:=by
  unfold form
  rw [show ∀ A B:G.Color,inner ℝ A B=inner ℝ B A from fun a b=>real_inner_comm b a,
    skew_ad b,inner_neg_left,Gauge.ad_skew,neg_neg]

theorem exchange (a b c:G.Color):form a b c= -form a c b:=by
  unfold form; rw [skew_ad b,inner_neg_right]

theorem sumTable (c:Fin 3→G.Color):
    (∑i:Fin 3,∑j:Fin 3,∑k:Fin 3,liftedSign i j k * form (c i) (c j) (c k))=
      6 * form (c 0) (c 1) (c 2):=by
  simp only [Fin.sum_univ_three,signTable]
  have p1:(1:Fin 3)+1=2:=rfl
  have p2:(2:Fin 3)+1=0:=rfl
  have h01:(0:Fin 3)≠1:=by decide
  have h02:(0:Fin 3)≠2:=by decide
  have h12:(1:Fin 3)≠2:=by decide
  norm_num [signCode,p1,p2,h01,h02,h12,h01.symm,h02.symm,h12.symm]
  linarith [turn (c 0) (c 1) (c 2),turn (c 1) (c 2) (c 0),
    exchange (c 0) (c 1) (c 2),exchange (c 1) (c 2) (c 0),exchange (c 2) (c 0) (c 1)]

theorem surveyed (T:Maxwell.TaylorTower G):
    Maxwell.probe T (base G 0).val=(Rose.f:ℂ)^3 *
    ↑(6 * form (vₜ 0 T) (vₜ 1 T) (vₜ 2 T)):=by
  change Maxwell.probe T (((Rose.f:ℂ)^3) • Chiral.B G)=_
  rw [map_smul,smul_eq_mul,fuelled,←sumTable (fun i=>vₜ i T)]
  push_cast; rfl

theorem deleted (c:Fin 3→G.Color)(S:Finset (Fin 3))(T:Maxwell.TaylorTower G)
    (held:(fun n=>gaugeJet (T n))=PositionX.Tri.chunk (chart (fun j=>direction j (c j)) S)):
    Maxwell.probe T (base G 0).val=if S=univ then
      (Rose.f:ℂ)^3*↑(6*form (c 0) (c 1) (c 2)) else 0:=by
  rw [surveyed]; simp_rw [shots c S T held]
  by_cases h0:(0:Fin 3)∈S <;> by_cases h1:(1:Fin 3)∈S <;> by_cases h2:(2:Fin 3)∈S
  · have h:S=univ:=eq_univ_of_forall fun i=>by fin_cases i <;> assumption
    simp [h]
  all_goals
    have h:S≠univ:=by intro e; subst S; simp_all
    simp [h,h0,h1,h2,form]

theorem nominated (C:Family G)(s:Rose.Badge)(upper:(0:Fin 3)∈s)(c:Fin 3→G.Color):
    reading (C.labels.level 6) (fun j=>direction j (c j)) (ladder C 6 (source C s 0))=
       (Rose.f:ℂ)^3*↑(6*form (c 0) (c 1) (c 2)):=by
  obtain ⟨T,sites,forms⟩:=WilsonPhysicalChiralNonfreeCartanPolarization.named C s 0 upper (fun j=>direction j (c j))
  refine forms.trans ?_
  simp_rw [fun S=>deleted c S (T S) (sites S)]
  simp

theorem positive (simple:G.Simple)(C:Family G):∃c:Fin 3→G.Color,∀s:Rose.Badge,(0:Fin 3)∈s →
    0<(reading (C.labels.level 6) (fun j=>direction j (c j)) (ladder C 6 (source C s 0))).re:=by
  obtain ⟨x,y,ne⟩:=simple.nonabelian
  let c:Fin 3→G.Color:=![G.ad x y,x,y]
  have h:0<form (c 0) (c 1) (c 2):=real_inner_self_pos.mpr ne
  refine ⟨c,fun s hs=>?_⟩
  rw [nominated C s hs,←Complex.ofReal_pow,←Complex.ofReal_mul,Complex.ofReal_re]
  exact mul_pos (pow_pos (inv_pos.mpr (Real.sqrt_pos.mpr (by norm_num))) _) (mul_pos (by norm_num) h)

end YM.Integration.WilsonPhysicalChiralNonfreeCartanOrientation
