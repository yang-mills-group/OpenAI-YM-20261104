import YM.Integration.WilsonRegisteredAffineRows
import YM.Next.RANK.LineBox

/-! The true forest interpolation is a left-increment curve with one fixed
physical direction, supported only on the moving, off-tree free links. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRegisteredAffineDirection
open Lattice Wilson Tree RG OPE.Therm Precision PertExtension
open WilsonPhysicalRegisteredForestAction WilsonReportingForestPivots
open scoped Classical
variable {G:Gauge} {c f:Side} {S:StepData c f}

private theorem exp_add (G:Gauge) (x:G.Color) (s t:ℝ) :
    G.lieExp ((s+t) • x)=G.lieExp (s • x)*G.lieExp (t • x):=by
  simpa only [add_comm t s] using Next.Rank.Spindle.together x t s

theorem located (T:Forest S.ratio) (B:Finset T.Free)
    (v:({i:T.Free|i∉moving T B}:Set T.Free)→G.El) (X:↥(moving T B)→G.Color) :
    ∃ a:Directions G f,(∀ e,‖a e‖ ≤ ‖X‖) ∧ ∀ s t:ℝ,
    let u (t:ℝ):=restored T B v (Chart.expLinks G (↥(moving T B)) (t • X))
    u (s+t)=increment (u t) (s • a) := by
  let E:=moving T B
  let a : Directions G f := fun e=>if trunk:e∈T.trunks then 0 else
    if active:(⟨e,trunk⟩:T.Free)∈E then X ⟨⟨e,trunk⟩,active⟩ else 0
  refine ⟨a,fun i=>?_,?_⟩
  · dsimp only [a];split_ifs
    · simpa only [norm_zero] using norm_nonneg X
    · exact norm_le_pi_norm X _
    · simpa only [norm_zero] using norm_nonneg X
  intro s t u
  let x (t:ℝ):=Chart.expLinks G (↥E) (t • X)
  let z (t:ℝ):=(cut T E).symm (x t*background T B v,v)
  have same (t:ℝ):u t=T.drape (z t):=rfl
  funext e
  change u (s+t) e=G.lieExp (s • a e)*u t e
  by_cases trunk:e∈T.trunks
  · simp only [a,dif_pos trunk,smul_zero,G.mat_lieExp_zero]
    rw [same,same,T.on_tree (z (s+t)) ⟨e,trunk⟩,T.on_tree (z t) ⟨e,trunk⟩,one_mul]
  let e':T.Free:=⟨e,trunk⟩
  have free (t:ℝ):u t e=z t e':=T.off_tree _ e'
  rw [free,free]
  by_cases active:e'∈E
  · let edge:↥E:=⟨e',active⟩
    have value (t:ℝ):z t e'=x t edge*background T B v edge:=
      congr_fun (congr_arg Prod.fst ((cut T E).apply_symm_apply (x t*background T B v,v))) edge
    have dir:a e=X edge:=by simp [a,trunk,active,e',edge] at *
    rw [dir,value,value]
    change G.lieExp ((s+t) • X edge)*_=G.lieExp (s • X edge)*(G.lieExp (t • X edge)*_)
    rw [exp_add,mul_assoc]
  have back (t:ℝ):z t e'=v ⟨e',active⟩:=
    congr_fun (congr_arg Prod.snd ((cut T E).apply_symm_apply (x t*background T B v,v))) ⟨e',active⟩
  have dir:a e=0:=by simp [a,trunk,active,e'] at *
  rw [dir,smul_zero,G.mat_lieExp_zero,one_mul,back,back]

end YM.Integration.WilsonRegisteredAffineDirection
end
