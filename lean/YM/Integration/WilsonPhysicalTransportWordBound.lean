import YM.Integration.WilsonPhysicalLocalPlaquetteLoop
import YM.Next.SCHEDULE.SlotPay

/-! Derivatives of an actual based link, along its genuine exponential
physical field. The unitarity in the original path bill prevents a factor
exponential in the true forest length. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonPhysicalTransportWordBound
open Lattice Wilson RG Function Work.G07 Next.Scheduling.Wages
open WilsonPhysicalAnchoredGauge WilsonPhysicalLocalPlaquetteLoop
open scoped Classical Matrix.Norms.Frobenius ContDiff BigOperators
variable {G:Gauge} {n:Side}

private theorem weights (x:Site n) (w:Walk):
    Path.price (Path.tissue (G:=G) x w)=1 ∧ (Path.uses (Path.tissue (G:=G) x w)).length=w.length:=by
  induction w generalizing x with
  | nil=>simp [Path.tissue,Path.price,Path.uses]
  | cons d w ih=>
    obtain ⟨h,k⟩:=ih (x+d.vec)
    have a : (Path.single (G:=G) x d).size=1 ∧ (Path.single (G:=G) x d).links=[d.used x]:=by
      unfold Path.single;split <;> exact ⟨rfl,rfl⟩
    rw [Path.tissue,Path.price,a.1,h,one_mul,Path.uses,a.2]
    simp only [List.singleton_append,List.length_cons,k];exact ⟨trivial,trivial⟩

private theorem shifted (V:Config G n) (a:Directions G n) (s t:ℝ):
    increment (increment V (t•a)) (s•a)=increment V ((s+t)•a):=by
  funext i;apply G.mat_injective
  simp only [increment,G.mat_mul,Pi.smul_apply,G.mat_lieExp,map_smul,add_smul,map_add,←mul_assoc]
  congr 1
  haveI : NormedAlgebra ℚ G.Mat:=.restrictScalars ℚ ℝ _
  exact (NormedSpace.exp_add_of_commute (((Commute.refl (G.colorMat (a i))).smul_left s).smul_right t)).symm

private theorem ray {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (F:Config G n→E) (V:Config G n) (a:Directions G n) (j:ℕ) (t:ℝ):
    iteratedDeriv j (fun s:ℝ=>F (increment V (s•a))) t=leftDerivs F (List.replicate j a) (increment V (t•a)):=by
  induction j generalizing t with
  | zero=>rfl
  | succ j ih=>
    rw [iteratedDeriv_succ,funext ih,List.replicate_succ]
    change deriv (fun s:ℝ=>leftDerivs F (List.replicate j a) (increment V (s•a))) t=
      deriv (fun s:ℝ=>leftDerivs F (List.replicate j a) (increment (increment V (t•a)) (s•a))) 0
    simp_rw [shifted]
    let f:ℝ→E:=fun s=>leftDerivs F (List.replicate j a) (increment V (s•a))
    change deriv f t=deriv (fun s=>f (s+t)) 0
    rw [deriv_comp_add_const,zero_add]

theorem word (x:Site n) (w:Walk) (V:Config G n) (a:Directions G n) (H:ℝ) (pos:0≤H)
    (size:∀ i∈Path.uses (Path.tissue (G:=G) x w),‖G.colorMat (a i)‖≤H) (j:ℕ) (t:ℝ) :
    ‖iteratedDeriv j (fun s:ℝ=>G.mat (travel (increment V (s•a)) x w)) t‖≤
       ‖(1:G.Mat)‖*((w.length:ℝ)*H)^j:=by
  let p:=Path.tissue (G:=G) x w
  simp_rw [Path.picture]
  rw [ray]
  have h:=Path.bill p H pos (increment V (t•a)) (List.replicate j a) (by
    intro i hi b hb;have e:b=a:=List.eq_of_mem_replicate hb;subst b;exact size i hi)
  simpa only [p,(weights (G:=G) x w).1,(weights (G:=G) x w).2,one_mul,List.length_replicate,mul_comm H] using h

/-- The same bound for the very field that feeds the regular RG input,
uniformly in time and period, with only its true rooted link-length. -/
theorem based_link (A:Roads n) (e:Edge (Site n)) (V:Config G n) (a:Directions G n) (H:ℝ)
    (pos:0≤H) (size:∀ i∈Path.uses (Path.tissue (G:=G) A.root (WilsonPhysicalLocalPlaquetteLoop.word A e)),‖G.colorMat (a i)‖≤H)
    (j:ℕ) (t:ℝ):
    ‖iteratedDeriv j (fun s:ℝ=>G.mat (based A (increment V (s•a)) e)) t‖≤
      ‖(1:G.Mat)‖*((WilsonPhysicalLocalPlaquetteLoop.word A e).length*H)^j:=by
  simp_rw [WilsonPhysicalLocalPlaquetteLoop.read]
  exact word _ _ V a H pos size j t

end YM.Integration.WilsonPhysicalTransportWordBound
