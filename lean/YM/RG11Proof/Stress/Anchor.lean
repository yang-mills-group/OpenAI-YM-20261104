import YM.RG11Proof.Stress.Normalized
import YM.Pert.Scale.Return

/-! # Existence/cost of the leading separated Ward tests

Witness at any A (maxwell leading at release Frames, γ-stress sign pinned
to Pert scheme `freeStress`). Future orders must still be identified and the
STRESS Ward data shown, incl vacuum/improvement rule. This file rules out a
spurious lack of existence at the free chosen sign; ensures even before any
interacting/actual identification that two tests disambiguate that sign on
the full candidate space. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.RG11.Stress
open PowerSeries YM.RG11.Fields YM.RG11.Jets YM.RG11.Nodes
open scoped Topology Classical ContDiff BigOperators
open Maxwell Labels Table Work.A01 Next.UVStress UVNext.FreeStress Function Filter Set MeasureTheory Pert.Position Pert.Scale Analysis
variable {G : Gauge}{F:Frames G}(B:Adapted F 4)

private def RJ :Rect Taps B.toBasis.J ℝ := Matrix.of fun i=>B.toBasis.coord (Pert.freeStress F i.1 i.2)
def freeMark : psStress B.toBasis := (RJ B).map PowerSeries.C

private theorem signJ : Pert.freeStress F=torch F (-1):=by rw [Pert.freeStress,←Pert.common_stress, torch,one_smul,torch,neg_smul,one_smul]
private theorem realJ : Pert.freeStress F∈ KernelSpace (Free.spin_free F):=signJ.symm ▸ lit_in F _ _
private theorem unfolds (a:Taps): B.toBasis.put (RJ B a)=Pert.freeStress F a.1 a.2:=
   B.toBasis.put_round _ ((sym_mem.mp (kernel_mem.mp realJ).1).2.1 ..)

-- Adapted version of `Pert.Scale.rare` which was for recorded corners.
 theorem rays (A:Adapted F 4)(i:A.toBasis.J)(t:ℝ): gear F 4 t (A.b i)=(t:ℂ)^(Fields.height A i) • A.b i :=by
    change _ = (t:ℂ)^((A.w i).1) • A.b i
    rw [←Pert.RawLabels.physical_round F (A.b i),gear_inherit,
       grow_weights (w:=(A.w i).1) (p:=Pert.RawLabels.physicalLabel F _ _) (fun v hv=> ?_) t,map_smul]
    exact congrArg Prod.fst ((Labels.weight_slot v).symm.trans ((Labels.pure_grade _ _|>.mp (basis_label A i)) hv))

 theorem at_grade (a:Taps)(j:B.toBasis.J)(hj:Fields.height B j ≠ 4): RJ B a j=0:=by
    let L:=gear F 4 2
    let S:=Pert.freeStress F a.1 a.2
    have he:(∑ i:B.toBasis.J, B.b.equivFun S i • L (B.b i)) = (2:ℂ)^4 • S:=by
        simp_rw [←_root_.map_smul L,← _root_.map_sum L,B.b.sum_equivFun]; simpa [L,S] using gear_stress F 2 a.1 a.2
    have hx:= congrArg (fun z=> B.b.equivFun z j) he
    simp_rw [map_sum,map_smul,Finset.sum_apply] at hx
    unfold L at hx
    simp_rw [rays, map_smul, Pi.smul_apply, Module.Basis.equivFun_self, smul_eq_mul] at hx
    classical
    simp only [mul_ite,mul_one,mul_zero, Complex.ofReal_ofNat, Finset.sum_ite_eq', Finset.mem_univ, if_true] at hx
    suffices B.b.equivFun S j=0 by change (B.b.equivFun S j).re=0; rw [this]; rfl
    have hv:(2:ℂ)^(Fields.height B j)≠ (2:ℂ)^4:= by
       intro hu; apply hj; apply StrictMono.injective (pow_right_strictMono₀ (by norm_num:1<(2:ℝ))); simpa only [← Complex.ofReal_ofNat,←Complex.ofReal_pow,Complex.ofReal_inj] using hu
    symm at hx
    rw [mul_comm ((2:ℂ)^4)] at hx
    apply Classical.not_not.mp
    intro HT; exact hv ((mul_left_cancel₀ HT hx).symm)


 theorem entry4 (k:ℕ):piece k (freeMark B)∈candidate B:=by
    have he:piece k (freeMark B)= if k=0 then RJ B else 0:= Matrix.ext fun i j=>by
        by_cases h:k=0 <;> simp only [piece_apply,freeMark,Matrix.map_apply,coeff_C,h, Matrix.zero_apply, ↓reduceIte]
    rw [he]; split
    · have H:disclose B (RJ B)=Pert.freeStress F:=funext fun _=>funext fun _=> unfolds B _
      refine ⟨H ▸ (kernel_mem.mp realJ).1,fun i j h=> at_grade B i j h⟩
    exact Submodule.zero_mem _

private theorem lighted (n:ℕ)(u:Axis→(clean (n+1)→ₗ[ℂ] ℂ))(A:ShapeReport G F)(v:Fin n→ B.toBasis.J):
    constantCoeff (relays (shine _ (freeMark B)) (queryHeads A _ u) v)=
      ∑ a,leaves A (u a) (Pert.freeStress F a 0) (B.b ∘ v):=by
   unfold relays armed shine freeMark queryHeads
   simp only [map_sum,map_mul,Matrix.map_apply, ← coeff_zero_eq_constantCoeff_apply ,deposited,coeff_C,↓reduceIte]
   have he(t:Taps): (∑ j:B.toBasis.J,(RJ B t j:ℂ)*constantCoeff (survey A B.toBasis (shellers u t) (Fin.cons j v)))=
       leaves A (shellers u t) (Pert.freeStress F t.1 t.2) (B.b ∘ v):=(extends_arm A B _ (RJ B t) v).trans (by rw [unfolds])
   -- restore constantCoeff
   simp only [coeff_zero_eq_constantCoeff_apply];
   simp_rw [he]
   change (∑ t:Axis × Axis,_)=_
   rw [Fintype.sum_prod_type]; apply Finset.sum_congr rfl; intro i _
   rw [Finset.sum_eq_single_of_mem (0:Axis) (by simp) (fun j _ hj=> ?_),shellers,if_pos rfl]
   rw [shellers,if_neg hj,leaves_eq,hears_site,LinearMap.zero_apply]

 theorem leads (hG:G.Simple)(A:ShapeReport G F){χ:E4→ℝ}(h:Window (camera 0) χ):Signals A B.toBasis (freeMark B) 0 h:=by
   constructor
   all_goals
     refine ⟨fun v j hj=>?_⟩
     obtain rfl:j=0:=Nat.eq_zero_of_le_zero hj
     rw [coeff_zero_eq_constantCoeff_apply,coeff_zero_eq_constantCoeff_apply,lighted, survey_zero4]
   · simp only [leaves_eq,hears_site,direct,on_at]
     let W:=Free.scheme F
     let z:= fourWord F (B.b ∘ v)
     have he (b : Axis): ∑ i:Axis,W.deriv 4 i (Pert.freeStress F i b)=0:=by rw [signJ]; exact (law F (Free.spin_free F) hG W (Free.scheme_derives F) (Free.phase_orientation F) (-1)).divergence _
     have hu(i:Axis):site F (Fin.cons (α:=fun _:Fin 2=>E F 4) (Pert.freeStress F i 0) (B.b ∘ v))=fun x=> (freeTable F).useAt (freeTable F) x (Fin.cons ⟨4,Pert.freeStress F i 0⟩ z):=funext fun x=>by simp_rw [site_desc,word_succ]; rfl
     change _ = (0:ℂ)
     simp_rw [hu,←(Free.scheme_derives F).kernels (x:=camera 0) _ _ _ (shutter 0),←front_eval,←map_sum]
     change frontRead _ _ _ (∑ x,W.deriv _ x _)=_; rw [he,map_zero]
   simp only [leaves_eq,hears_site,traded,run_at,on_at]
   simp_rw [site_desc,word_succ]
   let t:=B.b ∘ v
   let w:=Fin.tail t
   have hx:t=Fin.cons (t 0) w:=(Fin.cons_self_tail t).symm
   -- use test gradient derivative interface on RHS
   let W:=Free.scheme F
   have heq : StressLaws (freeTable F) (Pert.freeStress F) W.deriv ((-(-1:ℝ)) • (Free.gear F).lie):=by
     -- inspect actual type
     unfold Pert.freeStress
     have hv:=Free.beacon_signal F (-1)
     rw [show ((-1:ℝ) • Free.original F)= - Free.original F by simp,neg_neg, one_smul,one_smul] at hv; rw [neg_neg,one_smul]; exact hv
   change _ = Points.gradient _ _ (site F t) _
   have H:= heq.translation (shutter 0) (fourWord F w) h 0 4 (t 0)
   rw [(Free.scheme_derives F).kernels _ _ _ (shutter 0)] at H
   rw [Finset.sum_neg_distrib]
   have hv : fourWord F t=Fin.cons (Sigma.mk 4 (t 0)) (fourWord F w):= (congrArg (fourWord F) hx).trans (word_succ ..)
   change -(∑ a:Axis,∫ y:E4,((D (basis a) χ y:ℝ):ℂ)* (freeTable F).useAt _ _ (Fin.cons _ (fourWord F t))) = Points.gradient (n:=2) 0 0 (fun y=>(freeTable F).useAt _ y (fourWord F t)) _
   simp only [hv]; exact H
end YM.RG11.Stress
