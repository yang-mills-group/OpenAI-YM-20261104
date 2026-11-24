import YM.OPE.Compatible.Docks.Nurse
import YM.OPE.Compatible.Docks.Sco
import YM.OPE.Compatible.Lake.Lance
/-! # Complexify the real stencil. Multiplicative near-isometries, no constant penalties at each grade crossing. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Dial
open Function Filter Module Set Finset WithLp
open scoped Topology ContDiff BigOperators Classical
variable {J I E F:Type}{h d:ℕ}{L:Filter I}{p:I→ℝ}
abbrev BR (n:ℕ):= EuclideanSpace ℝ (Fin n)
abbrev BC (n:ℕ):= EuclideanSpace ℂ (Fin n)
noncomputable abbrev mix (h:ℕ) : BR h × BR h→ BC h:=fun p=> toLp 2 (fun i=> Yolk.DuoQ (p.1 i,p.2 i))
noncomputable abbrev mates (h:ℕ): BC h→ BR h × BR h:=fun p=> (toLp 2 (fun i=> (p i).re),toLp 2 (fun i=> (p i).im))
noncomputable def zag (h:ℕ): (BR h × BR h) ≃ₗ[ℝ] BC h := {
    toFun:= mix h
    invFun:=mates h
    left_inv p:=by obtain ⟨a,b⟩:=p; ext<;>simp [Yolk.DuoQ]
    right_inv p:=by ext1 i; exact Yolk.polarZ _
    map_add' p q:=by ext1 i; exact map_add Yolk.DuoQ (p.1 i,p.2 i) (q.1 i,q.2 i)
    map_smul' a v:=by ext1 i; exact Yolk.DuoQ.map_smul a (v.1 i,v.2 i) }
lemma zig_az (x:BR h× BR h)(a:ℂ): zag h (Yolk.Az x a) = a • zag h x:=by
       ext1 i; exact Yolk.duetA a (x.1 i,x.2 i)
lemma zag_sq (x:BR h× BR h): ‖zag h x‖^2=‖x.1‖^2+‖x.2‖^2:=by
        rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,EuclideanSpace.norm_sq_eq, ← Finset.sum_add_distrib]; refine sum_congr rfl fun i _=>?_ ; change ‖Yolk.DuoQ (x.1 i,x.2 i)‖^2= _; simp [Yolk.DuoQ, Complex.sq_norm, Complex.normSq_apply,Real.norm_eq_abs,sq_abs];ring -- TC
variable (D:Fin (d+1)→ℕ)
abbrev CanA (D:Fin (d+1)→ℕ):= (i:Fin (d+1))→ BR (D i)
abbrev BoxQ (D:Fin (d+1)→ℕ):= (i:Fin (d+1))→ BC (D i)
noncomputable def Garm : (CanA D × CanA D) ≃ₗ[ℝ] BoxQ D:= {
    toFun p i:= zag _ (p.1 i,p.2 i)
    invFun p:= (fun i=>((zag _).symm (p i)).1,fun i=>((zag _).symm (p i)).2)
    left_inv p:= Prod.ext (funext fun i=> congr_arg Prod.fst ((zag _).symm_apply_apply (p.1 i,p.2 i))) (funext fun i=> congr_arg Prod.snd ((zag _).symm_apply_apply (p.1 i,p.2 i)))
    right_inv p:= funext (fun i=> (zag _).apply_symm_apply (p i))
    map_add' p q:=funext (fun i=> map_add (zag _) (p.1 i,p.2 i) (q.1 i,q.2 i))
    map_smul' a p:=funext fun i=> (zag _).map_smul a (p.1 i,p.2 i) }
lemma VintQ (x:CanA D× CanA D)(a:ℂ): Garm D (Yolk.Az x a)=a • Garm D x := funext fun i=> zig_az (x.1 i,x.2 i) a
noncomputable def εarm (x:CanA D→L[ℝ] CanA D):BoxQ D→L[ℂ] BoxQ D:= LinearMap.toContinuousLinearMap {
        toFun p:= Garm D (Yolk.doublet x ((Garm D).symm p))
        map_add' p q:=by rw [map_add,map_add,map_add]
        map_smul' a p:=by
            obtain ⟨p,rfl⟩:= (Garm D).surjective p; rw[←VintQ,LinearEquiv.symm_apply_apply,LinearEquiv.symm_apply_apply]; change Garm D _= a • _; rw [← VintQ]; apply congr_arg (Garm D); apply Prod.ext <;>(first | rfl| simp [Yolk.Az,Yolk.doublet]) }
lemma Ωp (x:CanA D→L[ℝ] CanA D)(p:CanA D×CanA D): εarm D x (Garm D p)= Garm D (Yolk.doublet x p):=by change Garm D (Yolk.doublet x ((Garm D).symm _))=_; rw[LinearEquiv.symm_apply_apply]
section
omit D
end
end YM.OPE.Dial
