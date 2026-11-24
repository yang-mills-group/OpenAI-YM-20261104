import YM.OPE.Compatible.Glim.Camp
import YM.OPE.Compatible.Jess.Grab
/-! # Taylor derivatives at field, through ξ² -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Variance
open Function Filter Set MeasureTheory Lattice Wilson RG Precision Metric Matrix Cascade Finset
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{P:ChartRatio G}
attribute [local instance] Gauge.frobInner
open Next.SectorChange Stationary
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc
variable {E F I:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
noncomputable def Pry (v:E)(p:E→Token)(x:E) : Token:=⟨fderiv ℝ (fun y=> (p y).s) x v,fderiv ℝ (fun y=> (p y).l) x v,fderiv ℝ (fun y=> (p y).h) x v⟩
lemma pryB (v:E)(p:ScriptJ E)(h:p.B): ScriptJ.B (Pry v p):=by intro i; match i with | 0=>exact Bond.amount v (h 0)
                                                                                       | 1=>exact Bond.amount v (h 1)
                                                                                       | 2=>exact Bond.amount v (h 2)
                                                                                       | i+3=>exact Bond.keep _ 
omit [FiniteDimensional ℝ E] in lemma pryC (v:E)(p:Token):Pry v (fun _=>p)=0:= by funext x; unfold Pry; rw [fderiv_const_apply,fderiv_const_apply,fderiv_const_apply]; rfl
lemma pryAdd (v:E)(p q:ScriptJ E)(hp:p.B)(hq:q.B): Pry v (p+q)=Pry v p+Pry v q:=by
    funext i; have ha (j:Char.Phase): DifferentiableAt ℝ (fun y=>(p y).seq j.val) i:= (hp j).smooth.differentiable (by simp) i; have hb (j:Char.Phase): DifferentiableAt ℝ (fun y=>(q y).seq j.val) i:= (hq j).smooth.differentiable (by simp) i; have hj(p q:E→ℝ)(hp:DifferentiableAt ℝ p i)(hq:DifferentiableAt ℝ q i): fderiv ℝ (fun i=>p i+q i) i v=fderiv ℝ p i v+fderiv ℝ q i v:= DFunLike.congr_fun (fderiv_fun_add hp hq) _
    apply eta <;> simp only [Pry,Pi.add_apply,JetS.pl_s,JetS.pl_l,JetS.pl_h]
    · exact hj _ _ (ha 0) (hb 0)
    · exact hj _ _ (ha 1) (hb 1)
    exact hj _ _ (ha 2) (hb 2)
lemma pryMul (v:E)(p q:ScriptJ E)(hp:p.B)(hq:q.B): Pry v (p*q)=p*Pry v q+Pry v p*q:=by
    funext i; have hA (j:Char.Phase): DifferentiableAt ℝ (fun y=>(p y).seq j.val) i:= (hp j).smooth.differentiable (by simp) i; have hB (j:Char.Phase): DifferentiableAt ℝ (fun y=>(q y).seq j.val) i:= (hq j).smooth.differentiable (by simp) i
    have ha:DifferentiableAt ℝ (fun y=>(p y).s) i:=hA 0; have hb:DifferentiableAt ℝ (fun y=>(p y).l) i:=hA 1; have hc:DifferentiableAt ℝ (fun y=>(p y).h) i:=hA 2; have hx:DifferentiableAt ℝ (fun y=>(q y).s) i:=hB 0; have hy:DifferentiableAt ℝ (fun y=>(q y).l) i:=hB 1; have hz:DifferentiableAt ℝ (fun y=>(q y).h) i:=hB 2
    have hh(p q:E→ℝ)(hp:DifferentiableAt ℝ p i)(hq:DifferentiableAt ℝ q i):fderiv ℝ (fun y=> p y*q y) i v=p i*fderiv ℝ q i v+ q i*fderiv ℝ p i v:=by rw [fderiv_fun_mul hp hq];rfl
    have hH(p q:E→ℝ)(hp:DifferentiableAt ℝ p i)(hq:DifferentiableAt ℝ q i): fderiv ℝ (fun y=>p y+q y) i v=fderiv ℝ p i v+fderiv ℝ q i v:= DFunLike.congr_fun (fderiv_fun_add hp hq) _
    apply eta<;>simp only [Pry,Pi.mul_apply,Pi.add_apply,JetS.ml_s,JetS.ml_l,JetS.ml_h,JetS.pl_s,JetS.pl_l,JetS.pl_h]
    · rw [hh _ _ ha hx];ring
    · erw [hH _ _ (ha.mul hy) (hb.mul hx),hh _ _ ha hy,hh _ _ hb hx];ring
    erw [hH _ _ ((ha.mul hz).add (hb.mul hy)) (hc.mul hx),hH _ _ (ha.mul hz) (hb.mul hy),hh _ _ ha hz,hh _ _ hb hy,hh _ _ hc hx];ring
lemma tallJ (k:ℕ)(p:E→ℝ): ScriptJ.B (Pawn.mold p k):=by
     have ht(m): Bond (jet p m):= (Bond.keep _).mul (Bond.multiline (iteratedFDeriv ℝ m p 0) (fun _ : Fin m=>id) (fun _ ℓ=> Bond.glyph ℓ)); intro i; match i with|0=>exact ht k|1=>exact ht (k+1)|2=>exact ht (k+2)|j+3=>exact Bond.keep _
noncomputable abbrev bat (v:E)(p:E→ℝ):E→ℝ:= fun y=>fderiv ℝ p y v
omit [FiniteDimensional ℝ E]

lemma vast (p:E→ℝ)(k:ℕ)(h:ContDiffAt ℝ ω p 0)(v x:E): fderiv ℝ (jet p (k+1)) x v=jet (bat v p) k x:= Tensor.slot_lower (h.of_le le_top) v x
lemma pry_mold (p:E→ℝ)(k:ℕ)(h:ContDiffAt ℝ ω p 0)(v:E): Pry v (Pawn.mold p (k+1))= Pawn.mold (bat v p) k:= by funext x; exact eta _ _ (vast _ _ h v x) (vast _ (k+1) h v x) (vast _ (k+2) h v x)
noncomputable abbrev Un (E:Type):ScriptJ E:= fun _=> ⟨0,1,0⟩ -- may namespace F.Mesh req Norm etc
lemma pry_m0 (p:E→ℝ)(h:ContDiffAt ℝ ω p 0)(v:E): Pry v (Pawn.mold p 0)= Un E* Pawn.mold (bat v p) 0:= by
     funext x; apply eta
     · change fderiv ℝ (jet p 0) x v=_; rw [show jet p 0=(fun _=> p 0) from funext fun i=>jet_zero .., fderiv_const_apply]; change 0= (0:ℝ)* _;rw[zero_mul]
     · change fderiv ℝ (jet p _) x v=0*_+1*_; rw [vast p 0 h,zero_mul,one_mul,zero_add]
     change fderiv ℝ (jet p _) x v=0*_+1*_+0*_; erw [vast p 1 h,zero_mul,one_mul,zero_add,zero_mul,add_zero]
lemma picked (p:E→ℝ)(h:ContDiffAt ℝ ω p 0)(v:E): ContDiffAt ℝ ω (bat v p) 0:= (h.fderiv_right (m:=ω) (by simp)).clm_apply (g:=fun _=>v) contDiffAt_const
end YM.OPE.Variance
