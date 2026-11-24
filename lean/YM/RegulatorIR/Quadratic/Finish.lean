import YM.RegulatorIR.Primitives.Faber
import YM.RegulatorIR.Quadratic.Moon

/-!
# At finite terminal side — remove conditioning
Effective K for Horizon. Use all Wick legs ambient orbit. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.StopB
open Function Budget Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Set Filter Binding Diagram.Formal PertExtension Series Series.Radial Series.Tested MeasureTheory MvPolynomial Cluster Diagram Quadratic Lattice Wilson Geometry Geometry.Field Chart Gauge RG Orb Laplace Tree Forest Step Matrix Prim Binding.Last GaussianScore
open scoped Topology ENNReal BigOperators Classical PowerSeries ContDiff Matrix.Norms.Frobenius Matrix
variable {I J X:Type}{G:Gauge}{f:Side}
section Stiff
variable [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
variable {c:ℝ}{a:I→Prop}{K N: Matrix I I ℝ}{Q: Matrix J I ℝ}{D:Matrix I J ℝ}{L:Matrix J J ℝ}
variable (W:GridQ c a K L Q D N)
include W
lemma elder (u v:J→ℝ): u ⬝ᵥ (L*ᵥ v)=v ⬝ᵥ (L*ᵥ u):=by
 have he (x y:J→ℝ): x ⬝ᵥ (L*ᵥ y)= c*(x ⬝ᵥ y) -(D*ᵥ y) ⬝ᵥ (diagStiff c K Q*ᵥ (D*ᵥ x)):=by rw [W.eye (W.clipped y),← W.stiff, smul_mulVec,sub_mulVec,one_mulVec,← mulVec_mulVec,dotProduct_smul,dotProduct_sub,smul_eq_mul,mul_sub]
 rw [he u,he v,dotProduct_comm u v];apply congr_arg; rw (occs:=.pos [1])[← W.style]; rw [dotProduct_transpose_mulVec]
lemma elder_t : L.transpose=L:=by ext i j; have he:=elder W (Pi.single j 1) (Pi.single i 1); rw [dotProduct_comm (Pi.single j 1), dotProduct_comm (Pi.single i 1), dotProduct_single_one,dotProduct_single_one] at he; exact (dotProduct_single_one (L j) i).symm.trans (he.trans (dotProduct_single_one ..))
end Stiff

section Marks

def tipFlow (G:Gauge)(f:Side) : Micro (Book G f):= fun _ x=> ∑ i:Cotree f,entry G ((paper G f).symm x i.val)
def scribe (G : Gauge)(f: Side) : Run (tipFlow G f):= {
 J:=Book G f,fin:=inferInstance, inc:= Function.Embedding.refl _, script:=(fun p=> tipFlow G f p.1 p.2), smooth:=by
    apply ContDiffAt.sum; intro i _
    let L: ℝ × (Book G f→ℝ)→ₗ[ℝ] G.Color := (LinearMap.proj i.val).comp ((paper G f).symm.toLinearMap.comp (LinearMap.snd ..)); exact (show ContDiffAt ℝ ∞ (entry G) (L 0) from (map_zero L).symm ▸ ent_smooth G).comp (f:=L) _ L.toContinuousLinearMap.contDiff.contDiffAt,
 reaches:=fun _ _=>rfl }

def charter (G:Gauge)(f:Side) : Orders (Book G f):= ((scribe G f).issues 1 0).choose
lemma little : Lab 0 1 (tipFlow G f) (charter G f):= ((scribe G f).issues 1 0).choose_spec

def spine (G:Gauge)(f:Side) : Meadow G (Cotree f)→ₗ[ℝ](Book G f→ℝ):= (paper G f).toLinearMap.comp inhabit
def pupil (x:Book G f) : Module.Dual ℝ (Meadow G (Cotree f)):= wing (spine G f) x
lemma spurs (x : Meadow G (Cotree f)) : flank (tipFlow G f) (spine G f x)= psyche (Cotree f) G x:=by
 ext t; change (∑ i:Cotree f,entry G ((paper G f).symm (t • paper G f (inhabit x)) i.val))= ∑ i:Cotree f,entry G (t • x i)
 rw [map_smul,LinearEquiv.symm_apply_apply]; apply Finset.sum_congr rfl; intro i _; apply congr_arg
 change t • genJet x i.val=t • x i; simp [genJet,i.property]
lemma silence (w: Meadow G Empty)(i:Book G f) : announce 0 (dilute Function.Embedding.ofIsEmpty ((hover G).color w)) i=0:=by simp [announce]
lemma odour (x: Meadow G (Cotree f)): flavor 2 (spine G f x) (charter G f)=tale (psyche (Cotree f) G x):=by
 let H:=little (G:=G) (f:=f)
 ext1 i;by_cases h:i=0
 · subst i; rw [flavor_dark _ H.awake, tale_base,psyche_zero]
 rw [flavor_lo,← pack_extends (H.scope_ i) (show i+0 ≤ i+2 by omega),← speaking];rw [H.figures _ (show i>0 by omega),spurs]; simp
end Marks

section Gaussian
variable {K: Matrix (Book G f) (Book G f) ℝ}
variable (h:Vertex (beneath K)) (ht:K.transpose=K)(hf:Even f.val)
include h hf
lemma gains (x:Meadow G (Cotree f))(hx:x≠0): 0<phase K (spine G f x):=by
 have hv:=h (inhabit x);exact lt_of_le_of_ne hv.1 fun he=> hx (still _ hf (hv.2 he.symm))
include ht

def polar : Law (Meadow G (Cotree f)):= nymph (spine G f) K ht (gains h hf)
def axis : Layer (Book G f) (Book G f):= Diagram.Gaussian.bond (polar h ht hf) pupil
omit h ht hf in
lemma toner (i:ℕ) (x: Angle (Cotree f) Empty G) (he:i≠0): jet (priceMap (0:Hook G (Cotree f) Empty)) i x=0:=by rw [show priceMap (0:Hook G (Cotree f) Empty)=(fun _=>0) from rfl, jet,iteratedFDeriv_const_of_ne he]; simp
lemma lens : Nonempty (ZeroO (beneath K) (axis h ht hf) (charter G f)):=by
 let H:=little (G:=G) (f:=f)
 refine ⟨{ law:=polar h ht hf, slide:=fun (_:Meadow G Empty)=>0, directions:=pupil, covariance:=rfl, symmetry:=H.smooth, order:=H.form (by norm_num),witness:=fun w x i=>?_, gap:=fun w x=>?_, sing:=fun w x=>?_ }⟩
 · rw [silence w (Embedding.refl _ i),zero_add,add_zero];rfl
 · rw [add_zero, zeroJet]; change beneath K (inhabit x)+0= 0+_; rw [add_zero,zero_add];rfl
 dsimp only;let d:= (x,(1:ℝ),w); let F': Hook G (Cotree f) Empty:=0
 rw [prints,add_zero,zeroJet,neg_zero,Real.exp_zero,mul_one,map_one, one_mul];
 have he: logread (priceMap F') d=0:=by
    ext1 i; rw [logread,PowerSeries.coeff_mk, Series.Radial.layers,zeroJet,toner _ _ (by omega)];simp
 rw [show logread _ _=0 from he,show expo (0:PowerSeries ℝ)=1 from ?_,mul_one]
 · rw [show announce _ _ + _=spine G f x from ?_, odour];
   · let Y:= aura (1: Hook G (Cotree f) Empty); have hs:ContDiffAt ℝ ∞ Y 0:=contDiffAt_const.mul (((Chart.Ratio.jacobian_smooth (traySpec G)).of_le le_top).comp (f:=Prod.fst) (0: Angle (Cotree f) Empty G) contDiffAt_fst); rw [← lore hs d]
     rw [show (fun t:ℝ=>Y (t • d))=fun t=> Chart.jacobian (tray G) (t • x) from funext fun t=>one_mul _]; exact spirit ..
   ext1 i; rw [Pi.add_apply,silence w i, zero_add]; rfl
 ext i; rw [expo,PowerSeries.coeff_mk, truncP, Finset.sum_eq_single_of_mem 0 (by simp)]; simp
 intro b _ ht; rw [zero_pow ht,smul_zero]
end Gaussian
end YM.RegulatorIR.StopB
