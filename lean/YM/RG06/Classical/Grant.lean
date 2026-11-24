import YM.RG06.Classical.Green
import YM.Maxwell.Shell

/-!
# Divergence source for one homogeneous degree -> polynomial radial connection solution!
Use this explicit canonical right inverse, no choice involved. Lie/O4 equivariance work
separately. Left obstruction source divergence-free crucial (for *nonlinear* Euler equations,
customer will prove it from lower equations and covariant conservation, not postulate
constraints on independent operator jets). No regulator or correlations involved.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG06.ClassicalOn
open Function Labels Analysis Continuum Tensor
open scoped ContDiff BigOperators Classical Matrix.Norms.Frobenius InnerProductSpace Topology
variable {G:Gauge}{E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E]
variable {n k:ℕ}

structure Vectorial (n:ℕ)(f:Axis→E4→E):Prop where
   order(i): Level n (f i)
   div0: (∑ i:Axis,par i (f i))=0
namespace Vectorial
variable {f:Axis→E4→E}
private abbrev Gen(i:Axis)(x:E4):ℝ:=x i
lemma basis_pull (i j:Axis)(x:E4): par i (Gen j) x=basis i j:=by
 unfold par D Gen; let L:= (EuclideanSpace.proj j:E4→L[ℝ]ℝ); change fderiv ℝ L x _=_; rw [L.fderiv]; rfl
def area (n:ℕ)(f:Axis→E4→E)(i j:Axis)(x:E4):=((3+n:ℕ):ℝ)⁻¹ • ( Gen i x • f j x- Gen j x • f i x )
lemma area_sym (n:ℕ)(i j:Axis): area n f j i= -area n f i j:=by funext x; simp [area, ← smul_neg]
lemma area_level (e:Vectorial n f)(i j:Axis): Level (n+1) (area n f i j):=by
 rw [Nat.add_comm]; exact Level.scale (((Level.component i).eval (e.order j)).sub ((Level.component j).eval (e.order i))) _

lemma area_div (e:Vectorial n f)(j:Axis): (∑ i:Axis,par i (area n f i j))=f j:=by
 let U(i j:Axis)(x:E4):=Gen i x • f j x
 have he(i j):Level (1+n) (U i j):=(Level.component i).eval (e.order j)
 have ht(i j:Axis): Good (U i j - U j i):=ContDiff.sub (he i j).smooth (he j i).smooth
 funext x
 change (∑ i:Axis,par i (fun x=>((3+n:ℕ):ℝ)⁻¹ • (U i j-U j i) x)) x=f j x
 have HX(i): par i (fun x=>((3+n:ℕ):ℝ)⁻¹ • (U i j-U j i) x) = ((3+n:ℕ):ℝ)⁻¹ • (par i (U i j)-par i (U j i)):=by
    rw [show (fun x=> ((3+n:ℕ):ℝ)⁻¹ • _)= ((3+n:ℕ):ℝ)⁻¹ • (U i j-U j i) from rfl, par_scale _ (ht _ _),sub_eq_add_neg,par_add (g:=-U j i) (he _ _).smooth (ContDiff.neg (he _ _).smooth),par_neg, sub_eq_add_neg]
 have hZ(i m l:Axis): par i (U m l) x = basis i m • f l x + Gen m x • par i (f l) x:=by unfold U; rw [par_eval (Level.component m).smooth (e.order l).smooth,basis_pull]
 simp_rw [HX, Finset.sum_apply,Pi.smul_apply,Pi.sub_apply, hZ,←Finset.smul_sum,Finset.sum_sub_distrib,Finset.sum_add_distrib, basis_eq, ite_smul, zero_smul,one_smul,if_true,Finset.sum_const,Finset.card_univ,Fintype.card_fin]
 rw [show (∑i:Axis, Gen i x • par i (f j) x)=_ from (e.order j).euler x, ← Finset.smul_sum, ← show (∑i:Axis, par i (f i)) x=(∑i:Axis, par i (f i) x) from Finset.sum_apply ..,e.div0,Pi.zero_apply,smul_zero]
 have hs:(∑ i:Axis,if j=i then f i x else 0)=f j x:=by simp
 rw [hs,add_zero, ← Nat.cast_smul_eq_nsmul ℝ];
 let P:= f j x; have hv:(3+(n:ℝ))≠0:=by positivity
 push_cast
 rw [show (4:ℝ) • P + (n:ℝ) • P - P=(3+(n:ℝ)) • P from (by module), smul_smul,inv_mul_cancel₀ hv,one_smul]

def formal(n:ℕ)(f:Axis→E4→E)(i j:Axis): E4→E:= ((2:ℝ)⁻¹) • (ClassicalOn.inverse (n+1) 0 (area n f i j) -ClassicalOn.inverse (n+1) 0 (area n f j i))
lemma fair(e:Vectorial n f)(i j:Axis): Level (n+3) (formal n f i j):=by
  have he(i j):=inverse_hom (n+1) 0 (area_level e i j)
  exact Level.scale ((he i j).sub (he j i)) _
lemma formal_sym(n:ℕ)(i j:Axis): formal n f j i = -formal n f i j:=by rw [formal,formal, ← smul_neg,neg_sub]
lemma end_up (e:Vectorial n f)(i j:Axis): lap (formal n f i j)=area n f i j:=by
  have he(i j):= (inverse_hom (n+1) 0 (area_level e i j)).smooth
  unfold formal; rw [lap_scale (f:=ClassicalOn.inverse (n+1) 0 (area n f i j) - ClassicalOn.inverse (n+1) 0 (area n f j i)) _ (ContDiff.sub (he i j) (he j i)), sub_eq_add_neg,lap_add (g:=-ClassicalOn.inverse (n+1) 0 (area n f j i)) (he i j) (ContDiff.neg (he j i)),show ∀u:E4→E, lap (-u)= -lap u from fun u=>by unfold lap; simp_rw [par_neg, Finset.sum_neg_distrib]]
  simp_rw [solved _ _ (area_level e _ _),untold,area_sym n i j, neg_neg]; module

-- General commutation tools
lemma par_sw {E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E]{f:E4→E}(h:Good f)(i j:Axis):par i (par j f) = par j (par i f):=funext fun _=>par_cross h ..
lemma lap_par {E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E]{f:E4→E}(h:Good f)(i:Axis):lap (par i f)=par i (lap f):=by
 unfold lap; rw [par_sum _ _ (fun j _=> (h.par _).par _)]
 refine Finset.sum_congr rfl fun j _=>?_ ; conv_lhs=> rw [par_sw h j i]
 rw [par_sw (h.par j) j i]
lemma lap_sum {E I:Type*}[NormedAddCommGroup E][NormedSpace ℝ E](s:Finset I)(f:I→E4→E)(h:∀i∈s,Good (f i)): lap (∑ i∈s,f i)=∑i∈s, lap (f i):=by
 unfold lap; simp_rw [par_sum s f h _, par_sum s (fun i=>par _ (f i)) (fun i hi=>(h i hi).par _) _]; exact Finset.sum_comm

def raw(n:ℕ)(f:Axis→E4→E)(j:Axis): E4→E:=∑ i:Axis,par i (formal n f i j)
lemma raw_level (e:Vectorial n f)(i:Axis): Level (n+2) (raw n f i):=by apply Level.sum; intro j _; exact Level.advance (fair e j i) _
lemma raw_cost (e:Vectorial n f)(j:Axis):lap (raw n f j)=f j:=by
 unfold raw; rw [lap_sum _ _ (fun i _=> (fair e i j).smooth.par i)]; simp_rw [lap_par (fair e _ _).smooth,end_up e]; exact area_div e j
lemma raw_free(e:Vectorial n f):(∑ i:Axis, par i (raw n f i))=0:=by
 unfold raw; simp_rw [par_sum _ _ (fun j _=> (fair e j _).smooth.par j)]
 let F(i j):=par i (par j (formal n f j i))
 let X:E4→E:=∑ i:Axis,∑ j:Axis,F i j
 have he: X= -X:=by
    unfold X; conv_lhs=> rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro k _; rw [← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro i _; unfold F
    rw [par_sw (fair e k i).smooth i k,formal_sym n i k]
    simp only [par_neg]
 change X=0
 -- use char 0
 apply smul_right_injective _ (by norm_num : (2:ℝ)≠0); dsimp only; erw [two_smul,smul_zero]; nth_rw 2 [he]; simp
end Vectorial
namespace Vectorial
variable {f:Axis→E4→E}
def jem (n:ℕ)(f:Axis→E4→E)(x:E4):=((↑(n+3):ℝ)⁻¹) • (∑ i:Axis,x i • raw n f i x)
def chart (n:ℕ)(f:Axis→E4→E)(i:Axis):= raw n f i-par i (jem n f)
private lemma level_jem (h:Vectorial n f):Level (n+3) (jem n f):=by
 rw [show n+3=1+(n+2) by omega];
 apply Level.scale (f:=fun x:E4=>∑ i:Axis,x i • raw n f i x) ?_ _
 have he:=Level.sum (E:=E) (k:=1+(n+2)) (Finset.univ:Finset Axis) (fun i x=> x i • raw n f i x) (fun i _=>(Level.component i).eval (raw_level h _))
 rw [show (fun x:E4=>∑ i:Axis,x i • raw n f i x)=∑ i:Axis,(fun x:E4=>x i • raw n f i x) by ext; simp]; exact he
lemma membership (h:Vectorial n f)(i:Axis):Level (n+2) (chart n f i):=(raw_level h i).sub (Level.advance (level_jem h) i)
lemma resets (h:Vectorial n f)(z:E4): (∑i:Axis,z i • chart n f i z)=0:=by
 unfold chart; simp only [Pi.sub_apply,smul_sub,Finset.sum_sub_distrib]
 rw [(level_jem h).euler z,jem, smul_smul,mul_inv_cancel₀ (by positivity),one_smul,sub_self]

def MaxwellOp (B:Axis→E4→E)(b:Axis):=∑ i:Axis,par i (par i (B b) - par b (B i))
lemma maxwell_value (B:Axis→E4→E)(h:∀i,Good (B i))(b:Axis):MaxwellOp B b=lap (B b)-par b (∑ i:Axis,par i (B i)):=by
 rw [lap,par_sum _ _ (fun i _=> (h i).par i),← Finset.sum_sub_distrib]; unfold MaxwellOp; refine Finset.sum_congr rfl fun i _=>?_
 rw [sub_eq_add_neg,par_add (g:=-par b (B i)) ((h b).par i) (ContDiff.neg ((h i).par b)),par_neg,par_sw (h i) i b,← sub_eq_add_neg]
lemma gauge_linear (B:Axis→E4→E)(hB:∀i,Good (B i))(Φ:E4→E)(h:Good Φ)(b:Axis):
    MaxwellOp (fun i=>B i-par i Φ) b=MaxwellOp B b:=by
 unfold MaxwellOp; apply Finset.sum_congr rfl; intro i _; apply congrArg (par i)
 simp only [sub_eq_add_neg]
 rw [par_add (g:=-(par _ Φ)) (hB _) (ContDiff.neg (h.par _)),par_add (g:=-(par _ Φ)) (hB _) (ContDiff.neg (h.par _)), par_neg,par_neg,par_sw h i b]; abel
lemma overseen(h:Vectorial n f)(b:Axis):MaxwellOp (chart n f) b=f b:=by
 unfold chart; rw [gauge_linear _ (fun i=>(raw_level h i).smooth) _ (level_jem h).smooth,maxwell_value _ (fun i=>(raw_level h i).smooth),raw_cost h,raw_free h,Level.bottom (Level.zero (E:=E) 0),sub_zero]
end Vectorial
open Vectorial

/-- On canonical constrained radial coordinates themselves -/
def offer (n:ℕ)(v:Taylor G (n+1))(b:Axis):=MaxwellOp v.value b
def accepted {f: Axis→E4→G.Color}(h:Vectorial n f): Taylor G (n+1):=
   ⟨fun i=>Tensor.coeff (chart n f i) (n+2) 0,(fun i=> Tensor.coeff_symm ((ContDiff.contDiffAt (membership h i).smooth).of_le (WithTop.coe_le_coe.mpr le_top))),
     fun x=> (Finset.sum_congr rfl (fun i (_:i∈ (Finset.univ:Finset Axis))=> congrArg (x i • ·) ((membership h i).indicates x))).trans (resets h x)⟩
lemma postage{f:Axis→E4→G.Color}(h:Vectorial n f):offer n (accepted h)= f:=by
 funext b; unfold offer
 rw [show (accepted h).value=chart n f from ?_,overseen h]
 funext i x;exact (membership h i).indicates x
lemma drains {v:Taylor G (n+1)}: Vectorial n (offer n v):=by
 have ht(i:Axis):Level (n+2) (v.value i):=Level.tax ..
 constructor
 · intro i; unfold offer MaxwellOp; apply Level.sum; intro j _; exact (((ht i).advance j|>.sub ((ht j).advance i)).advance _)
 unfold offer MaxwellOp; simp_rw [par_sum _ _ (fun i _=> (Good.par (f:=fun x:E4=>_) (show Good (par i (v.value _) - par _ (v.value _)) from ContDiff.sub ((ht _).smooth.par _) ((ht _).smooth.par _)) i))]
 let F(i j:Axis):= par i (v.value j) - par j (v.value i)
 let X:=∑ i:Axis,∑ j:Axis,par i (par j (F j i))
 change X=0
 have hp: X= -X:=by
    unfold X; conv_lhs=> rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]; refine Finset.sum_congr rfl fun i _=>?_ ; rw [← Finset.sum_neg_distrib]; refine Finset.sum_congr rfl fun j _=>?_
    rw [par_sw (f:=F i j) (ContDiff.sub ((ht j).smooth.par i) ((ht i).smooth.par j)) j i,show F i j=-F j i from (neg_sub ..).symm]; simp only [par_neg]
 apply smul_right_injective _ (by norm_num : (2:ℝ)≠0); dsimp only; erw [two_smul,smul_zero]; nth_rw 2 [hp];simp


section Maxwell
open Maxwell
lemma offered (v:Taylor G (n+1))(b:Axis)(x:E4):(offer n v b x) =∑ i:Axis,grad i (diagonal (takeCurl v i b)) x:= by
 unfold offer MaxwellOp; rw [Finset.sum_apply]; simp_rw [takeCurl_diag]; rfl
lemma offer_shell (v:Shell G (n+1)):offer n (gaugeJet v)=0:=by funext b x; rw [offered,match_leg]; exact v.property.2 b x
def shelf (v:Taylor G (n+1))(h:offer n v=0):Shell G (n+1):=⟨takeCurl v, closedCurl v, fun b x=> by rw [← offered,h]; rfl⟩
lemma reference (v:Taylor G (n+1))(h:offer n v=0):gaugeJet (shelf v h)=v:=by
 apply Maxwell.potential.injective; exact Subtype.ext (match_leg _)
lemma rooms (v:Taylor G 0):∃ s:Shell G 0,gaugeJet s=v:=by
 suffices he: ∃ s:Shell G 0,s.val=takeCurl v by
   obtain ⟨s,hs⟩:=he; exact ⟨s,Maxwell.potential.injective (Subtype.ext ((match_leg _).trans hs))⟩
 refine ⟨⟨takeCurl v,closedCurl v,fun b x=>?_⟩,rfl⟩
 apply Finset.sum_eq_zero; intro i _; exact congr_fun ((Level.tax 0 _).bottom i (f:=Tensor.diagonal (takeCurl v i b))) x
end Maxwell
end YM.RG06.ClassicalOn

namespace YM.RG06.ClassicalOn.Vectorial
open Tensor Labels Analysis Continuum
open scoped ContDiff BigOperators Classical Matrix.Norms.Frobenius Topology
variable {E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E]{k:ℕ}{f:Axis→E4→E}
-- public nontransverse extension of membership proofs, used ONLY for triangular tours
lemma all_raw (h:∀ i,Level k (f i))(b:Axis):Level (k+2) (raw k f b):=by
 have he(i j:Axis): Level (k+1) (area k f i j):=by
    rw [Nat.add_comm]; exact Level.scale (((Level.component i).eval (h j)).sub ((Level.component j).eval (h i))) _
 unfold raw; apply Level.sum; intro j _; apply Level.advance
 exact Level.scale ((inverse_hom (k+1) 0 (he _ _)).sub (inverse_hom (k+1) 0 (he _ _))) _
lemma all_jem (h:∀ i,Level k (f i)):Level (k+3) (jem k f):=by
 rw [show k+3=1+(k+2) by omega];
 apply Level.scale (f:=fun x:E4=>∑ i:Axis,x i • raw k f i x) ?_ _
 rw [show (fun x:E4=>∑ i:Axis,x i • raw k f i x)=∑ i:Axis,(fun x:E4=>x i • raw k f i x) by ext; simp]
 exact Level.sum _ _ (fun i _=>(Level.component i).eval (all_raw h i))
lemma all_chart (h:∀ i,Level k (f i))(b:Axis): Level (k+2) (chart k f b):=(all_raw h b).sub ((all_jem h).advance b)
lemma all_rad (h:∀ i,Level k (f i))(x:E4): (∑ i:Axis,x i • chart k f i x)=0:=by
 unfold chart; simp only [Pi.sub_apply,smul_sub,Finset.sum_sub_distrib]; rw [(all_jem h).euler x,jem, smul_smul,mul_inv_cancel₀ (by positivity),one_smul,sub_self]
end YM.RG06.ClassicalOn.Vectorial
