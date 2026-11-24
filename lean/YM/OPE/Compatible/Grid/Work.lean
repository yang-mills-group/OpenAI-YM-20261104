import YM.OPE.Compatible.Grid.Home
/-!
# spirit Difference loop at grade 0
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume.Script
open Page Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free WithLp Work.F08 Matrix Bloch Precision Wilson Planned.PrimaryIntegral295.Carrier Asymptotics PertExtension Series
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{s b U D:ℝ}{d r m k q:ℕ}
variable {p:Script (Shade G) k}
abbrev bandC (v:fieldX (Shade G))(x:Cover):G.Color:= (pieces v 0 (carryP x)).sum
lemma taPZ (v:fieldX (Shade G))(w:Walk) : travel (lotU ((0:ℝ) • v)) (0:Cover) w=1:=by
      let U:= lotU ((0:ℝ) • v); suffices h:∀ x:Cover,travel U x w=1 from h 0
      intro x; induction w generalizing x with
      | nil=>rfl
      | cons a w ih=>rw [travel,ih,mul_one]; rw [show U=lotU ( (0:ℝ) • v) from rfl,matStep]; simp
lemma runV (v:fieldX (Shade G))(x:Cover)(w:Walk) : HasDerivAt (fun t:ℝ=>G.mat (travel (lotU (t • v)) x w)) (G.colorMat (pieces v x w).sum) 0:=by
     simp_rw [syntaxU]; let k:= pieces v x w
     have ht (k:List G.Color): HasDerivAt (voyageX k) (G.colorMat k.sum) 0:=by
          induction k with
          | nil=> simpa only [List.sum_nil,G.colorMat.map_zero] using! hasDerivAt_const (x:=(0:ℝ)) (1:G.Mat)
          | cons i l ih=>
             have hx(a:G.Color): horse a 0=1:=by simp [horse]; 
             have he:HasDerivAt (horse i) (G.colorMat i) 0:=by convert! ((runner i).differentiable (by simp) 0).hasDerivAt using 1; change _=deriv (horse i) 0; rw [horse_step,hx,one_mul]
             have hs (k:List G.Color): voyageX k 0=1:=by induction k with | nil=>rfl| cons i k ih=> change horse i 0*_=1; rw [hx,one_mul]; exact ih
             have hg:= he.mul ih; rw [hs,hx, mul_one,one_mul] at hg; rw [List.sum_cons,map_add]; exact hg
     exact ht _
attribute [local instance] Gauge.frobInner
lemma arcRead (v:fieldX (Shade G))(i:Cover×Shade G): HasDerivAt (fun t:ℝ=> board (lotU (t • v)) i)
      (v i+(mountain (fun j=> (-bandC v j.1) j.2)) i) 0:=by
      let F(x) := carryP x; let e:= i.2; let b:= i.1+step e.1; let V(t:ℝ):= lotU (t • v); let w(t:ℝ):G.El:= travel (V t) 0 (ringO (i.1,e.1)); let S(p:Cover)(t:ℝ):G.Mat:= G.mat (travel (V t) 0 (F p)); let a:=indexS (i.1,i.2.1) v; let z:= a+(bandC v i.1-bandC v b)
      have hg (p:Cover)(t:ℝ): travel (V t) p (Lattice.reverse (F p))=(travel (V t) 0 (F p))⁻¹:=by
           have ht:= travel_reverse (F p) (V t) (0:Cover); rw [show stop 0 (F p)=p from route_end ..] at ht; exact ht
      have hh: G.mat∘ w=(S i.1)*(horse a)*(star∘(S b)):=by funext t; simp only [Function.comp_apply,w, ringO,travel_append,carryP,G.mat_mul,stop_append]; rw [route_end,show stop i.1 _= b from rfl,show travel (V t) b _= _ from hg b t]; simp only [Gauge.mat_inv]; rw [travel,travel,mul_one, matStep]; rfl -- reductions
      have hf:HasDerivAt (G.mat ∘ w) (G.colorMat z) 0:=by
           have hv(p:Cover): HasDerivAt (S p) (G.colorMat (bandC v p)) 0:=runV ..
           have h0: horse a 0 =1:=by simp [horse]; 
           have hap:HasDerivAt (horse a) (G.colorMat a) 0:=by convert! ((runner a).differentiable (by simp) 0).hasDerivAt using 1; change _=deriv (horse a) 0; rw [horse_step,h0,one_mul]
           have hx(p: Cover): S p 0=1:=by unfold S V; rw [taPZ,G.mat_one]
           rw [hh]; convert! (((hv _).mul hap).mul (hv b).star) using 1; simp only [hx,h0, mul_one,one_mul,Pi.mul_apply,G.colorMat_skew,star_one,z,map_add,map_sub]; abel -- hasStar Key
      let p:G.Mat→L[ℝ]ℝ:=(pleatsF i.2.2).toContinuousLinearMap; have hy: HasDerivAt (fun t:ℝ=> board (V t) i) (p (G.colorMat z)) 0:=by
           rw [show (fun t:ℝ=> board (V t) i)= (p ∘ (fun t=> G.mat (w t)-1)) from funext fun t=> (pleatsEq _ _).symm]; exact (p.hasFDerivAt.comp_hasDerivAt (0:ℝ) (hf.sub_const _))
      convert! hy using 1; change _= chin _ (G.projectColor ((1/2:ℝ) • (G.colorMat z-star (G.colorMat z)))); rw [G.colorMat_skew,sub_neg_eq_add,← two_smul ℝ, smul_smul, div_mul_cancel₀ _ (two_ne_zero),one_smul,G.project_colorMat]; unfold z mountain; change _+ (-(bandC v _) _- - _) = v _+((bandC v _) _-(bandC v _) _); abel
