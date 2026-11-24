import YM.OPE.Compatible.Grid.Ours
/-! # Lowest coupling and grade maps -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade.Grid
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open PertExtension Series ScriptJ GaussianScore Work.F05 Rill Glass Coin Pilot Radial Flock
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier
variable {I J:Type}{G:Gauge}{n c f:Side}{d j k m:ℕ}{Q:Muse G}
section rank
variable (q z: Curtain I)
open Polynomial
lemma rollScale (q:Curtain I)(z:Site n)(p:deck I n)(x:ℝ)(k:ℕ): Flume.Script.value z (q k) (x • p)= Flume.Script.value z (q k) p*x^k:=by
    unfold Flume.Script.value scribe; rw [← tsum_mul_right]; refine tsum_congr (fun i=>?_); rw [mul_assoc]; congr 1; simp only [render, Pi.smul_apply, smul_eq_mul,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin]; exact mul_comm ..
lemma rollPoly (q:Curtain I)(z:Site n)(p:deck I n)(x:ℝ)(d:ℕ): Flair q d (x • p) z= Polynomial.eval x (∑ i∈Finset.range (d+1), Polynomial.monomial i (Flume.Script.value z (q i) p)):=by
    rw [eval_finsetSum]; simp_rw [eval_monomial]; unfold Flair; simp only [rollScale]
lemma coinsP (a b: deck I n)(j:Site n)(h:∀ c:ℝ, Flair q d (c • a) j= Flair z d (c • b) j)(he:k≤d):Script.value j (q k) a=Script.value j (z k) b:=by
    let f(u:Curtain I)(r:deck I n): Polynomial ℝ:=∑ i∈Finset.range (d+1), Polynomial.monomial i (Script.value j (u i) r); have ht:f q a=f z b:=Polynomial.funext fun i=> (rollPoly q j a i d).symm.trans ((h i).trans (rollPoly ..))
    have hv(u:Curtain I)(r:deck I n):coeff (f u r) k=Script.value j (u k) r:=by unfold f; rw [finsetSum_coeff]; rw [Finset.sum_eq_single k]; rw [coeff_monomial]; simp; intro i _ hi; simp [coeff_monomial,hi]; intro hz; exact False.elim (hz (Finset.mem_range.mpr (by omega)))
    rw [← hv,ht,hv]
end rank
lemma dwell {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E] [Fintype I] (x y:E→L[ℝ] deck I c) (q:Curtain I)(r:ℕ)(u:Site c)(hp:Summable (q r))(hs:(q r).sorted) (h:∀ v:E,Script.value u (q r) (x v)=Script.value u (q r) (y v)) (v:Fin r→E) : scribe u (q r) (x∘v)=scribe u (q r) (y∘v):=by
     let T:=orchestra (q r) u; have he(z:E→L[ℝ] deck I c):Tensor.Sym (T.compContinuousLinearMap (fun _=> z)):= fun h p=>ordered hs hp u (z ∘ h) p; have hh: T.compContinuousLinearMap (fun _=>x)=T.compContinuousLinearMap (fun _=>y):= Tensor.ext_diag _ _ (he x) (he y) (funext fun v=> (instruments _ hp ..).tsum_eq.symm.trans ((h v).trans (instruments _ hp ..).tsum_eq))
     exact (instruments _ hp ..).tsum_eq.trans ((DFunLike.congr_fun hh v).trans (instruments _ hp ..).tsum_eq.symm)
-- lift
def cliffL (G:Gauge)(n:Side):deck G.ColorIndex n→L[ℝ] deck (Shade G) n:=LinearMap.toContinuousLinearMap {
     toFun :=cliff
     map_add':=by intro x y; funext i; simp [cliff]; ring
     map_smul':=by intro c x; funext i; change c*_ -c*_ = c*(_-_); ring }
def hueL (p:G.El)(n:Side):deck (Shade G) n→L[ℝ] deck (Shade G) n:= LinearMap.toContinuousLinearMap {
     toFun:= hue p
     map_add':=by
          intro x y; ext1 i; let u(z:deck (Shade G) n):G.Color:= toLp 2 fun t=> z (i.1,i.2.1,t); change G.adjoint p (u (x+y)) _=G.adjoint p (u x) _+G.adjoint p (u y) _; rw [show u (x+y)=u x+u y from rfl,map_add]; rfl
     map_smul':=by
          intro c x; ext1 i; let u(z:deck (Shade G) n):G.Color:= toLp 2 fun t=> z (i.1,i.2.1,t); change G.adjoint p (u (c • x)) _= c*G.adjoint p (u x) _; rw [show u (c • x)=c • u x from rfl,map_smul];rfl }
lemma standP (h:Pathic d Q)(hq:Summable (Q 0 k))(he:k ≤ d)(hp:sorted (Q 0 k)): abides (Q 0 k)∧ painted (Q 0 k):=by
     constructor
     · intro i n w s; let U:=deck (Shade G) n; let V:= deck G.ColorIndex n; let X:= cliffL G n; let f:=ContinuousLinearMap.fst ℝ U V; let g:=ContinuousLinearMap.snd ℝ U V; let t:=Q 0 k
       have hX(z:U × V) : Script.value 0 t ((f+X ∘L g) z)= Script.value 0 t (f z):=by
            apply coinsP _ _ _ _ (d:=d) _ _ he; intro c; rw [_root_.add_apply,smul_add,ContinuousLinearMap.comp_apply,← X.map_smul]; exact cogG h _ _ _
       let v:Fin k→ U × V:=update (fun j=> (w j,(0:V))) i (0,s); have hz:=dwell (f+X ∘L g) f (Q 0) k 0 hq hp hX v; let T:= orchestra t (0:Site n); have hF(i:Fin k→ deck (Shade G) n): scribe 0 t i=T i:= (instruments t hq ..).tsum_eq; have hh: (f+X ∘L g)∘ v= update w i (cliff s):=by funext a; unfold Function.comp v; by_cases he:a=i; subst a; simp only [_root_.add_apply,ContinuousLinearMap.comp_apply,update_self]; change 0+X s= _; rw [zero_add];rfl; rw [update_of_ne he,update_of_ne he]; change w _+X 0=_; rw [map_zero, add_zero]
       rw [← hh,hz]; exact (hF _).trans (T.map_coord_zero i (show f (v i)=0 by rw [show v i=_ from update_self i _ _]; rfl))
     intro n u p; let A:= hueL p n; let I:=ContinuousLinearMap.id ℝ (deck (Shade G) n); exact dwell A I _ _ _ hq hp (fun x=> coinsP _ _ _ _ _ (fun v=> by rw [← A.map_smul]; exact cogHue h (v • x) p _) he) u
lemma enters {f:ℝ}(h: Pathic d Q)(hp:Tide Q d m f)(hs:∀r:ℕ,sorted (Q 0 r)) (k:ℕ): Q 0 k ∈ cope G k m := by
    obtain H:= hp 0; by_cases he:k ≤ d; · have hv:= standP h (sootS (H.2 k)) he (hs k); exact ⟨⟨_,H.2 _⟩,hv.1,hv.2,hs _⟩
    rw [H.1 k (show d+0<k from by omega)]; exact (cope G k m).zero_mem
end YM.OPE.Cascade.Grid
