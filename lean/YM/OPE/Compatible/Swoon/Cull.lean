import YM.OPE.Compatible.Swoon.Sap
/-!
# Tilt cumulants. Arithmetic helpers. Sym multilinear
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Libra.Coin
open Function Filter Lattice Laurent Tree Woody Weir MeasureTheory Exterior Bloch Cascade Module
open scoped Topology BigOperators ComplexConjugate Classical ContDiff RealInnerProductSpace ENNReal
open RG Bid Pressure Precision FreeResolvent WithLp Next.Free Frequency
open PertExtension Series Asymptotics GaussianScore Radial Finset Matrix LinearMap Flock
variable {E F Y I:Type} [NormedAddCommGroup E][NormedSpace ℝ E]
abbrev R2 (E:Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]:= Tensor.T E ℝ 2
abbrev R3 (E:Type*) [NormedAddCommGroup E][NormedSpace ℝ E]:= Tensor.T E ℝ 3
abbrev R4 (E:Type*) [NormedAddCommGroup E][NormedSpace ℝ E]:= Tensor.T E ℝ 4
def with2 (T:R2 E): E→ₗ[ℝ] Dual' E where
   toFun p:= {
      toFun r:=T (![p,r])
      map_add' x y:=by
          have hb:= DFunLike.congr_fun ((T.curryLeft p).curryLeft.map_add x y) (![]); exact hb
      map_smul' c x:=by have hb:= DFunLike.congr_fun ((T.curryLeft p).curryLeft.map_smul c x) (![]); exact hb }
   map_add' x y:= by apply LinearMap.ext; intro z; exact DFunLike.congr_fun (map_add T.curryLeft x y) (![z])
   map_smul' c x:= by apply LinearMap.ext; intro z; exact DFunLike.congr_fun (map_smul T.curryLeft c x) (![z])
abbrev carg (T:R3 E)(u:E):R2 E:= T.curryLeft u
abbrev bang (T:R4 E)(u:E):R3 E:= T.curryLeft u
lemma pact (T:R3 E)(x y z:E)(hs:Tensor.Sym T): T ![x,y,z]=T ![y,x,z]:=by let q:= Equiv.swap (0:Fin 3) 1; rw [show ![x,y,z]= _ from (show ![x,y,z]= ![y,x,z] ∘ q from funext fun i=>by fin_cases i<;>rfl)]; exact hs ..
lemma buck2 (T:R2 E)(x y:E)(h:Tensor.Sym T):T ![x+y,x+y]= T ![x,x]+2*T ![x,y]+T ![y,y]:=by
    let A:=with2 T; change A (x+y) (x+y)= A x x+2*A x y+A y y; have hh:A y x=A x y:=by
         change T ![y,x]=_; let q:=Equiv.swap (0:Fin 2) 1; rw [show ![y,x]=![x,y]∘ q from funext fun i=>by fin_cases i <;> rfl]; exact h (![x,y]) q
    simp only [map_add,LinearMap.add_apply,hh];ring
lemma hark2 {m:ℕ}(T:Tensor.T E ℝ (m+1))(p:E)(ht:Tensor.Sym T): Tensor.Sym (T.curryLeft p) := by
    intro v i; change T (Fin.cons p (v ∘ i))=T _; let k:= Equiv.Perm.decomposeFin.symm (0,i)
    rw [show Fin.cons p (v ∘ i)=Fin.cons p v ∘ k from ?_]; exact ht ..
    ext1 j; refine Fin.cases ?_ (fun l=>?_) j <;>simp [k]
lemma buck3 (T:R3 E)(x y:E)(h:Tensor.Sym T):T ![x+y,x+y,x+y]= T ![x,x,x]+3*T ![y,x,x]+3*T ![x,y,y]+T ![y,y,y]:=by
    let U:=carg T x; let W:= carg T y; have hh : U ![x,y]=T ![y,x,x]:=by
         change T ![x,x,y]=_; let p:= Equiv.swap (2:Fin 3) 0; rw [show ![x,x,y]=![y,x,x]∘ p from funext fun i=>by fin_cases i<;>rfl]; exact h ..
    change T.curryLeft (x+y) ![x+y,x+y]= U ![x,x]+3*T ![y,x,x]+3*U ![y,y]+W ![y,y]; rw [show T.curryLeft (x+y)= U+W from map_add ..,_root_.add_apply,buck2 U x y (hark2 T x h),buck2 W x y (hark2 T y h),hh, show W ![x,x]=T ![y,x,x] from rfl,show W ![x,y]=U ![y,y] from pact T y x y h];ring
lemma buck4 (T:R4 E)(x y:E)(h:Tensor.Sym T):T ![x+y,x+y,x+y,x+y]= T ![x,x,x,x]+4*T ![y,x,x,x]+6*T ![x,x,y,y]+4*T ![x,y,y,y]+T ![y,y,y,y] := by
    let U:=bang T x; let W:=bang T y; have ht:= hark2 T x h; have hw:=hark2 T y h
    change T.curryLeft (x+y) ![x+y,x+y,x+y]= U ![x,x,x]+4*W ![x,x,x]+6*U ![x,y,y]+4*U ![y,y,y]+W ![y,y,y]; rw [show T.curryLeft (x+y)=U+W from map_add ..,_root_.add_apply,buck3 U ..,buck3 W ..] -- hh args
    · have he : U ![y,x,x]=W ![x,x,x]:=by let p:=Equiv.swap (1:Fin 4) 0; change T ![x,y,x,x]=_; rw [show ![x,y,x,x]=![y,x,x,x] ∘ p from funext fun i=>by fin_cases i<;>rfl]; exact h ..
      have hh : W ![y,x,x]= U ![x,y,y]:=by
           let q:= (Equiv.swap (0:Fin 4) 2).trans (Equiv.swap 1 3); change T ![y,y,x,x]=_; rw [show ![y,y,x,x]=![x,x,y,y] ∘ q from funext fun i=>by fin_cases i<;>rfl]; exact h ..
      have hQ : W ![x,y,y]=U ![y,y,y]:=by let p:=Equiv.swap (0:Fin 4) 1; change T ![y,x,y,y]=_; rw [show ![y,x,y,y]=![x,y,y,y] ∘ p from funext fun i=>by fin_cases i<;>rfl]; exact h ..
      rw [he,hh,hQ];ring
    all_goals assumption
end YM.OPE.Libra.Coin
