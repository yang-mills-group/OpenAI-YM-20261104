import YM.OPE.Compatible.Vines.Epic
/-! Principal inverse stencils -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free Maxwell Labels Tensor ContinuousMultilinearMap WithLp
open scoped Topology BigOperators Classical
variable {r d m n:ℕ}{c:ℝ}{V W:Type*}{G:Gauge}
namespace Script
open Page
section pol
variable (W) [AddCommGroup W][Module ℝ W]
def movesX (i:Axis): (Cover→ W) →ₗ[ℝ] (Cover→ W):=LinearMap.pi (fun (x:Cover)=> (LinearMap.proj (R:=ℝ) (φ:=fun _=>W) (x+step i) - LinearMap.proj (R:=ℝ) (φ:=fun _=>W) x))
lemma moveX_eq (v:Cover→W)(i:Axis)(x:Cover): movesX W i v x=v (x+step i)-v x:=rfl
def trainX : (d:ℕ)→(Fin d→Axis)→ (Cover→W) →ₗ[ℝ] (Cover→ W)
| 0,_=>LinearMap.id
| d+1,p=> trainX d (Fin.tail p) ∘ₗ movesX W (p 0)
variable {W}[AddCommGroup V][Module ℝ V]
lemma tracksX (f:W→ₗ[ℝ] V)(v:Cover→W)(t:Fin d→Axis): trainX V d t (f ∘ v)=f ∘ (trainX W d t v):=by
    induction d generalizing v with
    | zero=>rfl
    | succ d ih=> rw [trainX, trainX, LinearMap.comp_apply,LinearMap.comp_apply,show movesX V (t 0) (f ∘ v)=f ∘ movesX W (t 0) v from funext fun i=> (map_sub f (v (i+step (t 0))) (v i)).symm,ih]
end pol
lemma moveLow (p:Flavor Axis d)(x:Axis):movesX ℝ x (p.val ∘ translit)=gust (basis x) p.val∘translit:=by ext v; have hv:translit (v+step x)=invertX (fromX (translit v)+basis x):=congr_arg invertX (cast_step v x); simp [gust,moveX_eq,hv]
lemma trackL (f:Lieu Axis→ℝ)(h:f∈Flavor Axis d) (z:Fin n→Axis)(ht:d<n):trainX ℝ n z (f ∘ translit)=0:=by
    induction n generalizing d f with
    | zero=>omega
    | succ n ih=>
       rw [trainX, LinearMap.comp_apply]; let v:Flavor Axis d:=⟨f,h⟩; rw [moveLow ⟨f,h⟩]; change trainX ℝ n _ (gust _ f ∘ translit)=_; have hs:= sudden f h (basis (z 0)); by_cases he:d=0
       · rw [hs.2 he]; exact map_zero _
       exact ih _ hs.1 _ (by omega)
lemma breezedL (f: Lieu Axis→ℝ)(h:f∈Flavor Axis (d+1)) (a:Axis) (p:Fin d→Axis): trainX ℝ d p (movesX ℝ a (f ∘ translit))=trainX ℝ d p (breeze (basis a) f ∘ translit):=by
    let x:=basis a; have hh:= tailP f h x; rw [moveLow ⟨f,h⟩]; by_cases ht:d=0
    · change trainX _ _ _ (gust x f ∘ translit)=_; rw [hh.2 (by omega)]
    apply sub_eq_zero.mp; rw [← map_sub]; exact trackL _ hh.1 _ (by omega)
lemma totX (T:Tensor.T E4 ℝ d) (h:Tensor.Sym T)(p:Fin d→Axis)(x:Cover):
    trainX ℝ d p (diagonal T∘fromX∘translit) x=(d.factorial:ℝ)* T (fun i=>basis (p i)):=by
    induction d with
    | zero=> simp only [trainX,LinearMap.id_apply,Nat.factorial_zero,Nat.cast_one,one_mul]; exact congr_arg T (Subsingleton.elim ..)
    | succ d ih=>
       let f:=diagonal T∘fromX; let v:= basis (p 0); rw [trainX,LinearMap.comp_apply]; erw [breezedL f (tgon T)]; let B:= T.curryLeft v
       have hh:breeze v f = ((d+1:ℕ):ℝ) • (diagonal B ∘ fromX):=by
          ext t; calc
             _ = fderiv ℝ (diagonal T) (fromX t) v:=rfl
             _ = _:=by rw [differential_diagonal T h,Pi.smul_apply, Nat.cast_smul_eq_nsmul]; rfl
       let g:= trainX ℝ d (Fin.tail p); let C:ℝ:=(d+1:ℕ)
       rw [hh, show (C • _) ∘ translit = (C : ℝ) • (diagonal B ∘fromX∘translit) from rfl]; rw [map_smul,Pi.smul_apply, ih B (freeze_sym T h _)]; simp only [smul_eq_mul,Nat.factorial_succ, Nat.cast_mul, mul_assoc]; congr! 2 -- B
       change T (Fin.cons v _) = _; apply congr_arg T; ext1 i; refine Fin.cases ?_ (fun j=>?_) i<;>rfl
end Script
end YM.OPE.Flume
