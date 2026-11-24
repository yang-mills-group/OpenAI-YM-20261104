import YM.X.Dock.Era
/-!
# Triangle numerical contour with contacts (component functionally ∂ at z; z relative). Not leaving ζ as unspecified distribution. ANY poses. C_T reproducible integral (see adjacent calculus for existence). suppress normalize factors; turns via other modules.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Chir.Dock
open Lattice Wilson Next.Rank LiftMark PertExtension LatticePT Crate Porch Rays Clove Interval Size Braid Shelf Tot
open Finset MeasureTheory Filter Set Function Reed Ocean Stems Hinge Haze Fielding Print Tri Plate Imprint CellsInt Beamer Asymptotics Crate.Fund
open Maxwell (Green normal grad)
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge} {m k d:ℕ} {V:Type*} {n:Side} {q:ℕ+}{r R R' e c:ℝ}
local notation "ε"=> epsilon q
local notation "L"=>(atTop:Filter ℕ)
local notation "T"=> Axis
abbrev tracker (A:Floor R)(x y z:E4)(t u v p:Tet)(i a b d:T):ℝ:= Bolt A x y z i (Aster 1 p a) (pull i (Aster 1 p a)) (Aster (-1) u b) (pull i (Aster (-1) u b)) (Aster (-1) v d) (pull i (Aster (-1) v d)) -- t extraneous
abbrev stableJ (A:Floor R)(x y z:E4):Prop:= ∀ t u v:Tet,∀ i a b d:T, Armor A x y z i (Aster 1 t a) (pull i (Aster 1 t a)) (Aster (-1) u b) (pull i (Aster (-1) u b)) (Aster (-1) v d) (pull i (Aster (-1) v d))
def overall (A:Floor R) (x y z:E4):Ter:= fun t u v p=> ∑ a:T,∑ i:T,form (-1) t i a* (∑ b:T,∑ d:T,form (-1) t b d * tracker A x y z t u v p i a b d)
variable (hq:1<q.val)(χ:Floor R)(hr:R<r) (X Y Z:Fielding.Walk) {x y z:E4} (hX:plot q X x)(hY:plot q Y y)(hZ:plot q Z z)(H:Search x y z r)
include hq hr hX hY hZ H
local notation "mo"=> transfer (-1)
lemma rooters : stableJ χ x y z∧ RootJ q X Y Z (overall χ x y z):= by
    let ψ(a i b d:T)(u v t:Tet):ℕ→ℝ:=lateral q X Y Z i (transfer 1 t a) (transfer (-1) u b) (transfer (-1) v d); have he:=fun (p u v:Tet)(i a b d:T)=>goes_price hq χ hr X Y Z x y z i hX hY hZ H _ _ _ _ _ _ _ _ _ (atlases 1 p i a hq) (atlases (-1) u i b hq) (atlases (-1) v i d hq); refine ⟨fun t u v i a b d=>(he t u v i a b d).1,fun t u v p=>?_⟩; refine (show Tendsto (fun k:ℕ=>∑ a:T,∑ i:T,form (-1) t i a *(∑ b:T,∑ d:T,form (-1) t b d * ψ a i b d u v p k)) L (𝓝 (overall χ x y z t u v p)) from tendsto_finsetSum _ (fun a _=>tendsto_finsetSum _ (fun i _=> ((tendsto_finsetSum _ fun b _=> tendsto_finsetSum _ fun d _=> ((he p u v i a b d).2.const_mul _)).const_mul _)))).congr fun k=> ?_ -- whitespace
    let f:=form (-1) t; let n:=side q k; let e:=ε k; let U(b:T)(x:Site n):= run q X 1 (mo u b) k x; let K(d:T)(x:Site n):=run q Y 1 (mo v d) k x; let P(a i:T)(x:Site n):= run q Z 2 (ds i (transfer 1 p a)) k x; let a:=transit q X k; let b:=transit q Y k; let c:=transit q Z k
    have hu(x:Site n): ester n e (-1) t u v a b x= ∑ i:T,∑ j:T,f i j*(U i x*K j x):= by unfold ester; simp_rw [mul_assoc]; rfl
    have hv(x:Site n): Wpp e 1 p (-1) t n c x= ∑ i:T,∑ j:T,f j i * P i j x:= by unfold Wpp exchangeF;simp only [sprite_val,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _=> Finset.sum_congr rfl (fun j _=> mul_left_comm _ (form (-1) t j i) _))
    change _= Union_z n e a b c t u v p; unfold Union_z galley; simp_rw [hu,hv,Finset.sum_mul]; let F(a i b d:T)(x:Site n) := form (-1) t i a * (e^4* form (-1) t b d * (P a i x*(U b x*K d x))); have h(a i b d:T): form (-1) t i a * (form (-1) t b d * ψ a i b d u v p k)=∑ x:Site n,F a i b d x:= by change _*( _*(e^4* (∑ x:Site n,P a i x*(U b x*K d x))))=_; simp_rw [F,Finset.mul_sum]; exact Finset.sum_congr rfl fun x _=> (by ring)
    calc
      _ = ∑ x:Site n,∑ a:T,∑ i:T,∑ b:T,∑ d:T,F a i b d x:= by -- lhs
           simp_rw [Finset.mul_sum,h];  symm; rw [Finset.sum_comm]; refine Finset.sum_congr rfl (fun a _=>?_); rw [Finset.sum_comm]; refine Finset.sum_congr rfl (fun i _=>?_); rw [Finset.sum_comm]; refine Finset.sum_congr rfl (fun b _=>?_); rw [Finset.sum_comm]; -- pass
      _ = _:= by
                 simp_rw [Finset.mul_sum]; iterate 5
                   refine Finset.sum_congr rfl (fun i _=>?_);
                 unfold f F; ring
end YM.PositionX.Chir.Dock
