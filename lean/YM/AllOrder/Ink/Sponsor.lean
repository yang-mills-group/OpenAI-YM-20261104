import YM.AllOrder.Ink.Spurt
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Ink
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function Fire Laplace.SigmaP Ker
open Progress.ClassicalKin Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial Response
open scoped BigOperators Topology Classical ContDiff
variable {n m:Side} {α β : Type} [Fintype α] [Fintype β] {k N M:ℕ} {a C D b:ℝ}
namespace Money
open Method
variable {V:Type}{Λ:V→ℝ} {Ad:Side→Prop}
variable (A:Stalk α α)(H:Belt A a C) (hC:0≤C)(ha:0<a)
variable {u v:Bills α}{X Y:Field α} {σ l l':ℝ}{π ρ: Side→ℝ}
  (hx:Pert Ad u X a l π k)(hy:Pert Ad v Y a l' ρ N) (hσ:0≤σ)(hs:σ*(N+1:ℕ) ≤ a)
def cubeD (α:Type)[Fintype α](n:Side)(k l : ℕ)(P x y : ℝ):= (Fintype.card (Leaf n α):ℝ)*((Fintype.card (Leaf n α):ℝ)*(P*((x*honor k)*(y*honor l))))
abbrev cellD (n:Side)(w:ℝ) := (Fintype.card (Site n):ℝ)*w
lemma Pert.fees (f:Bills α){n:Side}{C: Side→ℝ}(h:Pert Ad f X a l C k)(H:∀ n,0≤C n)(hm:0<a)(he:Ad n):Prices k (cellD n l+C n) (f n):= by
 have hy:= (h.1.binding (n:=n) hm.le); have hh:=h.2 n he; rw (occs :=.pos [1]) [← add_sub_cancel (X.table n) (f n)]; refine price_add hy (price_mono hh (mul_le_of_le_one_right (H n) ?_)); exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hm.le) (by positivity))
include hx hy hσ hs H hC ha
lemma spark_num (hP:∀ n,0≤π n)(hL:∀ n,0≤ρ n) : let β₀(n:Side):= cubeD α n k N C (π n) (cellD n l'+ρ n) + cubeD α n k N C (cellD n l) (ρ n); Pert Ad (fun n=> spark A (u n) (v n)) (embrace A X Y) σ (k * (N*(C*l')) *l) β₀ ((k-1)+(N-1)) := by
   intro β₀; refine ⟨gain_spark A X Y hσ hs hx.1 hy.1 H hC,fun n hn=>?_⟩; let r:= X.table n; let s:=Y.table n; let p:=u n-r; let q:= v n-s; let f (u v :rule α n→ℝ):= spark A u v; have hv(Z :ℝ)(b:ℝ)(he:σ≤b)(h:0≤Z):Z*dearth b n ≤ Z*dearth σ n:= by apply mul_le_mul_of_nonneg_left _ h; exact Real.exp_monotone (by gcongr)
   have hu := hx.fees u hP ha hn; have hu':= hy.fees v hL ha hn; have hp':=hx.1.binding (n:=n) ha.le; have hq':=hy.1.binding (n:=n) ha.le; have hπ:=hx.2 n hn; have hρ:=hy.2 n hn; let l0:= cubeD α n k N C (π n) (cellD n l'+ρ n); let l1:=cubeD α n k N C (cellD n l) (ρ n)
   have hf:f (u n) (v n) - f r s = f p (v n)+ f r q:= by
      ext1 x; let hx: (u n)= p+r:= (sub_add_cancel _ _).symm; let hv:= (sub_add_cancel (v n) s); let g a:= f a (v n) x; let w a:= f r a x; change g (u n)-_ = _ + _; rw [hx,show g (p+r)=_ from (toolA A k (v n) x).2.add _ _ hπ.2.1 hp'.2.1]; -- fix
      change (g p+w (v n))-w s=g p+w q; rw (occs:=.pos [1]) [show v n=q+s from hv.symm]; rw [(show w (q+s)=_ from (toolA A N r x).1.add _ _ hρ.2.1 hq'.2.1)]; abel
   rw [← embracing A X Y ha.le H hC hx.1 hy.1 hσ hs n,hf];
   have hb : σ≤a:= le_trans (le_mul_of_one_le_right hσ (by exact_mod_cast (show 1≤N+1 by omega))) hs
   refine price_mono (price_add (spark_est A k N H ha.le hπ hu') (spark_est A k N H ha.le hp' hρ)) ((le_of_eq ?_).trans (hv (β₀ n) a hb ?_))
   · change cubeD α n k N C (π n * dearth a n) _+cubeD α n k N C _ _= (_+_)*dearth a n; unfold cubeD; ring
   change 0≤ _+_; have hl:0≤ l:= hx.1.nonneg; have hl':0≤ l':= hy.1.nonneg; unfold cubeD cellD; have hD:=hL n; have hP:=hP n; have hq:= honor_pos k; have hh:=honor_pos N; positivity
end Money
end YM.AllOrder.Ink
