import YM.AllOrder.Ink.Adjoin
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Ink
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function Fire Laplace.SigmaP Ker
open Progress.ClassicalKin Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial Response
open scoped BigOperators Topology Classical ContDiff
variable {n m:Side} {α β : Type} [Fintype α] [Fintype β] {k N M:ℕ} {a C D b:ℝ}
namespace Method
open Field GaussianScore
local notation "L"=> Slip (Point α)
def toll {x y:Slip (Point α)} (i:LeafIdx x)(j:LeafIdx y)(w:Cover):= (knot x i).1 + w - (knot y j).1
def jointI (x y:L)(i:LeafIdx x)(j:LeafIdx y)(w:Cover):= eraseT x i ++ Field.along (toll i j w) (eraseT y j)
variable {x y:Slip (Point α)} {i:LeafIdx x}{j:LeafIdx y}
omit [Fintype α]
lemma hardL (h:x.length≤ k)(H:y.length ≤ N)(w:Cover): List.length (jointI x y i j w) ≤ (k-1)+(N-1):= by
   have hI := List.length_eraseIdx_add_one (l:=x) i.isLt; have hJ:= List.length_eraseIdx_add_one (l:=y) j.isLt; simp only [jointI, List.length_append, Field.along, List.length_map,eraseT]; omega
lemma hardP (H:y.length ≤ N)(w:Cover): meter (jointI x y i j w) ≤ (N+1)*(meter x+meter y+size w):=by
   have hp:= ending x i; have hq:=ending y j; have ht:size (toll i j w)≤ meter x+meter y+size w:= calc
      _ ≤ size ((knot x i).1+w)+size (knot y j).1:= by unfold toll; rw [sub_eq_add_neg]; exact (size_add _ _).trans_eq (congr_arg (size _+·) (size_neg _))
      _ ≤ _:= by have := size_add (knot x i).1 w; omega
   have hv := List.length_eraseIdx_add_one (l:=y) j.isLt; unfold jointI; rw [meter_add]; refine (Nat.add_le_add_left (lifted_cost ..) _).trans ((Nat.add_le_add_left (Nat.add_le_add_right (Nat.mul_le_mul (by unfold eraseT; omega : (eraseT y j).length≤ N) ht) _) _).trans ?_) -- placeholder
   rw [Nat.add_mul,Nat.one_mul]; omega
-- avoid includes: i j through estimates counts
variable (F:Stalk α α) (U V : Field α)
abbrev Family (A B:Field α): Type:= (i:A.Ty) × (j:B.Ty) × (_p:LeafIdx (A.slip i))×(_q:LeafIdx (B.slip j)) × Cover -- p Sigma syntax

def embrace (F:Stalk α α)(A B:Field α): Field α where
 Ty:= Family A B
 slip := fun ⟨i,j,p,q,w⟩=> jointI (A.slip i) (B.slip j) p q w
 fee := fun ⟨i,j,p,q,w⟩=> A.fee i*(B.fee j* F (knot (A.slip i) p).2 (knot (B.slip j) q).2 w)
-- sigma join cost exact
lemma gain_spark {b C D T:ℝ} (hp:0≤b)(hr:b*(N+1:ℕ) ≤ a)(hA:U.Good a C k)(hB:V.Good a D N)(hv:Belt F a T)(ht:0≤T):
    (embrace F U V).Good b ((k:ℝ)*((N:ℝ)*(T*D))*C) ((k-1)+(N-1)) := by
 let l(i:U.Ty):=k*(N*T*D)* U.price a i -- parenth nat coercions?
 have he(i:U.Ty)(j:V.Ty)(p:LeafIdx (U.slip i))(q:LeafIdx (V.slip j)): let u:= U.price a i; let v:= V.price a j;
      SumBudget (fun w:Cover=> (embrace F U V).price b ⟨i,j,p,q,w⟩) (T *u*v):= by
    intro u v; let f:=F (knot _ p).2 (knot _ q).2; let x:=U.slip i; let y:=V.slip j; let C':= u*v; have hC:= mul_nonneg (U.price_nonneg a i) (V.price_nonneg a j); rw [mul_assoc T, mul_comm T]; apply budget_mono (budget_scale hC (hv (knot x p).2 (knot y q).2)); · exact fun w=> (embrace F U V).price_nonneg ..
    intro w; unfold Field.price; change Real.exp (b*meter _)* |U.fee i*(V.fee j*f w)|≤ (Real.exp (a*meter x)* |U.fee i| *(Real.exp (a*meter y)* |V.fee j|))*(Real.exp (a*size w)* |f w|)
    rw [abs_mul,abs_mul]; refine (mul_le_mul_of_nonneg_right (show Real.exp (b*meter (jointI x y p q w)) ≤ Real.exp (a*(meter x+(meter y:ℝ)+(size w:ℝ))) from (Real.exp_monotone ?_)) (by positivity : 0 ≤ |U.fee i| *(|V.fee j| * |f w|))).trans_eq ?_
    · apply (mul_le_mul_of_nonneg_left (show (meter _:ℝ) ≤ (N+1:ℕ)*(meter x+(meter y:ℝ)+(size w:ℝ)) by exact_mod_cast hardP (x:=x) (i:=p) (j:=q) (hB.length j) w) hp).trans; rw [← mul_assoc]; gcongr
    simp_rw [mul_add,Real.exp_add]; ring
 let t u v:= T*u*v; let C' (i j) := (N:ℝ)*t (U.price a i) (V.price a j)
 refine ⟨fun ⟨i,j,p,q,w⟩=> hardL (hA.length _) (hB.length _) w,sumBudget_sigma (a:=l) (fun i=>sumBudget_sigma (a:=fun j=> (k:ℝ)*C' i j) (fun j=> ?_) ?_) ?_⟩
 · let f:=t (U.price a i) (V.price a j); have hw:0≤f:=mul_nonneg (mul_nonneg ht (U.price_nonneg ..)) (V.price_nonneg ..)
   have hg(u n:ℕ)(y:ℝ)(hx:0≤y)(hy:u≤n): SumBudget (fun (_:Fin u)=>y) ((n:ℝ)*y):= budget_finite (fun _=> hx) (by simpa using mul_le_mul_of_nonneg_right (show (u:ℝ)≤n from Nat.cast_le.mpr hy) hx)
   exact sumBudget_sigma (a:=fun p=>C' i j) (fun p=> sumBudget_sigma (a:=fun q=>f) (fun q=>he i j p q) (hg _ _ _ hw (hB.length _))) (hg _ _ _ (show 0≤ (N:ℝ)*f by positivity) (hA.length _))
 · have hz:= budget_scale (f:=V.price a) (show 0≤ T*U.price a i from mul_nonneg ht (U.price_nonneg ..)) hB.pay; have hp:= budget_scale (Nat.cast_nonneg (α:=ℝ) k) (budget_scale (Nat.cast_nonneg (α:=ℝ) N) hz); apply budget_loosen hp; unfold l; ring_nf; rfl
 unfold l; rw [← mul_assoc (N:ℝ)]; exact budget_scale (show 0 ≤ (k:ℝ)*(N*T*D) from (by have h:= hB.nonneg; positivity)) hA.pay
end Method
end YM.AllOrder.Ink
