import YM.AllOrder.Ink.Drive
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Ink
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function Fire Laplace.SigmaP Ker
open Progress.ClassicalKin Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial Response
open scoped BigOperators Topology Classical ContDiff
variable {n m:Side} {α β : Type} [Fintype α] [Fintype β] {k N M:ℕ} {a C D b:ℝ}
namespace Field
variable (U V:Field α) (f g:Cover)
omit [Fintype α] [Fintype β]
def plain (r:ℝ)(S:Slip (Point α)) : Field α:= ⟨Unit,fun _=>r,fun _=> S⟩
lemma wordy (r:ℝ)(S:Slip (Point α)): (plain r S).Good a (Real.exp (a*meter S)* |r|) S.length:= ⟨fun _=>le_rfl,by change SumBudget (fun _:Unit=> _) _; refine ⟨fun i=> mul_nonneg (Real.exp_pos _).le (abs_nonneg _),Summable.of_finite,?_⟩; rw [tsum_fintype,Fintype.sum_unique]; exact le_rfl⟩
lemma plain_site (r:ℝ)(S: Slip (Point α))(z:Site n):(plain r S).site n z= r • invoice z S:= by ext1 i; unfold site; change ∑' j:Unit,_=_; rw [tsum_fintype,Fintype.sum_unique]; rfl
lemma scale_site (U:Field α)(t:ℝ)(z: Site n): (U.scale t).site n z=t• U.site n z:= by ext1 i; simp only [scale,site,Pi.smul_apply,smul_eq_mul,mul_assoc, tsum_mul_left]
/-- Multiplication **at the anchoring site**; not TABLE. -/
def jointB (U V:Field α): Field α where
 Ty:= U.Ty × V.Ty
 fee i:= U.fee i.1*V.fee i.2
 slip i:= U.slip i.1 ++ V.slip i.2
lemma mates (H:U.Good a C k)(h:V.Good a D N) : (jointB U V).Good a (C*D) (k+N) := by
 let A:= jointB U V; refine ⟨fun i=> List.length_append.trans_le (Nat.add_le_add (H.length _) (h.length _)),?_⟩; let f i:= U.price a i; let g i:= V.price a i; rw [show A.price a=(fun i:U.Ty×V.Ty=> f i.1*g i.2) from funext (fun i=> by simp only [A,f,g,Field.price,jointB, meter_add,Nat.cast_add,mul_add,Real.exp_add,abs_mul]; ring)]; exact budget_prod H.pay h.pay
end Field
namespace Field
lemma mate_site (U V:Field α) (H:U.Good a C k)(h:V.Good a D N)(ha:0≤a)(z:Site n): (jointB U V).site n z=U.site n z * V.site n z:= by ext1 i; let f(p:U.Ty):= U.fee p*invoice z (U.slip p) i; let g(p:V.Ty):= V.fee p*invoice z (V.slip p) i; change (∑' j:(jointB U V).Ty,_)=(∑' p,f p)* ∑' p,g p; erw [← tsum_mul_right, ((mates U V H h).total ha z i).tsum_prod]; apply tsum_congr; intro p; rw [← tsum_mul_left]; refine tsum_congr fun q=> ?_; change U.fee p*V.fee q*invoice z _ i=_; rw [show invoice z ((jointB U V).slip (p,q)) =_ from invoice_add z (U.slip p) (V.slip q),Pi.mul_apply]; unfold f g; ring
end Field
namespace Method
open Field
variable (A:Stalk α β) (H: Belt A a C) (u:Point α) (x: rule β n) (z: Site n) (ha : 0≤a) (hc:0≤C)
def know (A:Stalk α β)(n:Side): rule β n →L[ℝ] rule α n:= LinearMap.toContinuousLinearMap ((direct A n).mulVecLin)
-- maybe mulVecLin type binder

def trailer (A:Stalk α β) (u:Point α)(p:Point β):= A u.2 p.2 p.1
-- offset convention

def stepL (A:Stalk α β)(u:Point α): Field β where
  Ty:= (_j:β)× Cover -- Sigma? yes
  fee i:= A u.2 i.1 i.2
  slip i:= [(u.1+i.2, i.1)]
omit [Fintype α]
include H ha hc
lemma knob : (stepL A u).Good a ((Fintype.card β:ℝ)*(Real.exp (a*size u.1)*C)) 1 := by
 let f:=stepL A u; refine ⟨fun _=>le_rfl,sumBudget_sigma (a:=fun j=>Real.exp (a*size u.1)*C) (fun j=> ?_) (budget_finite (fun i=>by positivity) (by simp))⟩
 apply budget_mono (budget_scale (Real.exp_pos _).le (H u.2 j)); · exact fun i=> f.price_nonneg ..
 intro i; change Real.exp (a*meter [(u.1+i,j)])* |A u.2 j i| ≤ _; rw [← mul_assoc (Real.exp _),← Real.exp_add]; simp only [meter,List.map_cons,List.map_nil, List.sum_cons,List.sum_nil,add_zero]; apply mul_le_mul_of_nonneg_right _ (abs_nonneg _); apply Real.exp_monotone; rw [← mul_add]; exact mul_le_mul_of_nonneg_left (by exact_mod_cast size_add u.1 i) ha
end Method
end YM.AllOrder.Ink
