import YM.AllOrder.Haiku.Origin
import YM.AllOrder.Ink.Render
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Haiku
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function Fire Laplace Laplace.SigmaP Ker
open Progress.ClassicalKin Progress.ClassicalKin.Tent Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Response Ink Ink.Method Ink.Money
open Tree Wilson Exterior Precision Push Pressure Next.Fluctuations MeasureTheory
open Stationary
open scoped BigOperators Topology Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge} {n m c:Side}{a C D:ℝ}{k N:ℕ} {ι:Type}
local notation "L"=> Coarse G
-- defeq Ward.Link footing
local notation "F[" n "]"=> Stationary.Link G n

namespace Revenue
open Bloch
section bank
variable {α:Type} [Fintype α][DecidableEq α]
local notation "P"=> Phase (Leaf n α)
lemma sheet (u:Page (Leaf n α) (k+1))(v:Fin (k+1) → Phase (Leaf n α)): enlarge u.toMultilinearMap v= ∑ i:Leaf n α,v 0 i * drive (darken (extractF u)) (Fin.tail v) i:= by
 classical
 unfold enlarge; rw [recording_apply,← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (k+1)=>Leaf n α)),Fintype.sum_prod_type]; refine Finset.sum_congr rfl fun i _=> ?_; unfold drive; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _=> ?_; rw [Fin.prod_univ_succ,mul_assoc]; apply congr_arg (v 0 i *·); rw [mul_comm]; refine congr_arg (fun x:ℝ=> (x:ℂ)*∏ y:Fin k, v y.succ (j y)) ?_; refine congr_arg u (funext fun z=>?_); ext1 y; simp [spot,Pi.single_apply, Fin.consEquiv]
lemma picks (F:FrameCoeffs ι α k ℂ)(i : Fin k→α)(z:ι): drive F (fun j=>Pi.single (i j) 1) z=F z i:= by
 unfold drive; rw [Finset.sum_eq_single i]; · simp
 · intro b hb hh; obtain ⟨l,hl⟩:=(Function.ne_iff.mp hh); rw [Finset.prod_eq_zero (mem_univ l),mul_zero]; simp [hl]
 simp

variable (F:Fan α α k)(h:Cap F a C)(h0:0≤a)
def featuristic (F: Fan α α k)(i:Fin (k+1) → α)(p: Space k):ℂ:= readable (F (i 0) (Fin.tail i)) p
include h h0
lemma acted (v: Fin (k+1)→Site n)(i:Fin (k+1)→α)(u:Page (Leaf n α) (k+1))(hx: extractF u=pieces F n):
 enlarge u.toMultilinearMap (fun l=>relay (v l) (i l)) = if ∑ j,v j=0 then (Fintype.card (Site n):ℂ)*featuristic F i (outphase v) else 0:= by
 let g:= Fin.tail v; let b:=Fin.tail i; let s:= (v 0); let V(l:Fin (k+1)):= relay (v l) (i l); let t:=∑ j:Fin k,g j; let f(j:Fin k):α→ℂ:=Pi.single (b j) 1; let F':= colors F (mon ∘ g)
 rw [sheet,hx, show Fin.tail V=(fun j:Fin k=> Primitives.TwoWave.ray (g j) (f j)) from rfl, fan_route h h0 g f, Fintype.sum_prod_type];
 have hu(x:Site n)(p:α): V 0 (x,p)=cell s x*(if p=i 0 then 1 else 0):= by unfold V relay tune s; simp only [Pi.single_apply]
 let A:= featuristic F i (outphase v); have ha: F' (i 0) b= A:=rfl; have ht : ∑ j,v j=s+t:= by rw [Fin.sum_univ_succ]; rfl
 change (∑ j:Site n,∑ q:α,V 0 (j,q)*(cell t j * drive F' f q))= _; simp_rw [hu,mul_ite,mul_one,mul_zero,ite_mul,zero_mul,sum_ite_eq',Finset.mem_univ,if_true]; rw [picks,ha,ht]; simp_rw [←mul_assoc,← Finset.sum_mul];
 have he(j:Site n): cell s j*cell t j= cell (s+t) j:= by rw [cell_duality s,cell_duality t,cell_duality (s+t),cell_add]
 simp_rw [he]; split
 · rename_i hv; simp [hv,cell,A]
 rename_i hv; rw [sum_cell hv,zero_mul]
end bank
section pict
variable (F: Ink.Field (Coarse G))(T:Fan (Coarse G) (Coarse G) k)
def coinT (f:Fan (Coarse G) (Coarse G) k) : Picture G k:= fun i z p=> (↑(Nat.factorial (k+1)):ℂ)⁻¹*featuristic f (fun j=>((z j,i j):Coarse G)) p
lemma coin_record {f:Link G n→ℝ} (H: extractF (iteratedFDeriv ℝ (k+1) f 0)=pieces T n)(ha:0≤a) (ht:Cap T a C) : Recorded (coinT T) f 0:= by
 intro p i b; have hh:= acted T ht ha p (fun j=> ((b j,i j):Coarse G)) _ H; rw [noteAt,_root_.smul_apply]; unfold beat Stationary.glyph; erw [hh]; unfold collected coinT; split
 · rw [smul_eq_mul,mul_left_comm]; simp -- eh
 simp
lemma rent_coin {N:ℕ}{a C:ℝ} (h:F.Good a C k)(ha:0<a) : let s:= weaker (N+1) (Rail.widthG a (N+1)); let t:= Rail.gift k C a (N+1); ∃ f:Picture G N,(∀ i j,Firm (small_a s) (‖(↑(Nat.factorial (N+1)):ℂ)⁻¹‖ *(t*boltC N s)) (f i j))∧ ∀ n, Recorded f (Ink.Field.table F n) 0:= by
 obtain ⟨F',hF,hv⟩:= Rail.endless F h ha N; intro s t; have he:0<s:=Rail.shorter F h ha _; have hk:0<small_a s:=div_pos he (by norm_num); refine ⟨coinT F',fun i j=>(Firm.const hk ((↑(Nat.factorial (N+1)):ℂ)⁻¹)).mul (Firm.of_series (hF.prom ..) hk),fun n=> ?_⟩; exact coin_record F' (hv n) hk.le hF
end pict
end Revenue
end YM.AllOrder.Haiku
