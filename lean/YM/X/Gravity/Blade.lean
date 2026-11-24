import YM.X.Local.Oar
import YM.X.Grow.GaugeJet
/-!
# Remote gradient prices separate modulo actual curvature shell lift on open Book space.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Gravity
open Lattice Wilson Next.Rank Normal Interval PertExtension LatticePT Filter Set Function Metric MeasureTheory Asymptotics Reed Size Braid
open MvPolynomial Hinge Clove Haze Grow Shelf Ocean Fielding Crystal Perch LiftMark
open Stems hiding X
open scoped Topology ContDiff BigOperators Classical
variable {q: ℕ+}(hq:1<q.val){V:Type*}{k m n d l:ℕ}{G:Gauge}{R r:ℝ}
local notation "X"=>MvPolynomial.X
local notation "K"=> Book G
def inkB (y:Long G) (i: Valves G):ℂ:= ((owns (Okay G) i.1).coord i.2 (y i.1):ℂ)
def torch (y:Long G) := slit (inkB y)
variable (A:Okay G k) (x y: Long G)
lemma ink (i: Valves G)(z:ℝ): inkB (x+ z • y) i= inkB x i+ z • inkB y i:= by unfold inkB; simp only [Pi.add_apply, map_add,Complex.ofReal_add, map_smul,Pi.smul_apply,smul_eq_mul,Complex.ofReal_mul];rfl
lemma candles (p:Book G)(z:ℝ): HasDerivAt (fun z:ℝ=> probeL (x+ z • y) p) (probeL (x+z • y) (torch y p)) z:= by
    induction p using MvPolynomial.induction_on with
    | C a=>simp only [torch,slit_C,map_zero,probeL,aeval_C];exact hasDerivAt_const z _
    | add a b u t=>simp only [map_add]; exact u.add t
    | mul_X p i ih=>
       have h (x:Long G): probeL x (X i)=inkB x i:= by simp [probeL,inkB]
       rw [mul_comm p]; have he: HasDerivAt (fun z:ℝ=> inkB (x+z • y) i) (inkB y i) z:= by simp_rw [ink x y i]; simpa only [one_smul] using ((hasDerivAt_id' z).smul_const (inkB y i)).const_add (inkB x i)
       unfold torch; simp_rw [map_mul,h,slit_prod,map_add,map_mul,h, show ∀(x:Long G) (z:ℂ), probeL x (C z) = z from fun x z=> (probeL x).commutes _]; exact ((he.mul ih).congr_deriv (add_comm ..)) -- simp odd

def backP (x: Long G):Long G:= fun i=> rightCur i (x i)
def stepP (A: Okay G k): Long G:= Pi.single k (A-rightCur k A)
def testP (A:Okay G k):= torch (stepP A)
lemma torch_zero (p:Book G): torch 0 p=0:= by rw [torch,show inkB (0:Long G)=0 from funext fun i=> by unfold inkB;rw [Pi.zero_apply,map_zero,Complex.ofReal_zero];rfl]; apply slit_zero
lemma torch_add (p:Book G): torch (x+y) p= torch x p+torch y p:= by unfold torch; rw [show inkB (x+y)= inkB x+inkB y from funext (fun i=>by simp [inkB])]; exact slit_linear ..
lemma sums_torch {I:Type*}(s:Finset I)(f:I→Long G)(p:Book G) : torch (∑ i∈s,f i) p= ∑ i∈s,torch (f i) p := by induction s using Finset.induction_on with| empty=> rw [Finset.sum_empty,Finset.sum_empty,torch_zero]| insert i s hi ih=> rw [Finset.sum_insert hi,Finset.sum_insert hi,torch_add,ih]
def wand (x: Long G)(p:Book G) : Long G:= ∑ i∈(p.vars.image Sigma.fst), stepP (x i)
lemma one_wand (p:Book G): torch (wand x p) p= torch (x-backP x) p:= by
    apply derivation_eq_of_forall_mem_vars; intro y hy; rw [torch,torch,slit_X,slit_X]; let l:ℕ:= y.1; let f:= wand x p; let g:=x-backP x;
    have he : f l=g l:= by
       have hx:l∈ p.vars.image Sigma.fst:= Finset.mem_image_of_mem Sigma.fst hy
       unfold f wand; rw [Finset.sum_apply, Finset.sum_eq_single_of_mem l hx]; exact Pi.single_eq_same .. -- name
       intro i _ hi; rw [stepP,Pi.single_eq_of_ne hi.symm] -- name
    unfold inkB; exact congr_arg _ (congr_arg Complex.ofReal (congr_arg ((owns (Okay G) y.1).coord y.2) he))
set_option maxHeartbeats 600000 in
lemma fixed_for (p:Book G)(h:∀ n:ℕ,∀ A:Okay G n, testP A p=0): localMap (E:=Okay G) rightCur p=p:= by
    apply probe_ext; intro x; let y:=backP x; let F(z:ℝ):=probeL (y+z • (x-y)) p; change _=_; rw [probe_map];
    have he : torch (x-y) p=0:= by unfold y; rw [←one_wand,wand,sums_torch]; exact Finset.sum_eq_zero fun i _=> h i _
    have hx(a:ℝ): HasDerivAt F 0 a:=by have hx:= candles y (x-y) p a; rw [he,map_zero] at hx; exact hx
    have hp : F 0=F 1:= is_const_of_deriv_eq_zero (fun x=> (hx x).differentiableAt) (fun x=>(hx x).deriv) 0 1; -- line break 
    simp only [F,zero_smul,one_smul,add_zero, add_sub_cancel] at hp; rw [show y+(x-y)=x by abel] at hp; exact hp
lemma flat_back (t:Okay G k): rightCur k (rightCur k t)=rightCur k t:= by cases k with | zero=> rfl| succ k=> simp_rw [rightCur,LinearMap.comp_apply,shelve_slip]
lemma quiet : backP (stepP A)=0:= by
   funext i; by_cases hp:i=k
   · subst i; change rightCur k (stepP A k)=(0:Okay G k); rw [show stepP A k=A-rightCur k A from Pi.single_eq_same ..,show rightCur k (A-rightCur k A) = _ from map_sub (rightCur k) A _,flat_back,sub_self]
   unfold backP; change rightCur i (stepP A i)=(0:Okay G i); rw [show stepP A i=(0:Okay G i) from Pi.single_eq_of_ne hp _, map_zero];
lemma local_shift (v:ℝ)(z:Long G): backP (z+v • stepP A)=backP z:= by funext i; unfold backP; simp only [Pi.smul_apply,Pi.add_apply,map_add,map_smul, show rightCur i (stepP A i)=(0: Okay G i) from congr_fun (quiet A) i, smul_zero,add_zero]
lemma testP_local (p:Book G) : testP A (localMap (E:=Okay G) rightCur p)=0:= by
   apply probe_ext; intro z; let F:= localMap (E:=Okay G) rightCur p; have he : HasDerivAt (fun t:ℝ=>probeL (z+t • stepP A) F) (probeL z (testP A F)) 0:= by simpa only [testP, zero_smul,add_zero] using candles z (stepP A) F 0
   have hp (t:ℝ) : probeL (z+t • stepP A) F=probeL (backP z) p:= (probe_map ..).trans (congr_arg (fun y=>probeL y p) (local_shift A t z))
   rw [map_zero]; simp_rw [hp] at he; exact he.unique (hasDerivAt_const ..)
end YM.PositionX.Gravity
