import YM.AllOrder.Kinetic.Lily
import YM.Extra.ITERATION_NO_LOSS.TermNorm
/-!
# Exact period transfer of a marked *unmasked input vertex* via its real frame
 Remove global mean shift BEFORE: here keep astronomical Lobby coordinates whose Hessian
 shift will be applied to these jet functions. Geometry bound seeing an atom at this root is
 in COARSE distances, so polynomially finite aperture length (even for winding marks) and
 pays before-L widths after moving. Our carry_le proof allows *full L* improvement not just
 a width which could never be used again at the next physical ratio. Keep cost of TRUE kernel
 length even in spectral tall auxiliary. Real evaluation outside visible order p used here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Sunrise.Campus
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function AllOrder AllOrder.Fire AllOrder.Laplace AllOrder.Laplace.SigmaP AllOrder.Ker AllOrder.Ker.Start
open Progress.ClassicalKin Progress.ClassicalKin.Tent Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial Response AllOrder.Ink AllOrder.Ink.Method GaussianScore Module
open Tree Wilson PhysicalNext Repeat Lapis ConnectedActivityE6 Blaze Precision Push Pressure Next.Fluctuations Next.SectorChange MeasureTheory
open scoped BigOperators Topology Classical ContDiff Matrix.Norms.Frobenius
open Work.F08
open Kinetic.Port
variable {G:Gauge}{n m:Side} {a k l :ℕ} (P:Patch) (K:KernelChoices)
local notation "T[" n "]" => trees P K n
local notation "S[" n "]" => dock P K n
local notation "X[" n "]"=> Positions (Primary n G)
local notation "J"=> RealSlice.Vertical G P K
local notation "E"=> Coarse G
local notation "R[" n "]" => Poll.Body (Precision.Key T[n] G)
local notation "N[" n "]" => below P n
local notation "B[" n "]"=> shores P n
local notation "I"=> Lobby P K G
local notation "Λ"=> P.L.val
local notation "I₀"=>Ad G P K
set_option quotPrecheck false
variable (u : Atom G k)(x:Site n)(v:rule (Lobby P K G) n)(hn: Ad G P K n) (hm: Ad G P K m) (p:Site P.L)
local notation "π"=>prom P K G (enough P K hn)
local notation "ξ"=> (π) v
local notation "F" => fine G T[n] (π v)

local notation "pt[" i "]"=> (shores P i).assemble
local notation "y"=> pt[n] (x,p)
lemma step_ne (x : Site n) (a : Axis) (h : 1 < n.val) : x+step a ≠ x := by
  haveI : Fact (1<n.val) := ⟨h⟩
  intro he
  have h' : step a=(0:Site n) := add_eq_left.mp he
  have h : (1:ZMod n.val)=0:= by simpa using congr_fun h' a
  exact one_ne_zero h
local notation "Z"=> (mapper P K G (enough P K hn))
lemma peek (j:Leaf n (I)): ξ (Z j)=v j:=by change v ((Z).symm _) =_ ; congr; exact (Z).symm_apply_apply _ -- note error (Z).symm
-- at block boundary.
private def couleur (G:Gauge)(f:G.ColorIndex→ℝ):G.Color:= WithLp.toLp 2 f
def inherit (t:Axis) (u : Lobby P K G→ℝ) : G.El :=if (lift p t)= (P.L.val/2:ℕ) then G.lieExp (couleur G (fun i=>u (.inl (Exterior.coord t,i)))) else 1
include hn
lemma repCoin (t:Axis): replica (B[n]) (outer G (T[n]) ξ) (y,t)= inherit P K p t (fun i=> v (x,i)):= by
 have hp : Odd Λ:= P.odd_side; let z:=B[n]; change Odd z.count.val at hp
 unfold replica; dsimp only; unfold inherit; rw [Ratio.parents_hop (B[n]) hp, Ratio.assemble_parent,Ratio.assemble_res]
 split_ifs with hu ht _ <;> first | (exfalso; exact step_ne x t (by have := enough P K hn; omega) (by exact ht)) | rfl | contradiction | skip
 rw [outer,Work.F03.represent_link]; refine congr_arg (G.lieExp) ?_; exact PiLp.ext fun i=> peek P K v hn (x,.inl (Exterior.coord t,i)) -- syntax
-- explicit lookup dependent wrap
omit hn
def wet (u : (Lobby P K G)→ℝ) (t:Axis): G.El:= if h: keep P K (p,t) then G.lieExp (couleur G (fun i=>u (.inr (⟨(p,t),h⟩,i)))) * inherit P K p t u else 1
include hn
lemma hit (t:Axis): F (y,t)=wet P K p (fun i=> v (x,i)) t:= by
 unfold wet; split
 next h=>
    let z:=(y,t); have hz : z ∉ (T[n]).trunks := (reserve P K (enough P K hn) x (p,t)).2 h ; let e : (T[n]).Free:= ⟨z,hz⟩
    change F e.val= _; rw [show F e.val= _ from ((T[n]).off_tree _ e)] -- exact lifting exp replica format?
    refine congr_arg₂ (·*·) ?_ (repCoin P K x v hn p t); refine congr_arg _ (PiLp.ext fun i=>?_); exact peek P K v hn (x,.inr (⟨(p,t),h⟩,i))
 next hp=> have hh := reserve P K (enough P K hn) x (p,t); have hz: (y,t)∈(T[n]).trunks := not_not.mp (mt hh.1 hp); exact (T[n]).on_tree _ ⟨_,hz⟩
lemma lookup (q:Cover) (t:Axis): (expandAt y F) (q,t)= wet P K (arrives p q) (fun i=>v (x+wrap n (carry p q),i)) t:=by
 unfold expandAt; dsimp only; rw [add_comm (wrap _ _), moves_site (B[n]), Ratio.assemble_parent,Ratio.assemble_res]; exact hit P K _ v hn (arrives p q) t
-- Sharp coarse reach, not carry_size∼|x|; need amplification for width permanence
omit hn
lemma toll (x:Cover) (R:Side) (p:Site R): R.val * size (carry p x) ≤ size x + 4*R.val:= by
    let n:ℤ:=R.val; have hn:0<n:= Int.natCast_pos.mpr R.pos
    have hf (i:Axis): (R.val:ℕ) * (carry p x i).natAbs ≤ (x i).natAbs+ R.val:=by
       let y2:= lift p i; let z:= lift (arrives p x) i;
       have he : y2+x i= z+n*carry p x i:= by simpa only [y2,z,n,Pi.add_apply,Pi.mul_apply,Pi.smul_apply,nsmul_eq_mul,Pi.natCast_apply] using congrFun (carry_spec p x) i
       have hp : |y2-z| ≤ n:= by rw [abs_sub_le_iff]; have h1: -n < 2*y2 ∧ 2*y2≤ n:= lift_centers p i; have h2: -n<2*z∧2*z≤n:= lift_centers (arrives p x) i; omega
       have hx : n*|carry p x i| ≤ |x i|+n := calc _ = |x i+(y2-z)|:= by rw [show x i+(y2-z)= n* carry p x i from (by omega),abs_mul, abs_of_pos hn]
                                                      _ ≤ _:= (abs_add_le ..).trans (add_le_add_right hp _)
       have hx : ((R.val*(carry p x i).natAbs: ℕ):ℤ) ≤ (↑((x i).natAbs+R.val:ℕ):ℤ):= by push_cast; exact hx 
       exact Int.ofNat_le.mp hx
    unfold size; rw [Finset.mul_sum]; exact (Finset.sum_le_sum (fun i _=>hf i)).trans_eq (by simp [Finset.sum_add_distrib,Axis])
-- Frame embedding finset for proof.Momentum.Vs.Big.Site. keep letters.R.Str
abbrev seatHeight (d:ℕ) := (d+4*P.L.val)/P.L.val
def crew (G:Gauge)(d:ℕ): Finset (Point (Lobby P K G)):= (Lattice.box (Campus.seatHeight P d)) ×ˢ Finset.univ
local notation "W" d:max=> crew P K G d
lemma sitting (d:ℕ) (e:Cover)(h:size e ≤ d)(j:I): (carry p e,j)∈ W d:= by
    have he:= toll e P.L p
    have hP : size (carry p e) ≤ seatHeight P d:=by apply (Nat.le_div_iff_mul_le P.L.pos).2; rw [mul_comm]; omega
    refine Finset.mem_product.mpr ⟨?_,mem_univ _⟩; rw [box_test]
    have hx(i:Axis) : (carry p e i).natAbs≤ Campus.seatHeight P d:= (Finset.single_le_sum (f:=fun j=> (carry p e j).natAbs) (fun j _=>Nat.zero_le _) (mem_univ i)).trans hP; dsimp only; exact ⟨fun i=>by have := hx i; omega,fun i=>by have := hx i; omega⟩
lemma seats (d:ℕ): (W d).card=((2*seatHeight P d+1)^4)*Fintype.card I:=by rw [crew,card_product, ← Fintype.card_coe, Stationary.Audience.portrait_card, card_univ] -- see audience namespace
lemma reserved {d:ℕ} {x:Point (I)} (h:x∈ W d): size x.1 ≤ 4* seatHeight P d:= FreeResolvent.Lifted.fit_box x.1 (seatHeight P d) (mem_product.mp h).1
lemma stand_in (d:ℕ) (hz:8*seatHeight P d<n.val) : Set.InjOn (stood (α:=I) x) (W d):=by
 intro i hi j hj he; have hx : wrap n i.1=wrap n j.1 := add_left_cancel (congr_arg Prod.fst he)
 refine Prod.ext ?_ (show i.2=j.2 from (congr_arg Prod.snd he : (stood x i).2=(stood x j).2)); rw [← FreeResolvent.size_centers _ _ (reserved _ _ hi) (by omega : 2*(4*seatHeight P d) < n.val),← FreeResolvent.size_centers _ _ (reserved _ _ hj) (by omega : 2*(4*seatHeight P d) < n.val), hx]
variable {d:ℕ} (x':Site m)(w:rule (Lobby P K G) m)
abbrev read : rule I n→ℝ := fun v=> u.unmasked (fine G T[n] (π v)) y
include hn hm
lemma aligned (hL:u.length≤d) (h:∀ j∈crew P K G d,v (stood x j)=w (stood x' j)): read P K u x hn p v= read P K u x' hm p w:=by
 apply congr_arg u.poly; ext1 i; apply (u.leg i).covered (expandAt y F) (expandAt (pt[m] (x',p)) (fine G T[m] (prom P K G (enough P K hm) w))); intro e he he'
 have h' := Extra.Iteration.Derivs.stencil_length (u.leg i) _ he; have hh : (u.leg i).length≤ u.length:= (Finset.single_le_sum (f:=fun i=>(u.leg i).length) (fun _ _=>Nat.zero_le _) (mem_univ _))
 rw [lookup (hn:=hn),lookup (hn:=hm)]; apply congr_arg (fun j=> wet P K _ j _ ); exact funext fun i=> h (carry p e.1,i) (sitting P K p d e.1 (h'.trans (hh.trans hL)) i)
end YM.QuadraticLocal.Sunrise.Campus
