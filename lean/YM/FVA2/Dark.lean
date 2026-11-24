import YM.FVA2.Plug
import YM.MS.Theater.RakeA
import YM.MS.Theater.Well
import YangMills.WilsonProof.NativeSupport.YM.MS.Local.Curls
import YM.MS.Theater.Life
import YM.MS.Theater.Eq
import YM.MS.Theater.Radium
import YM.MS.Theater.Pave
import YM.MS.Theater.Scale
import YM.MS.Theater.Seat
import YangMills.WilsonProof.NativeSupport.YM.MS.Local.Labels
import YangMills.WilsonProof.NativeSupport.YM.MS.Local.Fac
import YM.MS.Swirl.Dry

/-!
# Coordinate conventions for Endμ super-power-series

Bundle the *even part* with the proved commutative multiplication to use
mathlib algebra (`Π` and determinants) at each perturbative problem.
`atLetter` with an exterior slot name is odd: it is **not** represented
by this auxiliary type. Only pairs will be mapped back to `SpecB` via it.
No rank hypothesis hidden; enforce rank per row on descent.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Paper
open Filter Set
open MS MS.Koszul MS.Plane MS.Swirl MS.Orbit MS.Orbit.Cog MS.Orbit.LogReal MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Engine MS.Puff.SplitP MS.Puff.Actors MS.Puff.Mom MS.Cylinder MS.Cylinder.Lab MS.Theater Finset PowerSeries
open scoped Topology Classical
variable {A:Type} {p:Sector A}

abbrev Price (p:Sector A):= PowerSeries (Dark p)

def track (p: Sector A): Price p →ₗ[ℂ] SpecB A where
   toFun f i:= ↑(coeff i f)
   map_add' f g:= by ext1 i; rw [map_add]; rfl
   map_smul' c f:= by ext1 i; rw [coeff_smul]; rfl
lemma tracking (f:Price p)(i:ℕ): track p f i=(coeff i f).val:=rfl
lemma rack : Function.Injective (track p) := fun _ _ h=> PowerSeries.ext fun i=> Subtype.ext (congr_fun h i)
lemma track_even (f:Price p) (i:ℕ): track p f i∈ (actor p).guard:= (coeff i f).property
lemma track_full (f:Price p): track p f∈(PermV p).guard:= fun i _=>track_even f i
lemma pair (f g:Price p): track p (f*g)=(PermV p).core (track p f) (track p g):= by
  ext1 i; rw [tracking,coeff_mul]; change _=∑ x∈ antidiagonal i, product p _ _
  exact map_sum (Dark p).subtype _ _
lemma track_one : track p 1=(PermV p).unit:= by
  ext1 i; rw [tracking,coeff_one]; cases i with | zero=> rw [if_pos rfl]; exact Eq.symm (lone_use (coin 1)) | succ i=> rw [if_neg (Nat.succ_ne_zero i)]; change (0:BL A)=useN.refineV (coin 1) (i+1); unfold SplitP.refineV; rw [if_neg (show i+1 ≠ useN.origin from Nat.succ_ne_zero i)]

abbrev rex (x:Price p)(i:ℕ) := ∑ j∈range (i+1), (Actors.phase j) • x^j

def exp (x:Price p): Price p:= mk fun i=> coeff i (rex x i)

lemma exp_tracks (f:Price p) : track p (exp f)=exp0 p (track p f):= by
  have h (i:ℕ) : (PermV p).power (track p f) i=track p (f^i):= by
    induction i with
    | zero=> rw [pow_zero,track_one,Actors.power]
    | succ i ih=> rw [Actors.power, ih, ← pair,pow_succ']
  funext i; rw [tracking,Paper.exp,coeff_mk,← tracking]; change _=(PermV p).cheers _ i i; unfold rex Actors.cheers Actors.wages; simp_rw [ map_sum,h, map_smul]
lemma exp_one (f:Price p) : coeff 0 (exp f)=1:= by simp [Paper.exp,rex,Actors.phase]

lemma exp_add (a b:Price p) (ha:coeff 0 a=0)(hb:coeff 0 b=0): exp (a+b)=exp a * exp b:= by
   apply rack; rw [exp_tracks,map_add,pair,exp_tracks,exp_tracks]; exact cheer_a (track_full a) (track_full b) (by change (coeff 0 a).val=0; rw [ha]; rfl) (by change (coeff 0 b).val=0; rw [hb]; rfl)
lemma exp_sink (a:Price p)(h0:coeff 0 a=0)(h:a*a=0): exp a=1+a:= by
   have hv (k:ℕ) : a^(k+2)=0:= by rw [pow_succ,pow_succ,mul_assoc,h,mul_zero];
   apply PowerSeries.ext; intro k; rw [Paper.exp,coeff_mk,map_add,coeff_one]; rcases k with _|k; · simp [rex,h0,Actors.phase]; -- may duplicate cast
   rw [if_neg (Nat.succ_ne_zero _),zero_add]; unfold rex; rw [map_sum, Finset.sum_range_succ', Finset.sum_range_succ'];
   have he i: coeff (k+1) ( Actors.phase (i+1+1) • a^(i+1+1)) = 0:= by rw [hv,smul_zero,map_zero]
   simp [he,Actors.phase] -- actor type cast S? inspect
@[simp] lemma exp_zero : exp (0:Price p)=1:= by rw [exp_sink 0 (map_zero _) (mul_zero _),add_zero]

lemma trackC_mul (f: Dark p) (x:Price p) (i:ℕ) : track p (PowerSeries.C f*x) i=product p f.val (track p x i):= by rw [tracking,coeff_C_mul]; rfl

-- when used, Γ = Symm & Finite per-degree scalar.Vacuous outside generators. Check every row.
abbrev Bound (f:Price p): Prop:= Γ (track p f) p
lemma bound_zero: Bound (0:Price p):= by rw [Bound,map_zero]; exact (allIndex _ _).zero_mem
lemma bound_add {f g:Price p}(h:Bound f)(hp:Bound g): Bound (f+g):= by rw [Bound,map_add]; exact (allIndex _ _).add_mem h hp
lemma bound_sub {f g:Price p}(h:Bound f)(hp:Bound g): Bound (f-g):= by rw [Bound,map_sub]; exact (allIndex (FeeP p) ℕ).sub_mem h hp
lemma bound_one : Bound (1:Price p):= by rw [Bound,track_one]; exact refineπ useN (coin 1) feeUnit
lemma bound_C (x: Dark p)(hp:x.val∈FeeP p): Bound (C x):= by intro i _; rw [tracking,coeff_C]; split; exact hp; exact (FeeP p).zero_mem
lemma bound_exponential {x:Price p}(hx:Bound x): Bound (exp x):= by rw [Bound,exp_tracks]; exact expΓ hx
lemma bound_pair {x y:Price p}(hx:Bound x)(hy:Bound y): Bound (x*y):= by rw [Bound,pair]; exact ΤΓ_pair hx hy
lemma bound_sum {I:Type*} (S:Finset I)(f:I→Price p)(h:∀ i∈S,Bound (f i)): Bound (∑ i∈S,f i):= by rw [Bound,map_sum]; exact (allIndex _ _).sum_mem h
lemma bound_prod {I:Type*}(S:Finset I)(f:I→Price p)(h:∀ i∈S,Bound (f i)): Bound (∏ i∈S,f i):= by
   induction S using Finset.induction_on with
   | empty=> rw [Finset.prod_empty]; exact bound_one
   | insert i s hi ih=> rw [Finset.prod_insert hi]; exact bound_pair (h i (by simp)) (ih (fun j hj=> h j (by simp [hj])))
end YM.FVA2.Paper
