import YM.FVAAlt2.Fixed
/-! Multilinear conversion layer for the independent top regulator.
Allows arbitrary spacing-growing powers in triangular change; all calculations
at each regulator are exact (not limits). -/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2.Billing
open MS MS.Koszul MS.Native MS.Native.Wilsonian MS.Native.Studio MS.Book MS.Cylinder MS.Cylinder.Taylor MS.Cylinder.Lab MS.Puff MS.Puff.Actors MS.Swirl MS.Puff.Mom Swirl.Near MS.Fleet
open MS.Orbit MS.Orbit.LogReal MS.Orbit.Cog Convolve Program
open Function Finset Filter Topology MeasureTheory Lattice SchemeRG11.Sway SchemeRG11.Sway.Lam
open Precision Ends AtomCert
open scoped PowerSeries ContDiff
variable {J S E I L:Type}
section
variable [AddCommGroup J][Module ℂ J][AddCommGroup E][Module ℂ E][AddCommGroup I][Module ℂ I]
local notation "Z"=> PowerSeries ℂ
def scalS (z:Z) (X:T E):=pairW (LinearMap.lsmul ℂ E) (unpack z) X
lemma scal_comm (M:E→ₗ[ℂ] J)(X:T E)(z:Z): promote M (scalS z X)=scalS z (promote M X):=by funext i; simp_rw [promised,scalS,paired]; simp only [promised,map_sum,LinearMap.lsmul_apply,map_smul]
lemma pair_mul (f:E→ₗ[ℂ]J→ₗ[ℂ] I)(U:T E)(V:T J)(z:Z): pairW f U (scalS z V)=scalS z (pairW f U V):= MS.Menus.olio .. -- name

variable {p:Sector S}
abbrev formScale(p:Sector S):PowerSeries ℂ→+* PowerSeries (Com p):= PowerSeries.map (algebraMap ℂ (Com p))
lemma forget_R (z:Z)(x:PowerSeries (Com p)) : Com.forget p (formScale p z * x)=scalS z (Com.forget p x):= by
  funext i; rw [Com.forget_at,PowerSeries.coeff_mul,Submodule.coe_sum]; refine sum_congr rfl fun j _=>?_ ; rw [formScale,PowerSeries.coeff_map,Com.alg_piece, Com.piece_mul];rfl

def s4 (p:Sector S)(c:Z)(x:PowerSeries (Com p)) := PowerSeries.mk (substitute c (fun i=>PowerSeries.coeff i x))
lemma s4_forget(c:Z)(x:PowerSeries (Com p)): Com.forget p (s4 p c x)=substitute c (Com.forget p x):= by funext i; simp_rw [s4,Com.forget_at,PowerSeries.coeff_mk,rules,Submodule.coe_sum]; rfl

variable [Fintype S]{K:Matrix S S ℂ}{U:SpecB S}
lemma end_smul{F: SpecB S}{x:Z}(z:Z)(hf:Endμ K p U F (unpack x)): Endμ K p U (scalS z F) (unpack (z*x)):= by
 unfold Endμ; change ℶV K (pairW (product p) (exp0 p U) _) =_; rw [pair_mul, show ℶV K (scalS z _)=_ from scal_comm (View K) _ z,show unpack (z*x)=_ from unpack_mul z x]; -- check transform support
 change scalS z (ℶV K ((PermV p).core (exp0 p U) F)) = _
 rw [hf]; have hz(x y:T ℂ):Trunk.core x y=pairW (Algebra.lmul ℂ ℂ).toLinearMap x y:= rfl; have hb:Trunk.core (unpack z) (unpack x)=scalS z (unpack x):= rfl; rw [hb,hz,hz]; exact Eq.symm (pair_mul (Algebra.lmul ℂ ℂ).toLinearMap (ℶV K (exp0 p U)) (unpack x) z)
lemma end_sum
 (f:L→ SpecB S)(X:L→Z)(s:Finset L)(H:∀ i∈s,Endμ K p U (f i) (unpack (X i))): Endμ K p U (∑ i∈s,f i) (unpack (∑ i∈s,X i)):= by
 unfold Endμ; rw [ show unpack _= ∑ i∈s,unpack (X i) from funext fun n=> by unfold unpack; rw [map_sum,Finset.sum_apply] ]; simp_rw [map_sum]; exact Finset.sum_congr rfl fun i hi=> H i hi
end
end YM.FVAAlt2.Billing
