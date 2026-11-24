import YM.OPE.Compatible.Streams.Epic
/-! # Transition driver. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Hark
open Function Filter Set ContinuousLinearMap
open scoped Topology BigOperators Classical
variable {d k i j m s:ℕ}{E:Fin s→Type}{G:ℕ→Type}[∀ i,NormedAddCommGroup (E i)][∀ i,NormedSpace ℝ (E i)] [∀ i,NormedAddCommGroup (G i)] [∀ i,NormedSpace ℝ (G i)]
variable {b x v u:ℝ}{μ:ℕ→ℝ}
local notation "S!"=> Mints E
local notation "L!"=> S! →L[ℝ] S!
variable {T:∀ i: Fin s,Cuts d μ v b (E i) G}
open Drift
variable {X:Mints E→L[ℝ] Mints E}{V W:Type}{w':V→ℝ}
-- comm for recap plus shift.
lemma liftK' (Iq:S!→L[ℝ] S!)(ht:Iq * X=X*Iq):
    Iq*(X^m)= (X^m)*Iq:= (show Commute Iq X from ht).pow_right m |>.eq
lemma shiftsA {q:ℝ}(hp:0 < q) (P:S!→L[ℝ] S!)(h:P*X=X*P)(v:Fruition X q) :
     (Fleet X q s hp ^m) (Fellow P X q h v)=Fellow P X q h ((Fleet X q s hp ^m) v):=by
         let T:= portC X q s^m; let A:=Fleet X q s hp^m; let F:= Fellow P X q h; have ht(x):A (T x)=x:= DFunLike.congr_fun (bolt (X:=X) (μ:=fun _=>q) (k:=0) hp).1 x; have ha(x):T (A x)=x:= DFunLike.congr_fun (bolt (X:=X) (μ:=fun _=>q) (k:=0) hp).2 x
         have hc(x):T (F x)=F (T x):=by
              refine Subtype.ext ?_; unfold T; rw [portables]; change _= P ((portC X q s^m) x).val; rw [portables]; exact DFunLike.congr_fun (liftK' P h (m:=m)).symm x.val
         change A (F v)=F (A v); apply (show LeftInverse A T from ht).injective; rw [ha,hc, ha]
-- Power comparison.T fixed F normalized
lemma powerB (X:Mints E→L[ℝ] Mints E)(q:ℝ)(hp:0< q) (v:Fruition X q): (portC X q s^(i+j)) ((Fleet X q s hp ^j) v)=(portC X q s^i) v:=by rw [pow_add,byway]; let T:= Fleet X q s hp; let U:=portC X q s; change (U^i) ((U^j) ((T^j) v))= (U^i) v; rw [show (U^j) ((T^j) v)=_ from (show (U^j) ((T^j) v)=v from DFunLike.congr_fun (bolt (X:=X) (μ:=fun _=>q) (k:=0) hp (i:=j)|>.2) v)] -- pattern U
-- weakened preservation recurrence
variable (A:V→Mints E→L[ℝ] Mints E)
lemma Aeon.March.ofSlope (h:∀ z, Edgewise (A z))(hp:∀ (z:V)(n:ℕ)(i:Fin s)(_hn:n<d)(v:Mints E)(_ht:trims i.val v),v i∈ (T i).flag n → (T i).Tap n (A z v i)= (μ n)^m • (T i).Tap n (v i)): Aeon.March T A m:=by
       refine ⟨h,fun i j k hj v hz=> ?_,fun i j k hj v hz he=>hp k j i hj v hz he⟩; induction j with
       | zero=> exact iff_of_true ((T i).first _) ((T i).first _)
       | succ n ih=> rw [(T i).next n hj,(T i).next n hj,ih (Nat.le_of_lt hj)]; apply and_congr_right; intro hx; rw [hp k n i hj _ hz hx, smul_eq_zero_iff_right (pow_pos ((T i).tempo n hj) _|>.ne')]
end YM.OPE.Hark
