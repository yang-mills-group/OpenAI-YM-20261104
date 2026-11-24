import YM.XSpace.FPS
import Mathlib

/-!
# Substitution for field and scale variables (order-by-order ℝ jet algebra).

Here coupling powers import XScale.FPS. No gauge hypotheses or convergence in coupling. Never
construct the matching key from the actual density. `Key` keeps root and reality. Inverse
extends all formulas over junk with old convention `Use`. Position equations inspect only few.
-/
set_option autoImplicit false
noncomputable section
open scoped Topology BigOperators ContDiff Matrix Classical
namespace YM.MS.WilsonBridge.Coupling
open Function Finset Filter MeasureTheory XSpace PowerSeries
variable {G : Type*} {n:ℕ}
abbrev PS := PowerSeries ℂ
abbrev η := starRingEnd ℂ
abbrev RealK (x:PS):= PowerSeries.map η x=x

@[ext]
structure Key where
  knob : PS
  root : constantCoeff knob=0
  real : RealK knob

lemma RealK.sounds {x:PS}(h:∀ n:ℕ, star (coeff n x)=coeff n x):RealK x:= PowerSeries.ext fun n=> ( coeff_map .. ).trans (h n)
lemma RealK.native {x:PS}(h:RealK x)(i:ℕ) : ↑(coeff i x).re= ( coeff i x):=by
   let q:= coeff i x; change (q.re:ℂ)=q; have he : η q=q:= by unfold q; rw [← coeff_map,h ];
   apply Complex.ext; rfl; change (0:ℝ)=q.im; have ht : -q.im=q.im:= congr_arg Complex.im he; linarith
lemma RealK.pow {x:PS}(h:RealK x)(n:ℕ): RealK (x^n):=by unfold RealK; rw [map_pow,h]
namespace Key
variable (a b:Key)
def Id : Key:= ⟨ X,constantCoeff_X, PowerSeries.map_X _ ⟩
lemma has : HasSubst (S:=ℂ) a.knob:= HasSubst.of_constantCoeff_zero' a.root
def applyPS : PS→ₐ[ℂ] PS:= substAlgHom a.has
lemma sent (p:PS): a.applyPS p=p.subst a.knob:= congr_fun (coe_substAlgHom ..) p
lemma realPS (p:PS)(hp:RealK p) : RealK ( a.applyPS p ):=by unfold RealK; rw [sent,FPS.substitute_ringHom η _ a.root,hp, a.real ]
lemma closed (p:PS) : constantCoeff (a.applyPS p)= constantCoeff p:= by
   rw [ ← coeff_zero_eq_constantCoeff_apply, sent, FPS.coeff_substituted _ a.root ]; simp
lemma ready : a.applyPS (X:PS)=a.knob:= (sent ..).trans (subst_X a.has)

-- function composition (`a after b`)
def after : Key:= ⟨ b.applyPS a.knob,( b.closed _ ).trans a.root, b.realPS a.knob a.real ⟩
lemma afterK (p:PS) : (after a b).applyPS p=b.applyPS (a.applyPS p):= by rw [ sent,sent,sent, subst_comp_subst_apply a.has b.has ]; dsimp only [after]; rw [sent]
lemma after_one (p:PS) : Id.applyPS p=p:= (sent ..).trans (X_subst ..)
lemma after_assoc (c:Key) : (a.after b).after c=a.after (b.after c):=by ext1; exact ( afterK _ _ _ ).symm
lemma after_r : a.after Id=a:= by ext1; exact after_one ..
lemma after_l : Id.after a=a:= by ext1; exact ready a
abbrev tangent :ℂ:= coeff 1 a.knob
abbrev Use :Prop:= a.tangent≠0
-- reversion. 
lemma first (p:PS): coeff 1 (a.applyPS p)= tangent a * coeff 1 p:= by rw [sent,FPS.coeff_substituted _ a.root]; simp [sum_range_succ,tangent,mul_comm]
lemma tangentK : (after a b).tangent=b.tangent*a.tangent:= b.first _
lemma tangentId : tangent Id=1:= coeff_one_X
section reversal
variable (hu:Use a)
def invF := a.knob.substInvOfIsUnit (isUnit_iff_ne_zero.mpr hu)
lemma invRoot : constantCoeff (a.invF hu)=0:= by simp [invF]
lemma invLeft : a.applyPS (a.invF hu)=X:= ( sent a _ ).trans ( subst_substInvOfIsUnit_left a.knob a.root _ )
lemma invCancels : LeftInverse (fun p:PS=> p.subst (a.invF hu)) a.applyPS:= by
   intro p; dsimp only; rw [sent, subst_comp_subst_apply a.has (HasSubst.of_constantCoeff_zero' (a.invRoot hu))]; unfold invF; rw [subst_substInvOfIsUnit_right _ a.root,X_subst]
lemma invReal : RealK (a.invF hu):= by
   apply ( invCancels a hu ).injective; rw [invLeft,sent];
   have h:= FPS.substitute_ringHom η ( invF a hu ) a.root; rw [←sent,invLeft,map_X, a.real ] at h; exact h.symm

def inverse : Key:= if h : Use a then ⟨ a.invF h,a.invRoot h,a.invReal h ⟩ else Id
include hu
lemma leftInv : a.inverse.after a=Id:= by unfold inverse; rw [dif_pos hu ]; ext1; exact invLeft a hu
lemma rightInv : a.after a.inverse=Id:= by unfold inverse; rw [dif_pos hu ]; ext1; change applyPS _ _=X; rw [sent]; exact subst_substInvOfIsUnit_right a.knob a.root _
lemma tangent_inverse : tangent a.inverse=a.tangent⁻¹:= by
   have hx:= congr_arg tangent (leftInv a hu); rw [tangentK,tangentId] at hx; exact mul_left_cancel₀ hu (hx.trans (mul_inv_cancel₀ hu).symm)
end reversal

-- power mix over a real module without assuming a topology
variable {E R:Type*}
section mix
variable [AddCommMonoid E][Module ℝ E][AddCommMonoid R][Module ℝ R]
def Γ (a:Key) (l k:ℕ):ℝ:= (coeff l (a.knob^k)).re
lemma canonical (l k:ℕ): ((Γ a l k):ℂ)=coeff l (a.knob^k):= (a.real.pow k).native l
lemma Γ0 (k:ℕ):Γ a k 0=if k=0 then 1 else 0:= by apply Complex.ofReal_injective; rw [canonical,pow_zero,coeff_one]; split <;> simp_all

def mix (f:ℕ→E)(l:ℕ) : E:= ∑ k∈range (l+1),a.Γ l k • f k
lemma Γ_combine (p:E): mix a (fun i=> if i=0 then p else 0) n = if n=0 then p else 0 :=by
   unfold mix; rw [Finset.sum_eq_single_of_mem 0 ( Finset.mem_range_succ_iff.mpr (Nat.zero_le n)), Γ0 ]; · split_ifs<;> simp_all
   intro j _ h; simp [h] -- indent
lemma begins (f:ℕ→E): a.mix f 0=f 0:= by rw [mix,Finset.sum_range_succ,Finset.sum_range_zero,zero_add,Γ0,if_pos rfl,one_smul]
lemma life (f:ℕ→E) : a.mix f 1=a.tangent.re • f 1:= by rw [mix,Finset.sum_range_succ,Finset.sum_range_succ,Finset.sum_range_zero,Γ0]; simp [Γ,tangent]
lemma across (f:ℕ→E)(L:E→ₗ[ℝ] R) (n:ℕ) : L ( a.mix f n ) = a.mix (L ∘ f) n:= by rw [mix,mix,map_sum]; simp
lemma combined (f g:ℕ→E) (n:ℕ): a.mix (f+g) n=a.mix f n+a.mix g n:= by simp [mix,smul_add,sum_add_distrib]
lemma complexes (p:PS) : coeff n ( a.applyPS p )= a.mix (fun i=>coeff i p ) n := by rw [sent,FPS.coeff_substituted _ a.root n,mix]; exact Finset.sum_congr rfl fun i _=> by rw [Complex.real_smul,canonical]; exact mul_comm .. -- `R/E` omitted
end mix
end Key
end YM.MS.WilsonBridge.Coupling
