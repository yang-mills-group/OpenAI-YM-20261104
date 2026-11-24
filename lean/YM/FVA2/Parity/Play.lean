import YM.FVA2.Lambda.Parity
import YM.FVA2.Parity.Shards
import YM.XSpace.Welcome
/-!
# Our parity operations on the formal series

Auxiliary to `Parity/Clock.lean`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Parity.Invol
open Function Filter Set MeasureTheory Maxwell Maxwell.Free Maxwell.Wick
open MS MS.Local.Physical MS.High MS.Wind MS.Theater MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival
open MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open scoped Topology ContDiff BigOperators Classical
open Dframe Reg.Point Reg.Token Reg.Unique Reg.Choice _root_.YM.FVA2.Scale
open Hue.Agent Hue.Agent.Kappa
variable {n m k e i j:ℕ}{G:Gauge}{f q:Cn}
local notation "P"=> (-PowerSeries.X:Cn)
def Anti (f:Cn): Prop:= f.subst (-PowerSeries.X)= -f -- bind type inference
lemma t : Anti f↔ Rose.inversion f= -f:= by simp only [Rose.inversion,rescale_eq_subst, neg_one_smul ]; rfl
namespace Anti
variable (h:Anti f)
include h
lemma compose (hv:Anti q)(hu:Rooted q): Anti (f.subst q):= by
    apply t.mpr; have ht:= Rose.turnInv ((coeff_zero_eq_constantCoeff_apply _).symm.trans hu) ( t.mp hv ) f; rw [ht,t.mp h, ← coe_substAlgHom ( licence _ hu ), map_neg ]
lemma wipe (i:ℕ)(he:i%2=0): coeff i f=0:= Lambda.Pen.wipe _ h i (Nat.even_iff.mpr he)
lemma root : Rooted f:= wipe h 0 (by decide)
lemma pairwise (p n:ℕ)(hp:p%2≠n%2): coeff n (f^p)=0:= Hue.Agent.powers (g:=f) (k:=n) (fun i _ h'=> h.wipe i (by omega)) p n (le_refl _) (Ne.symm hp)
lemma pack (H:q.subst f= X)(hQ:f.subst q=X)(hq:Rooted q): Anti q:= by
    let k := ( licence f h.root ); let d:=( licence q hq ); have he: Rose.inversion X = -(X:Cn):= rescale_neg_one_X; have hc:= Rose.turnInv ((coeff_zero_eq_constantCoeff_apply _).symm.trans ( root h )) (t.mp h) q
    have hN: ( Rose.inversion q ).subst f = (-q).subst f:= by rw [← hc,H, he, ← coe_substAlgHom k, map_neg, coe_substAlgHom k,H]; -- `coe_substAlgHom` simp
    apply t.mpr; calc
     _= PowerSeries.subst q ( ( Rose.inversion q ).subst f ):= by rw [ subst_comp_subst_apply k d, hQ, X_subst ]
     _= _:= by rw [hN, subst_comp_subst_apply k d, hQ, X_subst ]
end Anti
-- frame convention: order-even blocks commute with sign matrix hinge; odd ones anticommute.
local notation "M"=> FieldEnd G n
local notation "L"=> Guard G n
local notation "Ω"=> Normalize.hinge
local notation "A₀"=> Normalize.hinge n
local notation "C"=> Hue.σ
-- non-near OK (doesn't rely on norm or ↑rank). preserve.L.Limit
abbrev Wants (i:ℕ)(A: FieldEnd G n): Prop:= ∀ x:Sec G n,A (Ω n x) = C i • Ω n ( A x )
abbrev Facing (A:Guard G n) : Prop:= ∀ i, Wants i (coeff i A)
namespace Wants
variable {A B: FieldEnd G n}{V: M}
lemma add (h:Wants i A)(hg:Wants i B): Wants i (A+B):= by intro x; simp only [LinearMap.add_apply, map_add,h,hg, smul_add]
lemma cash (h:Wants i A)(c:ℂ): Wants i (c • A):= by intro x; rw [LinearMap.smul_apply,LinearMap.smul_apply,map_smul,h, smul_comm c (C i)]
lemma zero : Wants i (0:M):= fun x=> by simp only [LinearMap.zero_apply, map_zero,smul_zero]
lemma sum {J:Type}{F:J→ FieldEnd G n}(s:Finset J)(h:∀ j∈s,Wants i (F j)): Wants i (∑ j∈s,F j):= by intro x; simp only [LinearMap.sum_apply,map_sum,Finset.smul_sum]; exact Finset.sum_congr rfl fun j hj=> h j hj x
lemma multip (h:Wants i A)(hg:Wants j B): Wants (i+j) (A*B):= by intro x; rw [ Module.End.mul_apply, Module.End.mul_apply, hg,map_smul, h,Hue.sp,smul_smul,mul_comm ]; -- dot
                                                        -- push
lemma same : Wants 0 (1:M):= by intro x; simp only [ Hue.s0, one_smul ]; rfl
lemma now (A: Normalize.Pick G n) (hp:faced A=A): Facing (deck A):= by
    intro i x; rw [← Screen.sig]; 
    obtain he:=posing A i x; rw [hp] at he; exact he
end Wants
namespace Facing
variable {A B:Guard G n}
lemma one : Facing (1:L):= by intro i; rw [coeff_one]; split_ifs with hi; subst i; exact Wants.same; exact Wants.zero
lemma mul (h:Facing A)(hg:Facing B): Facing (A*B):= by
    intro i; rw [ coeff_mul ]; exact Wants.sum _ (fun j hj=> ( Finset.mem_antidiagonal.mp hj ) ▸ (h j.1).multip (hg j.2)) -- possible Lean expands sum_rev direction
lemma substR (h:Facing A)(f:Cn)(hf:Anti f): Facing (Reg.Point.stepV f A):= by
    intro i; rw [Reg.Point.stepV, coeff_mk,rules]; apply Wants.sum; intro j hj; by_cases hx: i%2=j%2; · exact fun v=> Hue.s_he.mpr hx ▸ (( h j ).cash _ v); -- orientation check
    unfold Program.cut; rw [hf.pairwise j i ( Ne.symm hx ),zero_smul ]; exact Wants.zero
lemma sacr (t:ℝ) (h:Facing A): Facing (convertT t A):= by
    have he(t:ℝ): Wants 0 (Level.Dial n t (G:=G)):= by
        unfold Level.Dial; apply Wants.sum; intro j _; refine Wants.cash ?_ _; intro x; rw [Hue.s0,one_smul]; exact Subtype.ext (hinge_part ..)
    intro i; rw [convertT,coeff_mk]; exact Wants.multip ( by simpa only [zero_add] using Wants.multip ( he (-t) ) ( h i )) ( he t )
lemma keeps (h:Facing A): Facing (Scale.diagonal A):= by
    have he(i:Level.E n): Wants 0 (Level.proj (d:=n) (G:=G) i):= by intro x; rw [Hue.s0,one_smul]; exact Subtype.ext (hinge_part ..)
    intro i; rw [Scale.diagonal, coeff_mk]; exact Wants.sum _ (fun j _ => Wants.multip (by simpa only [zero_add] using Wants.multip ( he j ) ( h i )) ( he j ) )
lemma neg_w (n:ℕ): Wants 0 (-1:FieldEnd G n):= by intro x; rw [LinearMap.neg_apply,LinearMap.neg_apply,map_neg,Hue.s0,one_smul]; rfl
lemma reflects (h:Facing A): Facing (Scale.mirror A):= by
    intro i; induction i using Nat.strong_induction_on with
    | h i ih=>
        rw [Scale.mirror, coeff_invOfUnit i A 1]; simp only [inv_one, Units.val_one]; split_ifs with hi; · subst i; exact Wants.same
        have he {B: FieldEnd G n}(h: Wants i B): Wants i (( -1:M ) * B):= by simpa only [zero_add] using Wants.multip (neg_w (G:=G) n) h
        refine he ( Wants.sum _ ?_ ); intro j hj; split_ifs with hp; swap; exact Wants.zero; exact Finset.mem_antidiagonal.mp hj ▸ Wants.multip (h _) (ih j.2 hp)
end Facing
end YM.FVA2.Parity.Invol
