import YM.RG11Proof.Scale.Vanish
import YM.RG11Proof.Scale.Separating

/-!
# Formal scheme conversion of beta and gamma to given truncation order

`d_t` formal derivative, Θ geometric Euler on separated tests represented
by applying another profile (same width) yielding `euler` operation on a.
For each of two INDEPENDENT arrays and β,γ (here sign convention b,
 minus frame b on RHS when geometric side = Θ-aweight = β*a' - vary a b)
assume CS holds. Their mismatch at order k then detected by the SAME joint
pencil as for matching coupling/fields (not an actual readout inversion).
Orientation: `B(g) = A(T(g)) ∘ D(g)`. No divisions needed to express the
law, no preferred leading coefficient assumed. Require β_B zero constant
to require match only through order n incl n=0.
External β and γ are *inputs*, not defined by the transformation equations.
Translations to other normalization/sign conventions require adapters. If
Euler actions also move the frames/anchor/test parameters, must reduce to
this law with genuine common profiles first.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.RG11.Scale
open scoped BigOperators Classical Topology
open PowerSeries YM.PertExtension.Position YM.RG11.Jets

-- Use ℝ ring at present to insert engineering subtractions.
variable {J P:Type*}[Fintype J]{width:P→ℕ}
local notation "slot"=> PertExtension.Position.insert

-- Euler profile, THROUGH n equality on coefficientwise predictions

def euler (E:Keeper width)(w:J→ℕ)(A:ArrayAt J ℝ width)(v : Mark J width):PowerSeries ℝ:= A (E.move v)- C (bulk w v)*A v

def call (β:PowerSeries ℝ)(b:Square J (PowerSeries ℝ))(A:ArrayAt J ℝ width)(v:Mark J width):PowerSeries ℝ:= β* derivative ℝ (A v)- orbit A v b

def Stem (N:ℕ)(E:Keeper width)(w:J→ℕ)(A:ArrayAt J ℝ width)(β:PowerSeries ℝ)(b:Square J (PowerSeries ℝ)):Prop:= ∀ v, Through N (euler E w A v) (call β b A v)

-- split out maps
variable (p:Change ℝ J)(A:ArrayAt J ℝ width)

private def ψ (h: Anchored p.g): PowerSeries ℝ→ₐ[ℝ] PowerSeries ℝ:= substAlgHom (R:=ℝ) h.permits
private theorem uses(h:Anchored p.g) : (ψ p h : PowerSeries ℝ→ PowerSeries ℝ)= PowerSeries.subst p.g:=coe_substAlgHom _

private theorem ψ_act (h : Anchored p.g)(v:Mark J width): p.act A v=slot J width (fun v=>ψ p h (A v)) (fun i j=>p.Z i j) v:=by
  have he (x:PowerSeries ℝ): ψ p h x=PowerSeries.subst p.g x:=congrFun (uses p h) x
  simp_rw [he]; rfl
set_option maxRecDepth 1500
set_option linter.unusedSectionVars false

private theorem pins (h:Anchored p.g)(w:ℝ) : ψ p h (C w)=C w:= (ψ p h).commutes w

theorem call_derivative (β:PowerSeries ℝ)(b:Square J (PowerSeries ℝ))(hp:Anchored p.g)(v:Mark J width):
    call β b (p.act A) v = slot J width (fun z=> (β*derivative ℝ p.g)*PowerSeries.subst p.g (derivative ℝ (A z))) (fun i j=>p.Z i j) v +
        varies (fun z=>PowerSeries.subst p.g (A z)) p.Z (β • (flash p.Z)- b*p.Z) v:=by
    let S:= fun z=>PowerSeries.subst p.g (A z)
    let y:= fun z=>PowerSeries.subst p.g (derivative ℝ (A z))
    rw [call]
    change β * derivative ℝ (slot J width S (fun i j=>p.Z i j) v) - orbit (slot J width S (fun i j=>p.Z i j)) v b = _
    rw [derivative_insert,← varies_orbit,varies_exterior S p.Z 1 b,one_mul]
    rw [←responds_at,← responds_at, ←responds_at,map_sub,map_smul]
    rw [←slams_at, ← slams_at]
    have he (z:Mark J width): (derivative ℝ ∘ S) z= derivative ℝ p.g*y z:=by unfold S y; rw [Function.comp_apply,derivative_subst ℝ hp.permits,mul_comm]
    rw [show derivative ℝ ∘ S=(derivative ℝ p.g) • y from funext he]
    change _ - _ = slams p.Z v ((β*derivative ℝ p.g) • y) + (_ - _)
    rw [map_smul,map_smul]; simp only [smul_eq_mul]; change β * (_* _+ responds _ _ _ _)- responds _ _ _ _ = _
    dsimp only [S]; ring

-- act on call of A
theorem call_carried (β: PowerSeries ℝ)(b:Square J (PowerSeries ℝ))(hp:Anchored p.g)(v:Mark J width):
   p.act (call β b A) v = slot J width (fun z=> PowerSeries.subst p.g β* PowerSeries.subst p.g (derivative ℝ (A z))) (fun i j=>p.Z i j) v -
      varies (fun z=>PowerSeries.subst p.g (A z)) p.Z (p.Z*subs p.g b) v:=by
   rw [ψ_act p (call β b A) hp v]
   let S:= fun z=>PowerSeries.subst p.g (A z)
   have he (z:Mark J width) : ψ p hp (call β b A z)= PowerSeries.subst p.g β * PowerSeries.subst p.g (derivative ℝ (A z)) - orbit S z (subs p.g b):= by
      simp only [call,map_sub,map_mul,orbit,map_sum,uses,S,subs_apply]
   rw [←slams_at]
   simp_rw [he]
   change slams p.Z v ((fun z=> PowerSeries.subst p.g β * PowerSeries.subst p.g (derivative ℝ (A z)))-(fun z=>orbit S z (subs p.g b)))=_
   rw [map_sub,slams_at,slams_at]; congr 1
   rw [show (fun z=>orbit S z (subs p.g b))=varies S 1 (subs p.g b) from funext fun z=> (varies_orbit ..).symm, varies_interior,mul_one]

-- exact difference
set_option maxHeartbeats 800000 in
theorem next_left (β μ:PowerSeries ℝ)(b m:Square J (PowerSeries ℝ))(hp:Anchored p.g)(v:Mark J width):
    call β b (p.act A) v - p.act (call μ m A) v=
       leftover (A:=A) (β • (flash p.Z)-b*p.Z+p.Z * subs p.g m) (β * derivative ℝ p.g-PowerSeries.subst p.g μ) p v:=by
   rw [call_derivative _ _ β b hp,call_carried _ _ μ m hp,leftover]
   let y (v:Mark J width):=PowerSeries.subst p.g (derivative ℝ (A v))
   rw [←slams_at, ←slams_at,← slams_at,←responds_at,← responds_at,← responds_at]
   change slams p.Z v ((β*derivative ℝ p.g) • y)+_ - (slams p.Z v ((PowerSeries.subst p.g μ) • y)-_)=slams p.Z v ((β*derivative ℝ p.g-PowerSeries.subst p.g μ) • y)+_
   simp only [map_add,map_smul,smul_eq_mul,sub_mul]; abel

-- grade preservation commutes the bulk; use all FPS graded here, for finite order use prefix truncation later.
theorem sends_engineering (w:J→ℕ)(E:Keeper width)(hp:Anchored p.g)(hD:graded w p.Z)(v:Mark J width):
   p.act (euler E w A) v=euler E w (p.act A) v:=by
   simp_rw [ψ_act p (euler E w A) hp v, euler, map_sub,map_mul,pins]
   change slams p.Z v ((fun z=> ψ p hp (A (E.move z)))-(fun z=>C (bulk w z)*ψ p hp (A z)))= _- _
   rw [map_sub,slams_at,uses,Keeper.move_act]; congr 1
   rw [slams_at,Change.act]; unfold PertExtension.Position.insert
   rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun x _=>?_)
   by_cases h:∀ i,w (x i)=w (v.2 i)
   · dsimp only; rw [show bulk w (⟨v.1,x⟩:Mark J width)= bulk w v from Finset.sum_congr rfl (fun b _=>congrArg (Nat.cast) (h b)),mul_assoc]
   obtain ⟨i,hi⟩:= not_forall.mp h
   have he : ∏ b,p.Z (v.2 b) (x b) = 0:= Finset.prod_eq_zero (Finset.mem_univ i) (@hD (v.2 i) (x i) (Ne.symm hi))
   dsimp; rw [he]; simp
end YM.RG11.Scale
