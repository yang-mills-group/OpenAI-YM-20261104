import YM.FVA2.XReg.Post
/-!
# The posted/smeared arrays, and how to take their position limits

Unconnected arrays. In the MS variable. E.g.
`Rates` gives the smeared reports from `meteor` and `covered` gives all test-wise
limits at this stage of posting. See `Arrival/Landing.lean` about the underlying
cutoff estimates.

`ν` in this file is in the logarithmic convention of `YM/MS`. For example use
`ν = Teller.logNu 1` (see `Teller/Mass.lean`) to assert results at unit MS mass.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Reg.CoverTest
open Function Filter Set MeasureTheory Maxwell Maxwell.Free
open MS MS.Local.Physical MS.Menus MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival Dframe
open MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open Normalize.Fray Reg.Point Reg.Unique Retirement
open scoped Topology ContDiff BigOperators Classical
variable {n d k:ℕ}{G:Gauge}
local notation "Π"=> Press.portDeck G
local notation "ℒ"=> Normalize.Change G d
local notation "𝒮"=> XSpace.Structure1.Point G d n
local notation "μ"=> (PowerSeries.mk (R:=ℂ))
local notation "W"=> Fin n
-- two sides continuity.Determinants. Generic linear readers
variable (m:Mesh)
section realm
variable (C:Mesh→Reports G d) (P: Sample n→ℕ→ XSpace.Structure1.Point G d n)(v:Tags G d n) (U:Mesh→ Guard G d)
variable (q:Mesh→ Cn) (g:Test n)
abbrev Render := ∀ i:ℕ,∀ v:Tags G d n, C m i n g v=Deposit m (fun j=>P j i v) g
lemma forms (he:Render m C P g): realm (U m) (C m) k n g v= Deposit m (fun i=> status (U i.F) (P i) k v) g:= by rw [really]; simp_rw [he]; unfold Deposit; simp_rw [seen,Finset.mul_sum]; rw [Finset.sum_comm (s:=tally ..)]
lemma sub_s (ζ: Sample n→ T ℂ): Deposit m (fun i=> substitute (q i.F) (ζ i) k) g= substitute ( q m ) (fun i=> Deposit m (fun x=> ζ x i) g) k:= by
    unfold Deposit; simp_rw [rules,smul_eq_mul,Finset.mul_sum ]; rw [Finset.sum_comm (s:= Finset.univ)]; apply Finset.sum_congr rfl; intro i _; exact Finset.sum_congr rfl (fun j _=> by ring)
lemma sense (he:Render m C P g): substitute (q m) (C m) k n g v= Deposit m (fun i=> substitute ( q i.F ) (P i) k v) g:= by
    simp_rw [Dframe.translate]; rw [sub_s,← Reg.Point.seenT]; rw [Dframe.translate]; exact congr_fun (congr_arg (substitute (q m)) (funext (fun j=> he j v))) k -- maybe `rw [← seenT]`
lemma build_s (Y:XSpace.Initialize G): Render m (fun i=> batch Y i d) (live Y d (n:=n)) g:= fun i v=> ( deposit_live Y v m i g ).symm
end realm
open Pivot
variable (ν:ℝ)(Y:Initialize G)(S:Prescription (Press.portDeck G))
lemma price_m (t:Test n): Render m (posted ν Y S d) (postedPoint ν Y S d) t:= by
    let c:= Dframe.reset ν S; let C:=fun m:Mesh=> substitute ( c m ) (batch Y m d); have h(m): Render m C (fun i:Sample n=> orderT ν Y S i d) t:= fun i v=> sense m (fun m=> batch Y m d) (live Y d) v c t (build_s m t Y)
    intro i v; exact forms m C (fun i=> orderT ν Y S i d) v (fun m=> D ν S m d) _ (h m)
-- MS genuine Ops.P
section continuum
-- Complex linearity in the continuum calculation.
variable (P:Points n → XSpace.Structure1.Point G d n)
abbrev Continuum (P:Points n→𝒮) := ∀ p:Tags G d n, ContinuousOn (fun x=> P x p) (conf n)
def Sweep (P:Points n→ XSpace.Structure1.Point G d n) (hP: Continuum P) (t:Test n): 𝒮:= MultilinearMap.mk' (fun p=> t.applyTo fun x=> P x p)
    (fun p i a b=> by simp_rw [Test.applyTo,MultilinearMap.map_update_add,mul_add]; exact integral_add (t.smearing (hP _)) (t.smearing (hP _)) ) (fun p i a b=> by unfold Test.applyTo; simp_rw [ MultilinearMap.map_update_smul,smul_eq_mul, mul_left_comm (t _) a]; exact integral_const_mul a _ )
def cone (P:Points n → XSpace.Structure1.Point G d n)(hP: Continuum P): Test n →ₗ[ℂ] 𝒮:= {
    toFun := Sweep P hP
    map_add' := fun a b=> by ext1 p; simp only [Sweep,MultilinearMap.mk'_apply,Test.applyTo,add_apply,add_mul]; exact integral_add (a.smearing (hP _)) (b.smearing (hP _))
    map_smul' := fun c t=> by ext1 p; simp only [Sweep,MultilinearMap.mk'_apply,Test.applyTo,smul_apply,smul_eq_mul,RingHom.id_apply, mul_assoc]; rw [integral_const_mul] }
lemma present (hP: Continuum P) (p:Tags G d n)(t:Test n): cone P hP t p = t.applyTo fun x=> P x p:= rfl
variable {O: Booked (Press.portDeck G)} (T: MS_Data G O)
lemma measurable (k:ℕ): Continuum (fun x:Points n=> meteor ν T d x k):= by
    intro p; simp_rw [stencil_he ( meteor ν T d _ _ ) p,ribbon]; exact continuousOn_finsetSum _ (fun i _=> ( Landing.fresh ν T ( flash ∘ i ) _ _ ).const_mul _)
def Rates (d:ℕ): Reports G d:= fun k n=> cone _ ( measurable (n:=n) (d:=d) ν T k )
lemma indicative (t:Test n)(p:Tags G d n): Rates ν T d k n t p = t.applyTo fun x=> meteor ν T d x k p:=rfl
lemma ground : Rates ν T d 0=reference G d:= by
    ext1 n; ext1 t; ext1 p; rw [ indicative,reflects ]; apply Test.apply_eq; intro x hx; simp only [limit_lead (x:=x) ν T hx]
lemma regular (p:Tags G d n) (k:ℕ) : Centered (fun i:Sample n=> postedPoint ν Y S d i k p):= fun _ _ _=>rfl
variable (h:G.Simple) (hp:TaylorOKF T (Press.wickInput Y) S)
include h hp
abbrev Calls {I:Type*} (F:Filter I)(P:I→ Prediction G d)(R:Prediction G d): Prop:=∀ n (t:Test n)(p:Tags G d n), Tendsto (fun i=> P i n t p) F (𝓝 ( R n t p ))
lemma covered : Calls Front (fun i=> posted ν Y S d i k) (Rates ν T d k) := by
    intro n t p; simp_rw [ price_m _ ν Y S t k p ]; exact Photo.sees_test (conf n) t _ (conf_open n) ( tB ν Y S T h hp k p ) (regular ν Y S p k) t.tsupport_subset
end continuum
end YM.FVA2.Reg.CoverTest
