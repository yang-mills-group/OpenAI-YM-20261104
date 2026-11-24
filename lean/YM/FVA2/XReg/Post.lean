import YM.FVA2.XReg.Unique
/-!
# Exact finite-regulator price identity after the position-scheme comparison

Apply the **same** position scheme to the D-posted arrays (so `posted` here in the MS
coupling) as to the bare `batch`. The two near-free solves agree at order zero
since D itself is identity there in order zero and we actually precompose with the
reset coupling (substitution with no constant term). See `Ready` for the branch hypotheses and exact statement. By uniqueness
the rest must agree as formal frames, when right-composed onto D (left hand side
of `Ready.shape`), vs applying the **same reset** to the frame that was used in the
bare calculation (right hand side). This gives precise equalities for `substitute`
on both the points and the smeared arrays at finite regulator (`whole`, `rulers`).

`timely` is how to obtain `Ready` including its exact identity. We actually prove that
branch is available *eventually* as the regulator is removed. Then onwards no estimate or
truncation comparison on multiplying by a potentially divergent D is needed. See
`Main.Match.cancelsBare`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Reg.Pivot
open Function Filter Set MeasureTheory Maxwell Maxwell.Free
open MS MS.Local.Physical MS.Menus MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival Dframe
open MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open Normalize.Fray Reg.Point Reg.Unique
open scoped Topology ContDiff BigOperators Classical
variable {n d k:ℕ}{G:Gauge}
local notation "Π"=> Press.portDeck G
local notation "ℒ"=> Normalize.Change G d
local notation "𝒮"=> XSpace.Structure1.Point G d n
local notation "μ"=> (PowerSeries.mk (R:=ℂ))
local notation "W"=> Fin n
variable (ν:ℝ)(Y:Initialize G)(V:Normalize.Store G)(S: Prescription (Press.portDeck G))(m:Mesh)
local notation "A"=> ( V.measure d )
local notation "Ξ"=> ( V.survey d )
local notation "ℛ"=> ( V.prepared d )
local notation "𝒯"=> Dframe.reset ν S m
def posted (d:ℕ)(m:Mesh): Reports G d:= realm (D ν S m d) (substitute ( Dframe.reset ν S m ) (batch Y m d))
abbrev chalk (d:ℕ)(m:Mesh): Pick G d:= (V.survey d).Lays (V.prepared d) (posted ν Y S d m)
structure Ready (d:ℕ)(m:Mesh): Prop where
    open0 : V.Meets Y m d
    ink0 : Executed (V.survey d) (V.prepared d) (posted ν Y S d m)
    shape : D ν S m d * deck (chalk ν Y V S d m)= Point.stepV (reset ν S m) (deck (V.layout Y m d))
def coupledPoints (a:Sample n)(d:ℕ) : ℕ→Point G d n:= status (deck (chalk ν Y V S d a.F)) (postedPoint ν Y S d a)
def coupledBatch (d:ℕ)(m:Mesh):= realm (deck (chalk ν Y V S d m)) (posted ν Y S d m)
variable {O:Booked (Press.portDeck G)} (T: MS_Data G O)(h:G.Simple)(hs:TaylorOKF T (Press.wickInput Y) S)(hu:Favors.Horder S)(hx:Ace.UnitP S)
lemma genuine : CoreR (reset ν S m):= of_star (fun i=> ( Program.shiftR S.team i ).starv _)
include h hs hu
lemma posted_lead : posted ν Y S d m 0=batch Y m d 0:= eon ( batch Y m d ) 𝒯 ( D ν S m d ) ( Silver.dawn ν Y S m T h hs hu )
include hx
lemma timely {ι:Type*}{L:Filter ι}{g:ι→Mesh} (F:Expense.Stretched L g) :
        ∀ᶠ i in L, Ready ν Y V S d (g i):= by
    let D:= V.survey d
    have hw : D.Via (u:=L) (fun i=> posted ν Y S d (g i) 0):= by
      rw [show (fun i=> posted ν Y S d (g i) 0) = (fun i=> batch Y (g i) d 0)
          from funext fun i=> posted_lead ν Y S _ T h hs hu ]
      exact Fray.gait D Y F
    filter_upwards [ (V.nested_solution Y d F).2,D.happy ℛ hw] with i hi hp
    let l:=g i
    refine ⟨ hi.1,hp,duplicate ( share S.team _ ) ( genuine ν S l )
        ( batch Y l d ) ( Dframe.D ν S l d ) D ℛ
        (by exact ⟨ hi.1.1,hi.1.2.1,hi.1.2.2.2.2.2 ⟩ )
        ( Silver.formal_price ν Y S l T h hs hu hx ) ( Silver.dawn ν Y S l T h hs hu ) hp⟩
omit h hs hu hx
variable (a:Sample n)
lemma whole (he: Ready ν Y V S d a.F) : substitute (reset ν S a.F) (Rose.cooked Y V d a)=coupledPoints ν Y V S a d:= by
    let c:= deck (V.layout Y a.F d); let B:= live Y d a; have h: Rooted (reset ν S a.F):=share ..; unfold coupledPoints postedPoint; rw [eternal, he.shape]; exact Eq.symm (resetP (reset ν S a.F) c B h) -- Rose defeq
lemma rulers (he:Ready ν Y V S d m): substitute (reset ν S m) (V.opens Y m d)= coupledBatch ν Y V S d m:= by
    unfold coupledBatch posted; rw [parlance, he.shape, resetR 𝒯 _ _ (share ..)]; rfl
end YM.FVA2.Reg.Pivot
