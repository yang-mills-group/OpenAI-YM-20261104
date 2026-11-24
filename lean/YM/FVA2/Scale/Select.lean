import YM.FVA2.Scale.View
/-!
# One coupling and the entire horizon collection
Using the *same* diagnostic at each stage (after frame action). Establish a genuine
uniqueness on all such frames and all reports. Don't attempt to prove uniqueness of
*MS Data* among different dimensional conventions; through this horizon require the actual
supplied compatible one.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Scale.Select
open Function Filter Set MeasureTheory Maxwell Maxwell.Free Maxwell.Wick
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival
open MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open scoped Topology ContDiff BigOperators Classical
open Dframe Level Reg.Point Reg.Token Reg.Unique Reg.Choice Facets Equator Measure Jury
variable {G:Gauge}{n d k:ℕ}
section device
variable (A:Way G 6){V:Normalize.Store G}(K:Rose.Pick V)
abbrev Single (A:Way G 6)(i:Points 3) := Rose.b3 ( Rose.batchT ( fxt A i ) )
def output (A:Way G 6) := PowerSeries.mk (fun i=> Test.applyTo (Rose.test K) (fun x=> coeff i (Single A x)))
def meter (A:Way G 6): Cn:= tune K (output K A)
lemma steady (h:Thin A): ContinuousOn (fun x=> coeff k ( Single A x )) (conf 3):= by
    intro x hx; let p:= 𝓝[conf 3] x; exact ( Harmony.cycle (C:=fxt A (n:=3)) ( show Reg.Higher.Pieces p _ ( fxt A x ) from fun i t=> h _ i t x hx ) ) k
lemma media (q:Cn)(hq:Rooted q)(H:Thin A): meter K (couple q A)=(meter K A).subst q:= by
    unfold meter; rw [tune_p K _ _ hq]; congr 1; refine PowerSeries.ext fun i=>?_ ; simp_rw [output, ← Constants.actual_subst _ _ hq, coeff_mk, Single, fxt_c, b3_p _ _ hq, ← Constants.actual_subst _ _ hq, coeff_mk,rules,smul_eq_mul ]; -- simp fails if no match, calc
    unfold Test.applyTo; simp_rw [ Finset.mul_sum ]; rw [integral_finsetSum]; · refine Finset.sum_congr rfl (fun j _ => ?_); rw [ ← integral_const_mul ]; apply integral_congr_ae; filter_upwards with a; ring
    intro j _; exact (Rose.test K).smearing ( ContinuousOn.const_mul (b:=Program.cut q j i) (steady A H (k:=j)) )
end device
variable (Y:Initialize G){V:Normalize.Store G}(K:Rose.Pick V) (ν:ℝ) {O: Booked (Press.portDeck G)}(T:MS_Data G O)
variable (S: Prescription (Press.portDeck G)) (h:G.Simple)(hs:TaylorOKF T (Press.wickInput Y) S)(hr:Favors.Horder S)(hu:Ace.UnitP S)
local notation "Ψ"=> Measure.chi K ν T
local notation "φ"=> Measure.f K ν T
local notation "Ω"=> Reg.State.chooseL ν V T
local notation "P"=> start Y K
local notation "XQ"=> PowerSeries.X (R:=ℂ)
abbrev selected (d:ℕ): Way G d:= actMark (Reg.State.chooseL ν V T d) (wave ν T d) -- H in terms MS g
lemma meter_m : meter K ( selected (V:=V) ν T 6 )=Ψ:= by
    suffices h:output K (selected (V:=V) ν T 6)= sky ν K T by rw [meter,h]; rfl
    refine PowerSeries.ext fun i=>?_ ; rw [output,coeff_mk,Reg.Choice.sky,coeff_mk]; apply Test.apply_eq; intro x hx; dsimp only; unfold Single fxt; rw [dif_pos hx]; rfl
include h hs hr hu
lemma vigor : Payment Ψ φ:= Reg.Faith.hearty ν Y K S T h hs hr hu|>.cost
omit h hs hr hu in
lemma ranked : Thin (selected (V:= V ) ν T d):= ( ( initial ν T ).light ).specify _
lemma earlier : couple φ (selected (V:=V) ν T d)=P d:= by rw [ ← together Y K ν T S h hs hr hu ]; exact ( team ( wave ν T d ) _ _ (vigor Y K ν T S h hs hr hu).own ).symm
include ν
lemma overcome : meter K (start Y K 6)=XQ:= by rw [← earlier Y K ν T S h hs hr hu, media _ _ _ (vigor Y K ν T S h hs hr hu).own (ranked (V:=V) ν T), meter_m, (vigor Y K ν T S h hs hr hu).right ] -- ranked args
variable {p q:Cn} (hq:Rooted q)(hp:Rooted p)(hc:CoreR q)(hd: CoreR p)
include hp hq
lemma key (Ht:couple p ( start Y K 6 )=couple q ( start Y K 6 )): p=q:= by
    obtain he:Thin ( start Y K 6 ):=( enrolled ν T Y K S h hs hr hu ).light; replace Ht:= congr_arg (meter K) Ht; rw [ media _ _ _ hp he, media _ _ _ hq he,overcome Y K ν T S h hs hr hu, subst_X ( licence p hp ),subst_X (licence q hq) ] at Ht; exact Ht
include hc hd
-- uniqueness anew. $a$ packing not used, allows even arbitrary non-comp frames: forcing holds at **every** finite horizon, not just >=6, but needs info at >=6 for f specifically.
theorem lock (a b:(d:ℕ)→Guard G d) (ha:∀ i,Base (a i))(hb:∀ i,Base (b i))
    (H:∀ i, actMark (a i) (couple p (start Y K i))=actMark (b i) (couple q (start Y K i))): p=q∧a=b:= by
    have he(i:ℕ) : actMark ((a i)*mirror (b i)) (couple p (start Y K i))= couple q (start Y K i):= by rw [ ← acts, H, acts, (hb i).turn', acts_h ]
    have hA(i:ℕ) : a i * mirror (b i)=1:= Jury.measured_single ν T Y K S h hs hr hu ( a i * mirror ( b i ) ) hp hq hd hc ( ( ha i ).mul (hb i|>.rewind) ) (he i) -- binder order
    refine ⟨ key Y K ν T S h hs hr hu hq hp ( by rw [ ← he, hA 6,acts_h ] ), funext fun i=>?_ ⟩; rw [ ← mul_one (a i), ← (hb i).turn, ← mul_assoc, hA, one_mul ]
-- rigidity transfers to any scale.We need actual Eqconv uniqueness as well.
end YM.FVA2.Scale.Select
