import YM.FVA2.Generator.Prose
/-!
# One-vertex correction: qgau, finite flow interpretation

Using the diagonal result (`Prose.diary`) now obtain the actual
absence of an order-one term in the scale action on fields in the final
check and also in the MS scheme. Not claiming $κ$ ∞ expansion. Lifts through every finite grade in one statement.
Top stencil asymptotics already discharged. Then will differentiate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Generator.Q
open Function Filter Set MeasureTheory Maxwell Maxwell.Free Maxwell.Wick
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival
open MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open scoped Topology ContDiff BigOperators Classical
open Dframe Reg.Point Reg.Token Reg.Unique Reg.Choice _root_.YM.FVA2.Scale
open YM.FVA2.Scale.Facets Scale.Level Scale.Equator Scale.Measure Scale.Jury
open Scale.Meter Scale.GroupS Scale.Beta
variable {G:Gauge}{d:ℕ}
private lemma at_one (p:Cn)(hp:Tangent p)(X:Guard G d): coeff 1 (stepV p X)=coeff 1 X:= by
    rw [stepV,coeff_mk,rules, ← Nat.range_succ_eq_Iic, Finset.sum_range_succ, Finset.sum_range_one]; simp [cut,hp.lead]
private lemma matter (A B:Guard G d)(p:Base A)(q: Base B): coeff 1 (A*B) =coeff 1 A+coeff 1 B:= by
    rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (f:= fun i j=> coeff i A * coeff j B), Finset.sum_range_succ, Finset.sum_range_one,p.zero,Nat.sub_self,Nat.sub_zero,q.zero]; simp only [ one_mul,mul_one ]; exact add_comm ..
variable (ν:ℝ)(Y:XSpace.Initialize G){V:XSpace.Normalize.Store G}(K:XSpace.Rose.Pick V){O: Booked (Press.portDeck G)}(T:MS_Data G O)
variable (S:Prescription (Press.portDeck G)) (t:ℝ) (h:G.Simple)(hs:TaylorOKF T (Press.wickInput Y) S)(hr:Favors.Horder S)(hu:Ace.UnitP S)
local notation "γ" => Scale.GroupS.ψ K T ν
local notation "π" => Scale.GroupS.Ψ K T ν
local notation "Gm" => Scale.GroupS.gaugeM Y K T ν
local notation "Gn" => Scale.GroupS.gaugeN Y K T ν
local notation "Gx" => Scale.GroupS.gaugeB K T ν
local notation "Z" => Scale.Measure.Z Y K ν T
local notation "φ" => Scale.Measure.f K ν T
include h hs hr hu
lemma horizonX : diag (coeff 1 (gaugeB K T ν t d))=0:= by
    obtain H:= scaleX ν Y K T S h hs hr hu; obtain he:= reaches Y K ν T S h hs hr hu d; rw [Measure.together Y K ν T S h hs hr hu d] at he; exact Prose.diary h Y K t (Measure.start Y K d) (γ t) (Gx t d) he (H.led t) (H.paid t d) ( H.reads t d )
lemma lifted : coeff 1 ( gaugeN Y K T ν t d )=0:= by
    let N:= Measure.adjust Y K d; obtain he:=congr_arg ( fun p:Guard G d=> diag (coeff 1 p) ) (relatingN ν Y K T S h hs hr hu t) -- t order
    obtain hc:= true_N ν Y K T S h hs hr hu t (d:=d); have hz:= ( adj Y K ν T S (d:=d) h hs hr hu ).scale; have hh:= scaleX ν Y K T S h hs hr hu; rw [matter (Gx t d) _ (true_B ν Y K T S h hs hr hu t) (hz.switch (hh.led t).real), matter (convertT t ( adjust Y K d )) ( Gn t d ) (converts t _ hz) hc, at_one _ (hh.led t), convertT,coeff_mk] at he; -- Need `diagonal` proof.No use N.strict? diag(N)=no positive. diag( ξ) may not zero; both sides same. diag(N)* δ cancels.
    rw [map_add (diag (d:=d) (G:=G)),map_add (Level.diag (d:=d) (G:=G)),horizonX ν Y K T S t h hs hr hu, Penny.diag_version, fitsN ν Y K T S h hs hr hu t (d:=d) 1] at he
    ext1 v; have hu:=LinearMap.congr_fun he v; change 0+diag (coeff 1 N) v= diag (coeff 1 N) v+coeff 1 (Gn t d) v at hu; rw [zero_add] at hu; exact add_eq_left.mp hu.symm
lemma liftedM : coeff 1 ( gaugeM Y K T ν t d )=0:= by
    obtain hV:= Measure.litZ Y K ν T S (d:=d) h hs hr hu; obtain hm:= true_M ν Y K T S h hs hr hu t (d:=d); have he:= congr_arg ( fun z:Guard G d=> coeff 1 z ) (contractM ν Y K T S h hs hr hu t (d:=d)); obtain hx:= Specific.vigor_f Y K ν T S h hs hr hu; obtain ht:= true_ψ ν Y K T S h hs hr hu t; rw [ matter _ _ (hm.switch hx.real) (hV.switch ht.real), matter _ _ hV ( true_N ν Y K T S h hs hr hu t ),at_one _ ht, at_one _ hx,lifted ν Y K T S t h hs hr hu ] at he; ext1 v; have hh:= LinearMap.congr_fun he v; change coeff 1 (gaugeM Y K T ν t d) v+coeff 1 (Z d) v=coeff 1 (Z d) v + 0 at hh; rw [add_zero] at hh; exact (add_eq_right.mp hh)
/-- Reusable erected output on formal Wilson certification input,
no assumption about rotational calibration past equivariant orientation as in this $Z$. -/
theorem witnessed (d:ℕ): coeff 1 (gaugeN Y K T ν t d)=0 ∧ coeff 1 (gaugeM Y K T ν t d)=0:= ⟨ lifted ν Y K T S t h hs hr hu, liftedM ν Y K T S t h hs hr hu ⟩
end YM.FVA2.Generator.Q
