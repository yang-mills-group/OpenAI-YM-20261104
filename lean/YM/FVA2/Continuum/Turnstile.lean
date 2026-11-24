import YM.FVA2.Press.Lights
import YM.MS.Dial.Signals
/-!
# Actual applications of Tide.remove and Dial.LPT_to_MS using the same identified coefficients

This installs *raw* (pre-W Wick cleanup) physical fields with exactly the native stencils.
In this application of `Tide.remove` and `Dial.LPT_to_MS` each provides a choice of
`TaylorOK` scheme (incl. matching team and mark fees) and a comparison with MS using
those data. We call both, and enhance each result to also see the *other*
endpoint comparison using the same choices. In fact, **every** scheme with the
stated `TaylorOK` works for both (`match_p`), on the tuning/display geometries of
`Uses` below, incl positive arities.
Later for position normalization we need an extension of that comparison (for the
W-compensated version of the columns). See `YM/FVA2/Full` for the extension. We do not
assume that particular witnesses of the two endpoints here are equal
as fees/poles or assert separate procedures commute.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Continuum
open Function Set Filter Finset Lattice MeasureTheory
open YM.MS MS.High MS.Orbit MS.Vista MS.Tide MS.Fleet MS.Wind MS.Rake MS.Tone MS.Swirl MS.Swirl.Near
open MS.Menus MS.Local.Physical MS.Book MS.Book.Convolve Program MS.Land
open Dial
open Press Change
open scoped Topology BigOperators
variable {G:Gauge} (Y:XSpace.Initialize G)
local notation "B" => Press.portDeck G
local notation "H" => Press.program Y
variable {W I:Type} [LinearOrder W]
variable (u:W→ MS.Rake.Label (Press.portDeck G)) {M: MS.Land.Booked (Press.portDeck G)} (F: MS_Data G M)
variable (P: MS.Dial.Trial I W) (v: ℝ)(l:Filter I)
variable (A: Land.Prescription (Press.portDeck G))
local notation "W₀" => ApplyM (Press.program Y) (Stripped A.team) A u

lemma period_even (n:Lattice.Side) : Even (MS.Orbit.periodN n).val := ⟨n.val,show 2*n.val=n.val+n.val from two_mul _⟩
/-- Pre-W versions of the actual moments at each finite regulator, with mark fees
and action recoupled using the data in `A` -- see `Change.Dictionary` for the
reassembly involved. The `trueBorn` assertion then verifies these as the
ordinary products corresponding to the `V : Terrify W I` in the comparison. -/
def rawFull : Terrify W I := fun s k i =>
    (dictionary Y).finite u (P.head i) (fun w=> P.off w i) s A
      ( MS.Orbit.dimT P.side i ) (v-P.profile.θ i) k
local notation "Z₀" => rawFull Y u P v A

def trueBorn (V:Terrify W I) : Prop:= ∀ i s,(bury i s V)= (dictionary Y).finite u (P.head i) (fun w=>P.off w i) s A ( MS.Orbit.dimT P.side i ) (v-P.profile.θ i)
lemma reality_backend (V:Terrify W I): Cutoff (Press.program Y) u P v true A V ↔ trueBorn Y u P v A V:= by
    let D:= dictionary Y; refine ⟨fun h i s=> Eq.symm ?_,fun h i s=> ?_⟩
    · exact (D.identify u _ _ _ (period_even _) s A _).mp (h i s)
    exact (D.identify u _ _ _ (period_even _) s A _).mpr (h i s).symm
lemma recounted {V:Terrify W I}(h:trueBorn Y u P v A V) : PeakT.ordZ V=rawFull Y u P v A:= by funext s k i; exact congr_fun (h i s) k

/-- Both comparisons for the *same* `V`. This includes quantitative power estimates
on the trial as in `coherent` and `scalePhysics`, on every finite set of marks. `trueBorn`
and `whole` link those results to the actual pre-W moments (`Y` specifies
our choice of stencils). No identification of the `b=false` case is intended. -/
structure Twin (A:Land.Prescription (Press.portDeck G)) (V:Terrify W I) : Prop
    extends toCoherent : MS.Dial.coherent M F (Press.program Y) u P v true A l V where
    born : trueBorn Y u P v A V
    whole : PeakT.ordZ V = rawFull Y u P v A
    removes : ∃ U, Tide.scalePhysics P.profile M F v A
      (Press.program Y) u P.off P.head P.side true l V U
lemma paired {V:Terrify W I}(h: MS.Dial.coherent M F (program Y) u P v true A l V)(ht:Uses P l v)(hz:∃ Z U,Tide.scalePhysics P.profile M F v A (Press.program Y) u P.off P.head P.side true l Z U): Twin Y u F P v l A V:= by
    obtain ⟨Z',U,p⟩:=hz; have hp:Cutoff (program Y) u P v true A Z':= fun i s=> ht.reality i ▸ p.native i s
    have he:= MS.Dial.separate _ _ _ h.cost hp h.init p.empty; -- the V are identified
    obtain hb:= (reality_backend Y u P v A _).mp h.cost; exact ⟨h,hb,recounted Y u P v A hb,⟨U, he.symm ▸ p⟩⟩

-- common. literal endpoints.
structure TruePlan (F: MS_Data G M)(Y: XSpace.Initialize G)(A: Land.Prescription (Press.portDeck G)) : Prop where
   taylor : MS.Land.TaylorOK F (program Y) A
   poses (W I:Type) [LinearOrder W] (P:Trial I W) (l:Filter I) (v: ℝ)
       (u:W → MS.Rake.Label (Press.portDeck G)) :
     Dial.Uses P l v → ∃! V:Terrify W I, Twin Y u F P v l A V

lemma match_p (hG:G.Simple) (h: TaylorOK F (program Y) A) : TruePlan F Y A := by
 refine ⟨h,?_⟩; intro W I i P l v u he
 obtain ⟨V,hV⟩ := Dial.check_t F (Press.program Y) u P h he hG true
 exact ⟨V, paired Y u F P v l A hV he (Tide.called u P.off he.total he.reality
        he.upright he.super hG he.clear he.wind he.knit h true),
      fun y hy=> Dial.separate _ _ _ hy.cost hV.cost hy.init hV.init⟩

-- Literal applications. Use `proofStart` and `plan` in Continuum/Reg.lean
-- to access the tuning.
lemma from_tide (h:G.Simple) : ∃ A:Land.Prescription (Press.portDeck G), TruePlan F Y A := by
 obtain ⟨A,hA,T⟩:= YM.MS.Tide.remove (Press.program Y) F h
 refine ⟨A,hA,?_⟩; intro W I i P l v u he
 obtain ⟨V,hV⟩ := Dial.check_t F (Press.program Y) u P hA he h true
 exact ⟨V, paired Y u F P v l A hV he (T I W i P.profile P.side P.head true
        l u P.off v he.total he.reality he.upright he.super he.clear he.wind he.knit),
      fun y hy=> Dial.separate _ _ _ hy.cost hV.cost hy.init hV.init⟩

lemma from_dial (h:G.Simple) : ∃ A:Land.Prescription (Press.portDeck G), TruePlan F Y A := by
 obtain ⟨A,hA,T⟩:= YM.MS.Dial.LPT_to_MS (Press.program Y) F h
 refine ⟨A,hA,?_⟩; intro W I i P l v u he
 obtain ⟨V,hV,U⟩ := T W I i P l v u true he
 exact ⟨V, paired Y u F P v l A hV he (Tide.called u P.off he.total he.reality
        he.upright he.super h he.clear he.wind he.knit hA true),
      fun y hy=> U y hy.toCoherent⟩

/-- Choose both the XSpace initialization and the supplied MS data on `portDeck G`.
For the final comparison using this structure we choose a particular `Booked`
(incl. particular equivariant choices at all ranks), but `Continuum.some`
just exhibits a `Continuation` choice without additional hypotheses. -/
structure Continuation (G:Gauge) extends XSpace.Initialize G where
    optics : MS.Land.Booked (Press.portDeck G)
    data : MS.Land.MS_Data G optics

def some (G:Gauge) := let q:= Classical.choice (MS.Land.suitable (Press.portDeck G)); Continuation.mk ( XSpace.Initialize.standard G ) q (Classical.choice (MS.Land.bookedMS q))

end YM.FVA2.Continuum
