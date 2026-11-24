import YM.ForFlash.F9.Comparison
import YM.SignedWilsonExpansion.Camera.Void
/-! # Read the price through this horizon of marks and poses

Unlike `Padded` accepts the supplied Stage along with its moving polynomial geometry.
The Estate and all its tuner caps and compact certificates (purchased before measuring at
these poses) are *not* being modified to read about the growing `Covers`. Keep a joint reception
of a further itinerary (at this same K, D, axes, height,...) in `BoughtForFlash`.
Retain compact estimates while reading these, e.g., it's not enough to have got some separately
certified leading-frame adjustment on the compacts then some other here.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option quotPrecheck false
noncomputable section

/- Adapted YM/SignedWilsonExpansion/Camera/Void.lean -/
namespace YM.SignedWilsonExpansion.Camera
open Function Set Filter MeasureTheory Extraction Climb Spec Table Next.UVStress OPE.Levy Trace.Pilot PhysMS PhysMS.Frame
open MergeProof.East Next.Rank Ward Next.Rank.East Pert.Scale Maxwell Extra.FD PhysicalNext.Repeat.Legato Run Lattice FullVolume Cells Homes
open XSpace Commission Dancer Dancer.Motif Dancer.Supper Dancer.Drawing Asymptotics Dancer.Stitch
open WilsonCoeffUV WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Xa MarqueQ MarqueQ.PorchK WilsonCoeffUV.Bank PathCost
open Wilson RG PowerSeries Purchases UVClock PurchVoice Schedules HalfRoof HalfRoof.Minty WardBin Source Labels Normalize
open FVA2 FVA2.Dframe SeatsW Dancer.Shell Dancer.Fort XSpace.Cirrus
open Kane.Tilted Belle Belfry Belfry.ScaleFits StageG
open scoped Topology ContDiff Classical BigOperators
open FVA2.Scale Level Maxwell.Free Future Gauge Dancer.Coats SignedWilsonExpansion.Fire
variable {G:Gauge}{d t n b:ℕ}{ι L J:Type}{ℱ:Filter ι}
open MS MS.Puff MS.High MS.Native MS.Land MS.Fleet MS.Book WilsonCoeffUV.Cosmos.Polestar Precision XSpace.Structure1
variable {c a:Axis}{e u k q h K:ℕ}
variable {X:Initialize G}{T:∀ h,Rays G h X.hol} {C:Family G} {f:Extraction.Order} {S':Table C.book}(F:Final C f S')(W:ℝ→tower S') (H:(Bel C.book).Hierarchy) (lead:Leading F W)
variable (A: L→Shawl C S' ι W) {r:ι→ℝ}(hr:Tendsto r ℱ trail) (p:∀ i,0<r i)
variable (U:Normalize.Store G)(P:Rose.Pick U){Ω:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))} {J':MS.Land.Prescription (Press.portDeck G)}(Q:Speed.Quoted X P Ω J')
variable (B:Plans a)(X₀:ChartRatio G)
variable (M : Estate W H A U P X₀ B f ℱ r p Q T b d)
namespace Estate
variable {F W H A U P X₀ B p Q}
local notation "μ₀" => alongT ℱ f
local notation "C₀" => (liftV (needle G∘r))^b

include M
local notation "lpB"=> ( cck G ∘ liftV r )
abbrev ReserveForFlash := Cooking.RoomForFlash M.U' (alongT ℱ f) (cck G ∘ liftV r) M.k1 M.Wν (liftV r) (fun i=>p i.1) X T C.labels M.h M.k
abbrev BoughtForFlash (S:Fin (n+1)→ℕ)(P':Fin (n+1)→L)(x:ι→Fin (n+1)→ Cover) := Presented C X₀ S (liftV x) (fun i=>liftV ( A ( P' i ) ).station) ( M.R₁∘P' ) (fun i=> liftV (M.j ( P' i ))) M.q M.k M.e (loN ι) (lop ι) (liftV M.F) (liftV M.D) (liftV M.v) (alongT ℱ f) (( liftV (needle G ∘ r) )^b)

/- Adapted YM/SignedWilsonExpansion/Camera/Void.lean -/
variable (U':Fin (n+1)→ℕ)(T':Fin (n+1)→L) (hn:B.hired n)(x:ι→ Shake (n:=n+1))(V₁:∀ i,0<U' i∧ U' i≤d) (Z':MovesIn ℱ (cck G∘r) (plot r M.F x C.S)) (y:ι→Scale (n+1))(v₀:∀ᶠ i in ℱ,(y i).val=plot r M.F x C.S i)
abbrev estateVForFlash (i:Visual ι) : MultilinearMap ℂ (fun i=> Sec G ( U' i )) ℂ := highEst C U' (liftV y) U P M.y (πP W A T') (πS W A T') (pvV M.j T') (pvV M.l T') ( fun i=> M.R₁ ( T' i ) ) M.q d (loN ι) (lop ι) (liftV M.v) (liftV r) i
include Z' v₀
lemma poseHoldForFlash
    (Room:M.ReserveForFlash):
    TollQ.SeatsForFlash μ₀ (picture M.k1 M.Wν (liftV M.F) (liftV x) M.U'.draws (fun i=>p i.1)) (liftV y) ∧ MovesIn μ₀ lpB (fun i=> Garden (hereD M.U'.draws (liftV r) (liftV M.F) i) (liftV x i)) ∧ (∀ᶠ i:Visual ι in μ₀,(y i.1).val=Garden (hereD M.U'.draws (liftV r) (liftV M.F) i) (liftV x i)):=by
    let F':= M.club.camp; have hL:= F'.yonderK.spectrum T _ M.y; have hx: ∀ i:Visual ι, plot r M.F x C.S i.1=Garden (hereD M.U'.draws (liftV r) (liftV M.F) i) (liftV x i):=fun i=>by rw [ M.draw ]; rfl
    have hz:= ( ( Z'.comp ( M.firstV (R:=(track f).fuse) ) ).tee (Eventually.of_forall hx)); have hp:(fun i:Visual ι=>(y i.1).val)=ᶠ[μ₀] (fun i=> Garden (hereD M.U'.draws (liftV r) (liftV M.F) i) (liftV x i)):=(( M.firstV.eventually v₀ ).mono fun i hi=> hi.trans (hx i))
    exact ⟨ artForFlash _ T F'.timeRise F'.meshP Room (hL.mono fun i ⟨_,_,_,x,t,r⟩=> t.trans (r.trans x) ) (liftV y) (hL.mono fun i ⟨_,_,q,w,_,_⟩=>q.trans w ) _ hz hp, hz,hp ⟩
include hn V₁
lemma horizonForFlash (Room:M.ReserveForFlash)(Booked:M.BoughtForFlash U' T' x) (v:Visual ι→ (i:Fin (n+1))→Sec G (U' i))(p₀:∀i,Salary ℂ (alongT ℱ f) 1 (fun j=> v j i)):
     (fun i=> cameraV W A T' U' M.F x r i (v i)- M.estateVForFlash U' T' y i (v i))=o[alongT ℱ f] ((liftV ( needle G∘ r ))^b):=by
       apply ecclesia U' (𝒜:= cameraV W A T' U' M.F x r) (𝒜':= M.estateVForFlash U' T' y) ( ?_ ) v p₀; intro w; obtain ⟨_,hm,hT⟩:= M.poseHoldForFlash x Z' y v₀ Room; exact psΓForFlash C X₀ U' (track f) H (liftV x) (liftV y) U P Q M.y (πP W A T') (πS W A T') (pvV M.j T') (pvV M.l T') (fun i=> M.R₁ ( T' i )) C.params _ M.he M.merit M.club M.hG (fun i=>M.seen _) (fun i=> M.firstV.eventually ( M.pupil _ )) M.draw M.paid V₁ ( M.holds _ hn _ V₁ ) M.vest Room hm hT Booked w -- check unit rewrite
end Estate
end YM.SignedWilsonExpansion.Camera

end
