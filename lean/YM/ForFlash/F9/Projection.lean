import YM.ForFlash.F9.Horizon
import YM.SignedWilsonExpansion.Camera.Dew
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

/- Adapted YM/SignedWilsonExpansion/Dancer/Dial.lean -/
namespace YM.SignedWilsonExpansion.Dancer.Drawing
open XSpace XSpace.Structure1 Normalize Future Gauge Filter Function Matrix MeasureTheory
open Asymptotics Shell Lights SeatsW Fort Coats Commission Maxwell Maxwell.Free Maxwell.Wick
open FVA2 FVA2.Scale FVA2.Dframe
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open WilsonCoeffUV.Mer.Xa WilsonCoeffUV.Mer.Xa.MarqueQ PorchK Crops Crops.Taught
open scoped BigOperators Topology ContDiff Classical
variable {G:Gauge}{n h m q b d:ℕ}{a:Axis}{ι:Type}{l:Filter ι}
open Commission.Gram
variable (W': Initialize G) {N: Normalize.Store G} (K: Rose.Pick N) (s:G.Simple)
variable {Y:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))} {S:Prescription (Press.portDeck G)} (P:Speed.Quoted W' K Y S)
variable (Q : Way G d)
variable {g:ι→ℝ}{V:Set (Points n)} {p:ι→ Stage n} {x:Stage n}
local notation "Q₁"=> FVA2.Scale.Measure.start W' K d
include P s
lemma discardsForFlash (p:ι→Stage n)(v:ι→XSpace.Cirrus.Sample n) (hp:TollQ.SeatsForFlash l v p)(w:Tags G d n) (y:g=O[l] (1:ι→ℝ)) : (fun i=> Print W' K q (p i) ( g i ) w)=O[l] (1:ι→ℝ) :=by
       simp_rw [Print,atW]
       have hy:(fun i=>( g i:ℂ ))=O[l] (1:ι→ℝ):= IsBigO.trans ( g:=g ) (IsBigO.of_bound' (Eventually.of_forall fun i=> (Complex.norm_real _).le)) y
       apply IsBigO.sum; intro i _; suffices hx: (fun i'=> Q₁ n (p i') i w)=O[l] (1:ι→ℝ) by simpa only[Pi.one_apply,one_pow,mul_one] using! (hy.pow i).mul hx
       exact (TollQ.priceForFlash s W' K Y S 0 P v p hp w i).2
end YM.SignedWilsonExpansion.Dancer.Drawing

/- Adapted YM/SignedWilsonExpansion/Camera/Grain.lean -/
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
section phases
variable {f:Extraction.Order} (Y:Ultrafilter (ℕ×ℕ)) (P: Fin (n+1)→ L) (S:Fin (n+1)→ℕ) (Z:Pad (n+1))(g:ι→ℕ)(x:ι→ Shake (n:=n+1)) {r:ι→ℝ}(hr:Tendsto r ℱ trail)
variable {R:Run G} {S': Table R.family.book}(F:Final R.family f S')(W:ℝ→tower S') (H:(Bel R.family.book).Hierarchy) (lead:Leading F W)
variable (A: L→Shawl R.family S' ι W)(Y₀:(Y:Filter _)≤ (track f).fuse)(Q:∀ a:L,Shine (f:=f) W H (A a) Y r ℱ d) (z:∀ᶠ i in ℱ, plot r g x R.family.S i∈ conf _)
local notation "C₀" => R.family
variable (s:G.Simple)(u':(track f).PointLimits R.family S')
include Y₀ Q z hr s u'
lemma governForFlash (T:ι→ (j:Fin (n+1))→ Sec G (S j)) (hv:∀j,S j ≤ d): ∀ᶠ i:ι in ℱ,
     Tendsto (fun p:ℕ× ℕ=> cameraV W A P S g x r (i,p) (fun j=> wear W A r i (P j) (S j) (T i j))) (Y:Filter _) (𝓝 ( ΩW F W A P S r i (plot r g x R.family.S i) (T i) )):=by
      let st j:= A (P j); filter_upwards [z, hr.eventually self_mem_nhdsWithin, eventually_all.mpr (fun j=> ( Q ( P j ) ).contact (hv j)),eventually_all.mpr (fun j=> lamp W H (st j) Y hr ( Q ( P j ) ) (hv j))] with i hz hp hY hQ; let X(j:Fin (n+1)):= wear W A r i ( P j ) ( S j ) ( T i j ); let B:= plot r g x R.family.S i; let a0(j):= pre C₀ (X j); let V(j):= gear R.family.labels (S j) (r i/(st j).home i) ( a0 j ); choose y cap openY using (fun j=> hY j (V j)); let m:= (Y:Filter (ℕ×ℕ)); let v':=office C₀ r g x i hp
      have hh : r i • B∈conf (n+1):= Work.A05.smul_conf hp hz
      rw [show ΩW F W A P S r i B (T i)= S'.value S (Order.grid C₀ ( g i ) ( x i )) y from ?_ ] -- let B rw rewrite? Might goal not match.
      · let Λ(p:ℕ×ℕ):=R.family.ensemble S (fun j=> Cells.location R.family.S (g i) p.1 p.2 (x i j)); let A'(p:ℕ×ℕ) j:= ((st j).station i).microphone p ( S j ) ( V j ); change Tendsto (fun p=> Λ p ( A' p )) _ _; exact Next.UVStress.tendsto_multi _ Λ (fun v=> S'.value S (Order.grid C₀ ( g i ) ( x i )) v) (fun v=> (tie_bill R s F.room.kernel u' ( x i ) (v' ▸ hh) S v).mono_left Y₀) y A' cap
      unfold ΩW sPlot; rw [← v']; let w:= fun j=> (st j).legs i (S j) ( V j ); change S'.classMoment S' S _ (fun j=> walk W ((st j).home i) (S j) (_))= _; trans S'.classMoment S' S (r i • B) w; · exact congrArg (S'.classMoment S' S ( r i • B )) (funext fun j=> ( hQ j ( T i j ) ).symm)
      rw [show w=(fun j=> S'.project _ ( y j )) from funext fun j=> (openY j).symm]; exact S'.at_project S' F.room.kernel.laws.toSymmetric (fun _=> le_refl _ ) hh (fun i=> ⟨ S i,y i ⟩)
lemma earnedPriceForFlash {ε:ι→ℝ}(he:∀ᶠ i in ℱ,0<ε i) (T:ι→ (j:Fin (n+1))→ Sec G (S j)) (hv:∀j,S j ≤ d):
 (fun i:Visual ι=> ΩW F W A P S r i.1 ( plot r g x R.family.S i.1 ) ( T i.1 )-cameraV W A P S g x r i (fun j=> wear W A r i.1 (P j) (S j) (T i.1 j))) =o[ℱ.curry (Y:Filter (ℕ×ℕ))] liftV ε:=by
     refine IsLittleO.of_bound fun b hb=>?_ ; rw [eventually_curry_iff]; -- he probably b eventually property |; view
     filter_upwards [he,governForFlash (r:=r) Y P S g x hr F W H A Y₀ Q z s u' T hv] with i h p; refine (Metric.tendsto_nhds.mp p ( b * ε i ) ( mul_pos hb h ) ).mono fun j hi=>?_ ; rw [dist_eq_norm,norm_sub_rev] at hi; exact hi.le.trans_eq (by rw [liftV, comp_apply, Real.norm_eq_abs,abs_of_pos h])
end phases
end YM.SignedWilsonExpansion.Camera

/- Adapted YM/SignedWilsonExpansion/Camera/Dew.lean -/
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
open Matrix
variable {R:PhysicalNext.Repeat.Legato.Run G}{X:Initialize G}{T:∀ h,Rays G h X.hol} {f:Extraction.Order} {S':Table R.family.book}(F:Final R.family f S')(W:ℝ→tower S') (H:(Bel R.family.book).Hierarchy) (lead:Leading F W)
variable (A: L→Shawl R.family S' ι W) {r:ι→ℝ}(hr:Tendsto r ℱ trail) (p:∀ i,0<r i) (Y:Ultrafilter (ℕ×ℕ))(Y₀:(Y:Filter _)≤ (track f).fuse)(h':∀ a:L,Shine (f:=f) W H (A a) Y r ℱ d)
variable (U:Normalize.Store G)(P:Rose.Pick U){Ω:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))} {J':MS.Land.Prescription (Press.portDeck G)}(Q:Speed.Quoted X P Ω J')
variable {C:Family G} (B:Plans a)(X₀:ChartRatio G)(Z':(track f).PointLimits R.family S')(z':(track f).Ordered R.family S')
variable (M : Estate W H A U P X₀ B f ℱ r p Q T b d)
namespace Estate
open Gram Lights
variable {F W H A U P X₀ B p Q }
local notation "μ₀" => alongT ℱ f
local notation "C₀" => R.family
variable (x:ι→ Shake (n:=2))(w: Tendsto (plot r M.F x R.family.S) ℱ (𝓝 ( Gram.nodes a ))) (e:L) -- always Nick.Horiz
include M
local notation "ϰ" => ( ( liftV ( needle G∘r ) )^b )
local notation "ΠF" => (lPersh ℱ Y)
variable (S:Fin (n+1)→ℕ)(s:∀i,0<S i∧ S i≤d)(p':Fin (n+1)→L) (k': B.hired n)(ξ:ι→ Shake (n:=n+1)) (L':MovesIn ℱ (cck G∘r) (plot r M.F ξ R.family.S)) (Room:M.ReserveForFlash)(Yp':ι→Scale (n+1))(Yp:∀ᶠ i in ℱ,(Yp' i).val=plot r M.F ξ R.family.S i)(T':∀ i,Sec G (S i))
include h' hr lead z' Z' L' s k' Room Yp
-- Extend environment to Υ limit. No moving r approximation at continuum.L_
lemma stakesTForFlash : (fun i=> M.estateVForFlash S p' Yp' i (fun t=> wear W A r i.1 (p' t) (S t) (T' t))- M.virtQ ( Yp' i.1 ) i ( M.leafsT S s p' T' i ))=o[μ₀] ϰ:=by
     let U(i:Visual ι)(j:Fin (n+1)):= M.dressed (S j) (p' j) i ( T' j ); let Y₁(i):= Normalize.up M.club.rung ∘ M.leafsT S s p' T' i; let Q'(i:Visual ι):= M.orbit_est ( Yp' i.1 ) i
     have hp(t:Tags G M.h (n+1)): (fun i=> Q' i t)=O[μ₀](1:Visual ι→ℝ):= discardsForFlash X P M.U'.hG Q (liftV Yp') _ ( M.poseHoldForFlash ξ L' Yp' Yp Room ).1 t ( Wipe.stop M.cent_t )
     have hx (j:Fin (n+1)): Salary ℂ μ₀ 1 (fun i=> Y₁ i j) := translates ( income (washedP lead hr Y h' Z' z' M (p' j) (s j|>.1) (s j|>.2) ( T' j ) )) ( Normalize.up ( ( s j ).2.trans M.club.rung ) ); refine ( matPays (p:=U) hp hx (fun j=> income ( formal lead hr Y h' Z' z' M (p' j) (s j|>.1) (s j|>.2) ( T' j ) )) (fun j=> M.hems hr Y h' (p' j) (s j|>.1) (s j|>.2) (T' j)) ).congr_left (?_); intro i; change Q' i (U i)-Q' i (Y₁ i)= Q' i (U i)-_; rw [show M.virtQ ( Yp' i.1 ) i (M.leafsT S s p' T' i)=Q' i (Y₁ i) from Drawing.increases X P M.U'.hG Q _ M.club.rung _ _ ]
variable (Booked:M.BoughtForFlash S p' ξ)
include Y₀ Booked
lemma reportedPForFlash : (fun i:Visual ι=> ΩW F W A p' S r i.1 ( plot r M.F ξ R.family.S i.1 ) T'-M.virtQ ( Yp' i.1 ) i ( M.leafsT S s p' T' i ))=o[ lPersh ℱ Y ] ϰ:=by
      have hx:∀ᶠ i in ℱ,0 < needle G (r i)^b:= hr.eventually (( implicit_clock M.U'.hG ).positive.mono fun i hi=> pow_pos hi b)
      let v(i:Visual ι) j:= wear W A r i.1 (p' j) (S j) (T' j); let M' (i):= M.estateVForFlash S p' Yp' i ( v i ); let Ty' (i):= cameraV W A p' S M.F ξ r i ( v i ); have hv:= ( M.horizonForFlash S p' k' ξ s L' Yp' Yp Room Booked v ( fun i=> income ( M.buyUp hr Y h' ( p' i ) ( s i|>.2 ) ( T' i ) ) ) )
      have hu:= earnedPriceForFlash Y p' S M.F ξ hr F W H A Y₀ h' ( Yp.mono fun i hi=> hi ▸ (Yp' i).property ) M.U'.hG Z' hx (fun _=>T') (fun i=>(s i).2)
      refine ( hu.add ((( hv.add ( stakesTForFlash lead hr Y h' Z' z' M S s p' k' ξ L' Room Yp' Yp T' ) ).mono ( M.sharpen Y Y₀ ))) ).congr ?_ (fun i=>rfl); intro i; change _-Ty' i+(Ty' i - M' i+( M' i - _))=_; abel
lemma repointForFlash : (fun i:Visual ι=> ΩW F W A p' S r i.1 ( plot r M.F ξ R.family.S i.1 ) T'-M.revenue S s p' T' ( plot r M.F ξ R.family.S i.1 ) i )=o[lPersh ℱ Y] ϰ:=by
      refine ( M.reportedPForFlash lead hr Y Y₀ h' Z' z' S s p' k' ξ L' Room Yp' Yp T' Booked ).congr' ( ?_ ) ( .refl .. ); filter_upwards [ M.firstV.eventually Yp ] with i hi; refine congrArg (fun z:ℂ=> _-z) (?_); unfold revenue; rw [← show (Yp' i.1).val=_ from hi,Path.pollen]
end Estate
end YM.SignedWilsonExpansion.Camera

end
