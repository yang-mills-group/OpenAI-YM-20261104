import YM.SignedWilsonExpansion.Camera.Pouch
import YM.SignedWilsonExpansion.Sat.Trail
import YM.SignedWilsonExpansion.Sat.Blank
import YM.SignedWilsonExpansion.Sat.Flash
set_option autoImplicit false
set_option maxHeartbeats 150000
noncomputable section
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
local notation "ζL" => (lPersh ℱ Y)
local notation "Uψ" => ( ( liftV ( needle G ∘ r ) )^b )
namespace Cello
variable (t:Tags G d (n+1)) (K:B.hired n)(u:Set (Points (n+1)))(R':Path.Roi u)(W₀:u⊆interior (B.Arena n K).F) (h₀:( A e ).home =ᶠ[ℱ] r)
-- through entire bought interior. CAMERA in W frame. learner (Marque earned) postdefined.
open Path
include M
abbrev sage {n:ℕ} (t: Tags G d n)(i:Visual ι)(x:Points n):= Path.mote ( FVA2.Scale.Measure.start X P d ) M.q x ( M.θU i ) ( ( M.liftQ e i d ) ∘ t )
abbrev play (i:Visual ι)(x:Points (n+1)):= levelOf F W (liftV r) i d (n+1) x t
abbrev Diff (i:Visual ι) := play (F:=F) (W:=W) (r:=r) t i-sage M e t i -- nodal differences
private lemma sageAt (i:Visual ι)(x:Points (n+1)) : M.revenue (fun j=>d) (fun _=> ⟨ M.ep_Pos,le_rfl⟩ ) (fun _=> e) t x i=sage M e t i x:= rfl
include lead hr Y₀ Z' z' h' h₀
lemma taughtMesh : Ping.shown ζL ( B.Arena n K ).F ( Diff (F:=F) M e t ) Uψ (liftV ( sizeP r M.F R.family.S )):=by
    intro ε h; filter_upwards [ M.firstV.eventually h₀, M.fullCharge lead hr Y Y₀ h' Z' z' (fun _=> d) ( fun _=>⟨ M.ep_Pos,le_rfl⟩ ) (fun _=> e) K t ε h ] with i hi hv z hx
    let C':= (A e).home; have ht:( r i.1 )≠0:= (p _|>.ne'); let x:=plot r M.F (fun _=> z) R.family.S i.1; have he:∀ v: Points (n+1), play (F:=F) (W:=W) (r:=r) t i v= ΩW F W A (fun _=>e) (fun _=>d) r i.1 v t:=by
       intro v; change S'.classMoment _ _ _ _ = S'.classMoment _ (fun _=>d) _ _; apply congrArg _; funext j; change walk W (r i.1) d ( t j )=walk W ((A e).home i.1) d ( Level.Dial d ( jumpY W (A e) r i.1 ) (t j) ); change (A e).home i.1=r i.1 at hi; rw [jumpY,hi,div_self ht,Real.log_one,Level.flat]; rfl
    change ‖play (F:=F) (W:=W) (r:=r) t i x-sage M e t i x‖ ≤ ε * ‖needle G ( r i.1 )^b‖ -- annotations
    rw [ he,← sageAt ]; exact hv z hx
-- support property on all of interior. know on boundary? not needed
include W₀ R'
lemma taughtReal : Serves ζL (play (F:=F) (W:=W) (r:=r) t) ( sage M e t ) u Uψ:=by
    intro ε h; let δ:=sizeP r M.F R.family.S; let hφ:= M.sharpen Y Y₀; have hu:Tendsto (liftV δ) ζL (𝓝 0):=(M.locationH hr).comp M.firstV; let hL:= (B.Arena n K).F; 
    -- fork
    have hC := (B.Arena n K).roi; have hp:Iris.Calm ζL ( Diff (F:=F) M e t ) hL:= Iris.sub ( Iris.blink lead hC (hr.comp M.firstV) t ) ( Iris.paid X P Q M.U'.hG hC (fun i=> income (monoY ( M.washedP lead hr Y h' Z' z' e M.ep_Pos le_rfl ( t i ) ) hφ)) (M.cent_t.mono_left hφ) M.q )
    let M' := liftV (needle G∘r); have hD(i: Visual ι): 0<liftV δ i:= div_pos ( R.family.S.a_pos _ ) (p _); have hE : liftV δ=O[ζL] M':= IsBigO.of_bound' ((M.firstV.eventually M.camera).mono (fun i u=> (Real.norm_of_nonneg (hD i).le).trans_le ((show liftV δ i≤M' i from u).trans (le_abs_self ..)))) -- cast abs
    have hh: ((liftV δ)^(b+1))=o[ζL] Uψ:= (hE.pow (b+1)).trans_isLittleO ( Wipe.expense ( ( M.needle_clock hr ).comp M.firstV ) IsEquivalent.refl ( Nat.lt_succ_self b ) )
    obtain ⟨C,pC,o⟩:= hp.cost (b+1); exact Ping.extendsOn hu (Diff (F:=F) M e t) (hp.smooth.mono fun i hi x hx=> hi x ( interior_subset hx )) ⟨ C,pC,o.mono fun i hi x hx=>hi x ( interior_subset hx )⟩ (taughtMesh lead hr Y Y₀ h' Z' z' M e t K h₀) hh (Eventually.of_forall hD) R'.1 W₀ ε h -- check `Iris.Calm`
end Cello
end Estate
end YM.SignedWilsonExpansion.Camera
