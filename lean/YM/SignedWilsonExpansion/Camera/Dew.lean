import YM.SignedWilsonExpansion.Camera.Cabinet
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
include M
local notation "ϰ" => ( ( liftV ( needle G∘r ) )^b )
abbrev lPersh (L:Filter ι)(Y:Ultrafilter (ℕ×ℕ)):= L.curry (Y:Filter (ℕ×ℕ))
local notation "ΠF" => (lPersh ℱ Y)
include Y₀
lemma sharpen : lPersh ℱ Y ≤ alongT ℱ f:=by
     apply le_def.mpr; intro s hs; change ∀ᶠ i in ℱ,∀ᶠ p in (Y:Filter _),(i,p) ∈ s; change ∀ᶠ i in ℱ,∀ᶠ p in ( track f ).fuse,(i,p)∈ s at hs; exact hs.mono fun i h=> (h.filter_mono Y₀) -- cast
omit Y₀
variable (S:Fin (n+1)→ℕ)(s:∀i,0<S i∧ S i≤d)(p':Fin (n+1)→L) (k': B.hired n)(ξ:ι→ Shake (n:=n+1)) (L':pad0 ( B.Arena n k' ) r M.F ξ ℱ R.family.S)(T':∀ i,Sec G (S i))
abbrev virtQ (v: Scale n)(z: Visual ι): Point G d n:= orbit (Measure.start X P d) M.q v ( M.θU z )
abbrev leafsT (z:Visual ι): Tags G d (n+1):=fun j=> up (s j).2 (M.wrapW (S j) (p' j) z ( T' j ))
abbrev revenue (x:Points (n+1))(z:Visual ι):= Path.mote (Measure.start X P d) M.q x ( M.θU z ) ( M.leafsT S s p' T' z )
include h' hr lead z' Z' L' s
-- Extend environment to Υ limit. No moving r approximation at continuum.L_
lemma stakesT : (fun i=> M.estateV S p' k' ξ i (fun t=> wear W A r i.1 (p' t) (S t) (T' t))- M.virtQ ( M.Padded k' ξ i.1 ) i ( M.leafsT S s p' T' i ))=o[μ₀] ϰ:=by
     let U(i:Visual ι)(j:Fin (n+1)):= M.dressed (S j) (p' j) i ( T' j ); let Y₁(i):= Normalize.up M.club.rung ∘ M.leafsT S s p' T' i; let Q'(i:Visual ι):= M.orbit_est ( M.Padded k' ξ i.1 ) i
     have hp(t:Tags G M.h (n+1)): (fun i=> Q' i t)=O[μ₀](1:Visual ι→ℝ):= discards X P M.U'.hG Q (liftV ( M.Padded k' ξ )) ( B.Arena n k' ).F ( B.Arena n k' |>.roi ).1 ( B.Arena n k'|>.roi ).2 ( by
         have p:= (stamp_p ( B.Arena n k' ) C₀ r M.F ξ L'); filter_upwards [ M.firstV.eventually p, M.firstV.eventually L' ] with i hv hi; exact hv.symm ▸ hi ) t ( Wipe.stop M.cent_t )
     have hx (j:Fin (n+1)): Salary ℂ μ₀ 1 (fun i=> Y₁ i j) := translates ( income (washedP lead hr Y h' Z' z' M (p' j) (s j|>.1) (s j|>.2) ( T' j ) )) ( Normalize.up ( ( s j ).2.trans M.club.rung ) ); refine ( matPays (p:=U) hp hx (fun j=> income ( formal lead hr Y h' Z' z' M (p' j) (s j|>.1) (s j|>.2) ( T' j ) )) (fun j=> M.hems hr Y h' (p' j) (s j|>.1) (s j|>.2) (T' j)) ).congr_left (?_); intro i; rw [lens]; rw [show M.virtQ ( M.Padded k' ξ i.1 ) i (M.leafsT S s p' T' i)=Q' i (Y₁ i) from Drawing.increases X P M.U'.hG Q _ M.club.rung _ _ ]; rfl
include Y₀
lemma reportedP : (fun i:Visual ι=> ΩW F W A p' S r i.1 ( plot r M.F ξ R.family.S i.1 ) T'-M.virtQ ( M.Padded k' ξ i.1 ) i ( M.leafsT S s p' T' i ))=o[ lPersh ℱ Y ] ϰ:=by
      have hx:∀ᶠ i in ℱ,0 < needle G (r i)^b:= hr.eventually (( implicit_clock M.U'.hG ).positive.mono fun i hi=> pow_pos hi b)
      let v(i:Visual ι) j:= wear W A r i.1 (p' j) (S j) (T' j); let M' (i):= M.estateV S p' k' ξ i ( v i ); let Ty' (i):= cameraV W A p' S M.F ξ r i ( v i ); have hv:= ( M.horizon S p' k' ξ s L' v ( fun i=> income ( M.buyUp hr Y h' ( p' i ) ( s i|>.2 ) ( T' i ) ) ) )
      have hu:= earnedPrice Y p' S ( B.Arena n k' ) M.F ξ hr F W H A Y₀ h' L' M.U'.hG Z' hx (fun _=>T') (fun i=>(s i).2)
      refine ( hu.add ((( hv.add ( stakesT lead hr Y h' Z' z' M S s p' k' ξ L' T' ) ).mono ( M.sharpen Y Y₀ ))) ).congr ?_ (fun i=>rfl); intro i; change _-Ty' i+(Ty' i - M' i+( M' i - _))=_; abel
lemma repoint : (fun i:Visual ι=> ΩW F W A p' S r i.1 ( plot r M.F ξ R.family.S i.1 ) T'-M.revenue S s p' T' ( plot r M.F ξ R.family.S i.1 ) i )=o[lPersh ℱ Y] ϰ:=by
      refine ( M.reportedP lead hr Y Y₀ h' Z' z' S s p' k' ξ L' T' ).congr' ( ?_ ) ( .refl .. ); filter_upwards [ M.firstV.eventually ( stamp_p ( B.Arena n k' ) C₀ r M.F ξ L' ) ] with i hi; refine congrArg (fun z:ℂ=> _-z) (?_); unfold revenue; rw [← show (M.Padded k' ξ i.1).val=_ from hi,Path.pollen]
omit L' in
lemma fullCharge : ∀ ε:ℝ,0<ε → ∀ᶠ i in (lPersh ℱ Y),∀ x:Shake (n:=n+1),Extraction.tag (sizeP r M.F R.family.S i.1) x∈ zone ( B.Arena n k' )→ ‖(ΩW F W A p' S r i.1 (plot r M.F (fun _=> x) R.family.S i.1) T'- M.revenue S s p' T' (plot r M.F (fun _=> x) R.family.S i.1) i)‖ ≤ ε * ‖needle G (r i.1)^b‖ :=by
    intro ε p; -- `p` variable
    exact allP ( B.Arena n k' ) r M.F (M.locationH hr) ( hr.eventually self_mem_nhdsWithin ) ( fun i v u=> ‖(ΩW F W A p' S r i ( plot r M.F (fun _=>u) R.family.S i ) T'- M.revenue S s p' T' ( plot r M.F ( fun _=>u ) R.family.S i ) (i,v))‖≤ ε * ‖needle G (r i)^b‖ ) fun x h=> ( M.repoint lead hr Y Y₀ h' Z' z' S s p' k' x h T' ).bound p
omit s L' Y₀ Z' z'
-- along outer. correct assignments for Ω at all cap choices
lemma grow_Ω (s:∀ i,S i≤d): ∀ᶠ i in ℱ,∀ x∈ conf _, ΩW F W A p' S r i x T'=ΩW F W A p' ( fun _=>d ) r i x (fun j=> Normalize.up (s j) ( T' j )) :=by
      -- use W leading & dial chain. `t` tuner irrelevant.Snapshot.Macro
      filter_upwards [ eventually_all.mpr (fun i=> risePlot lead ( s i ) ( compare_pivot hr ((h' ( p' i )).pivots) |>.1 )) ] with i hi x hx; let T (j):= T' j;
      let w(j):= walk W ((A (p' j)).home i) (S j) ( Level.Dial (S j) (jumpY W (A (p' j)) r i) (T j) ); let W'(j):=walk W ((A (p' j)).home i) d ( Level.Dial d ( jumpY W (A ( p' j )) r i ) ( Normalize.up ( s j ) ( T j ) ) ); change S'.classMoment S' S _ w=S'.classMoment S' (fun _=> d) ( r i • x ) W'; have hp(j): W' j=F.sector.derivatives.rise (s j) ( w j ):=by unfold W' w; rw [Level.chain]; exact hi j _
      rw [funext hp]; exact (AllOrder.Leading.moment_inclusion F.room.kernel.laws.toSymmetric F.phase.transport.injection s (Work.A05.smul_conf (p i) hx) w).symm
end Estate
end YM.SignedWilsonExpansion.Camera
