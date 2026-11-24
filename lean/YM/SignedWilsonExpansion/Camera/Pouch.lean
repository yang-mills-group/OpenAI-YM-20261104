import YM.SignedWilsonExpansion.Camera.Dew
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
abbrev liftQ (l:L)(i:Visual ι): Veto.caps G:= fun t=> M.wrapW t l i
abbrev firmQ (i:Visual ι): Point G d 2:= M.virtQ ( M.Padded B.leading x i.1 ) i
include M
lemma ep_Pos : 0 < d:= (show 0<6 from by norm_num).trans_le M.club.leader -- implicit M include
variable (Y1:(Y:Filter _)≤ (track f).fuse)
include M lead Z' z' hr h' w Y₀
lemma iterate (y:Sec G t)(p₀:Sec G d)(v:t≤d)(p:0<t) :
     (fun i=>Paar ( M.firmQ x i ) (M.wrapW d e i (up v y)) ( M.wrapW d e i p₀ )-Paar ( M.firmQ x i ) ( up v ( M.wrapW t e i y ) ) ( M.wrapW d e i p₀ ) )=o[ζL] Uψ:=by
      let S:=![ t,d ]; have hD(i):0< S i∧ S i≤d:= by fin_cases i; exact ⟨p,v⟩; exact ⟨M.ep_Pos,le_rfl⟩
      let T (i:Fin 2):= d; let p'e(i:Fin 2):= e; let X:= plot r M.F x R.family.S; let A0:∀ i,Sec G (S i):= Fin.cons (α:=fun i=> Sec G (S i)) y (Fin.cons p₀ (fun i=> Fin.elim0 i)); let x':Tags G d 2:= fun i=> up ( hD i ).2 ( A0 i );
      have hx:=M.passed x w; have he:= (( M.reportedP lead hr Y Y₀ h' Z' z' S hD p'e _ x hx A0 ).sub ( M.reportedP lead hr Y Y₀ h' Z' z' T (fun i=>⟨ M.ep_Pos,le_refl d ⟩) p'e _ x hx x' ))
      refine IsLittleO.congr' he ( ?_ ) ( .refl .. ); have hp:= M.grow_Ω lead hr Y h' S p'e A0 (fun i=> (hD i).2); filter_upwards [ M.firstV.eventually hp, M.firstV.eventually hx ] with i hi h1
      change ΩW F W A p'e S r i.1 (X i.1) A0- _ - (ΩW F W A p'e T r i.1 ( X i.1 ) x'-_) = _; have hu : X i.1 ∈ conf _:= ( B.Arena 1 B.leading |>.roi ).2 h1; rw [ hi _ hu ]; let P:= M.firmQ x i; let B':= up v y
      have hz : M.leafsT S hD p'e A0 i = ![up v ( M.wrapW t e i y ), M.wrapW d e i p₀] := funext fun j=>by fin_cases j <;> rfl
      have ht: M.leafsT T (fun i=>⟨M.ep_Pos,le_rfl⟩) p'e x' i = ![ M.wrapW d e i B', M.wrapW d e i p₀ ]:= funext fun j=>by fin_cases j <;> rfl
      rw [hz,ht]; unfold Paar; abel
lemma embassy : Veto.Marque a ζL Uψ ( M.liftQ e ) ( M.firmQ x ):=by
    let he:= M.sharpen Y Y₀; let H:= M.shinesW lead hr Y h' Z' z' e M.ep_Pos (le_refl d); refine ⟨?_,⟨M.tiny.mono he, (fun x=>monoY (H.limits x) he),fun s v k=>?_,fun v k=>?_,fun k=>?_⟩,fun t u v y p₀=> iterate lead hr Y Y₀ h' Z' z' M x w e y p₀ v u ⟩
    · exact Dancer.Shell.emblemY ( Drawing.emblem X P M.U'.hG Q M.cent_t (( M.anchorT x w ).comp M.firstV) ) he -- notation expects lemma section? check
    · exact ( H.spin s v k ).mono he
    · exact ( H.reo v k ).mono he
    exact ( H.unit k ).mono he
-- #36 on bounded ratios.Stories.Camera supports beforeens.Canvas.Vertex margin
lemma perspective {g:ι→ℝ}(q:L)(P1:(A q).home =ᶠ[ℱ] r)(P2:(A e).home=ᶠ[ℱ] jump r g) (y: Sec G t) (k: Sec G t) (hu:t≤d) (p₁:0<t): Tendsto (MergeGeometry (W:=W) (F:=F) (r:=r) (g:=g) y k (plot r M.F x R.family.S)) ℱ (𝓝 ( Paar ( GramW G t a ) y k )) :=by
      let C (t'):=(A t').home; let X₁:= plot r M.F x R.family.S; let T':= ![e,q]; let K'(_ : Fin (1+1)):= t; let u:Tags G t 2:=![y,k]
      let P0 (i:ι):= ΩW F W A T' K' r i (X₁ i) u; let tφ:Visual ι→ℂ:= liftV P0; have hE: P0 =ᶠ[ℱ] (MergeGeometry y k X₁ (W:=W) (r:=r) (F:=F) (g:=g)):=by
         filter_upwards [P1,P2, Eventually.of_forall p] with i hi hQ hv; change C q i= r i at hi; change (A e).home i=jump r g i at hQ; change S'.classMoment S' K' _ (fun j=> walk W ((A ( T' j )).home i) t (Level.Dial t (jumpY W ( A ( T' j )) r i) (u j)))= S'.classMoment S' K' _ (fun j=> walk W ( r i ) t (( ![bend W (r i) (jump r g i) t ( Dial t (-g i) y ), k]: Tags G t 2 ) j)); refine DFunLike.congr_arg _ (funext fun j=> ?_); fin_cases j
         · change walk W ((A e).home i) t (Level.Dial t ( jumpY W ( A e ) r i ) y)= walk W (r i) t (bend W (r i) (jump r g i) t (Level.Dial t (-g i) y)); rw [jumpY,hQ,Kane.Tilted.swing,Kane.Tilted.jump,mul_div_cancel_left₀ _ hv.ne',Real.log_exp]
         change (A q).home i= r i at hi; change walk W ((A q).home i) t (Level.Dial t ( jumpY W ( A q ) r i ) k)= walk W (r i) t k; rw [jumpY,hi,div_self hv.ne',Real.log_one,Level.flat]; rfl
      let v(i):=![up hu (M.wrapW t e i y),up hu (M.wrapW t q i k)]; let pK(j):0<K' j ∧ K' j≤ d:= ⟨p₁,hu⟩; have hm(i): M.leafsT K' pK T' u i=v i:= funext fun j=>by fin_cases j <;> rfl
      let Φ':= fun i=> M.virtQ ( M.Padded B.leading x i.1 ) i (v i); have hΦ:(fun i : Visual ι=>tφ i- Φ' i)=o[ ζL ] Uψ:=by
          refine ( M.reportedP lead hr Y Y₀ h' Z' z' K' pK T' _ x ( M.passed x w ) u ).congr_left fun i=> ?_; rw [hm]; rfl
      let B0:= Paar ( GramW G t a ) y k; have he:= M.sharpen Y Y₀; have hd := M.embassy lead hr Y Y₀ h' Z' z' x w e
      have pt:Tendsto Φ' ζL (𝓝 B0):= by
         have s1:= M.washedP lead hr Y h' Z' z' e p₁ hu y; have s2:= M.washedP lead hr Y h' Z' z' q p₁ hu k; refine Eq.subst (?_ : Paar ( GramW G d a ) ( up hu y ) ( up hu k ) = B0 ) (motive:=fun x=> Tendsto Φ' ζL (𝓝 x)) (Dancer.Shell.p_emit hd.toEmblem ( translateBy ( Normalize.up hu ) ( monoY s1 he ) ) (translateBy (Normalize.up hu ) (monoY s2 he))); unfold B0 Paar GramW; rw [ Normalize.screen,Normalize.screen ]; exact congrArg _ (funext fun i=> by fin_cases i <;> rfl)

      have hv:= ((isLittleO_one_iff ℝ).mp ( hΦ.trans_isBigO ( M.tiny.mono he ) )).add pt; rw [zero_add] at hv; have pt:Tendsto tφ ζL (𝓝 B0):= hv.congr' (Eventually.of_forall fun i=> sub_add_cancel ..); suffices P:Tendsto P0 ℱ (𝓝 B0) from P.congr' hE; apply Filter.tendsto_def.mpr; intro s h; exact Kane.Tilted.curryRec (l:=ℱ) (Y:Filter (ℕ×ℕ)) (pt h)
omit w
lemma scouting {g:ι→ℝ}(q:L)(P1:(A q).home =ᶠ[ℱ] r)(P2:(A e).home=ᶠ[ℱ] jump r g)(hu:t≤d) (p₁:0<t): Witness F W t ℱ r g:=by
      obtain ⟨x,w⟩:= M.photo lead hr Y h' Z' z'; exact ⟨⟨ a,plot r M.F x R.family.S,w,fun u v=> M.perspective lead hr Y Y₀ h' Z' z' x w e q P1 P2 u v hu p₁⟩⟩
end Estate
end YM.SignedWilsonExpansion.Camera
