import YM.SignedWilsonExpansion.Camera.Shawl
import YM.SignedWilsonExpansion.Fire.Timer
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
abbrev Visual (ι:Type):= ι× (ℕ×ℕ)
abbrev liftV (q:ι→J): Visual ι→J := q ∘ Prod.fst
abbrev pvV (q:L→ι→J)(u:Fin n→L)(j:Fin n): Visual ι→J := liftV (q (u j))
abbrev loN (ι:Type)(q:Visual ι):= q.2.1
abbrev lop (ι:Type)(q:Visual ι):= q.2.2
section
variable {C:Family G} {f:Extraction.Order} {S':Table C.book}(F:Final C f S')(W:ℝ→tower S') (H:(Bel C.book).Hierarchy) (lead:Leading F W)
variable (A: L→Shawl C S' ι W) {r:ι→ℝ}(hr:Tendsto r ℱ trail)
variable (Y:Ultrafilter (ℕ×ℕ))(Y₀:(Y:Filter _)≤ (track f).fuse)(Q:∀ a:L,Shine (f:=f) W H (A a) Y r ℱ d)
-- linear caps heterogeneous.Storm
variable (P: Fin (n+1)→ L)(S:Fin (n+1)→ℕ)
abbrev πP : Fin (n+1)→ Visual ι→ℝ := pvV (fun a=> (A a).home) P
abbrev πS : Fin (n+1)→Visual ι→BeamT C:= pvV (fun a=>(A a).station) P
variable (Z: Pad (n+1))(g:ι→ℕ)(x:ι→ Shake (n:=n+1))(u:pad0 Z r g x ℱ C.S)
-- local notation "Ξ" => ℱ.curry (Y:Filter (_×_))
abbrev cameraV (r:ι→ℝ)(i:Visual ι) := μRead C S (liftV x) (πP W A P) (πS W A P) (loN ι) (lop ι) (liftV g) (liftV r) i
abbrev ΩW (r:ι→ℝ)(i:ι)(x: Points (n+1)) := sPlot F none (r i) S (fun j=> (walk W ((A (P j)).home i) (S j)).toLinearMap.comp (Level.Dial (S j) (jumpY W (A ( P j )) r i))) x
abbrev wear (r:ι→ℝ)(i:ι)(t:L)(d:ℕ):= Shawn W (A t) r i d
-- no assumption beyond Leading.V
end
section phases
variable {f:Extraction.Order} (Y:Ultrafilter (ℕ×ℕ)) (P: Fin (n+1)→ L) (S:Fin (n+1)→ℕ) (Z:Pad (n+1))(g:ι→ℕ)(x:ι→ Shake (n:=n+1)) {r:ι→ℝ}(hr:Tendsto r ℱ trail)
variable {R:Run G} {S': Table R.family.book}(F:Final R.family f S')(W:ℝ→tower S') (H:(Bel R.family.book).Hierarchy) (lead:Leading F W)
variable (A: L→Shawl R.family S' ι W)(Y₀:(Y:Filter _)≤ (track f).fuse)(Q:∀ a:L,Shine (f:=f) W H (A a) Y r ℱ d) (z:pad0 Z r g x ℱ R.family.S)
local notation "C₀" => R.family
variable (s:G.Simple)(u':(track f).PointLimits R.family S')
include Y₀ Q z hr s u'
lemma govern (T:ι→ (j:Fin (n+1))→ Sec G (S j)) (hv:∀j,S j ≤ d): ∀ᶠ i:ι in ℱ,
     Tendsto (fun p:ℕ× ℕ=> cameraV W A P S g x r (i,p) (fun j=> wear W A r i (P j) (S j) (T i j))) (Y:Filter _) (𝓝 ( ΩW F W A P S r i (plot r g x R.family.S i) (T i) )):=by
      let st j:= A (P j); filter_upwards [z, hr.eventually self_mem_nhdsWithin, eventually_all.mpr (fun j=> ( Q ( P j ) ).contact (hv j)),eventually_all.mpr (fun j=> lamp W H (st j) Y hr ( Q ( P j ) ) (hv j))] with i hz hp hY hQ; let X(j:Fin (n+1)):= wear W A r i ( P j ) ( S j ) ( T i j ); let B:= plot r g x R.family.S i; let a0(j):= pre C₀ (X j); let V(j):= gear R.family.labels (S j) (r i/(st j).home i) ( a0 j ); choose y cap openY using (fun j=> hY j (V j)); let m:= (Y:Filter (ℕ×ℕ)); let v':=office C₀ r g x i hp
      have hh : r i • B∈conf (n+1):= Work.A05.smul_conf hp ( Z.roi.2 hz )
      rw [show ΩW F W A P S r i B (T i)= S'.value S (Order.grid C₀ ( g i ) ( x i )) y from ?_ ] -- let B rw rewrite? Might goal not match.
      · let Λ(p:ℕ×ℕ):=R.family.ensemble S (fun j=> Cells.location R.family.S (g i) p.1 p.2 (x i j)); let A'(p:ℕ×ℕ) j:= ((st j).station i).microphone p ( S j ) ( V j ); change Tendsto (fun p=> Λ p ( A' p )) _ _; exact Next.UVStress.tendsto_multi _ Λ (fun v=> S'.value S (Order.grid C₀ ( g i ) ( x i )) v) (fun v=> (tie_bill R s F.room.kernel u' ( x i ) (v' ▸ hh) S v).mono_left Y₀) y A' cap
      unfold ΩW sPlot; rw [← v']; let w:= fun j=> (st j).legs i (S j) ( V j ); change S'.classMoment S' S _ (fun j=> walk W ((st j).home i) (S j) (_))= _; trans S'.classMoment S' S (r i • B) w; · exact congrArg (S'.classMoment S' S ( r i • B )) (funext fun j=> ( hQ j ( T i j ) ).symm)
      rw [show w=(fun j=> S'.project _ ( y j )) from funext fun j=> (openY j).symm]; exact S'.at_project S' F.room.kernel.laws.toSymmetric (fun _=> le_refl _ ) hh (fun i=> ⟨ S i,y i ⟩)
lemma earnedPrice {ε:ι→ℝ}(he:∀ᶠ i in ℱ,0<ε i) (T:ι→ (j:Fin (n+1))→ Sec G (S j)) (hv:∀j,S j ≤ d):
 (fun i:Visual ι=> ΩW F W A P S r i.1 ( plot r g x R.family.S i.1 ) ( T i.1 )-cameraV W A P S g x r i (fun j=> wear W A r i.1 (P j) (S j) (T i.1 j))) =o[ℱ.curry (Y:Filter (ℕ×ℕ))] liftV ε:=by
     refine IsLittleO.of_bound fun b hb=>?_ ; rw [eventually_curry_iff]; -- he probably b eventually property |; view
     filter_upwards [he,govern (r:=r) Y P S Z g x hr F W H A Y₀ Q z s u' T hv] with i h p; refine (Metric.tendsto_nhds.mp p ( b * ε i ) ( mul_pos hb h ) ).mono fun j hi=>?_ ; rw [dist_eq_norm,norm_sub_rev] at hi; exact hi.le.trans_eq (by rw [liftV, comp_apply, Real.norm_eq_abs,abs_of_pos h])
omit Y₀ z
abbrev alongT (l:Filter ι)(f:Extraction.Order):Filter (Visual ι):=l.curry (track f).fuse
variable (b0:(track f).Ordered R.family S')
include lead b0
lemma partner (e:L)(T:ι→(j:Fin (n+1))→Sec G (S j))(v:∀j,Sec G ( S j ))(sV:∀ j, By ℂ ℱ (fun i=> T i j) (v j))(hV:∀ j,S j≤d)(y:Points (n+1))(t:y∈conf _)(vT:Tendsto (plot r g x R.family.S) ℱ (𝓝 y)): Tendsto (fun i:Visual ι=> cameraV W A (fun _=> e) S g x r i ( T i.1 )) (alongT ℱ f) (𝓝 (WickGoal (d:=S) (fun i=>pre C₀ (v i)) y)):= by
     let Tv:= fun (i:ι) j=> pre C₀ ( T i j ); exact projectionP R s F b0 u' H hr lead S ( Q e |>.pivots ) (Q e|>.lives) (Q e|>.checked) g x ( (hr.eventually self_mem_nhdsWithin).mono fun i hi=>office C₀ r g x i hi) t vT (w:=Tv) ( fun i=> Stock' (v:=pre C₀ ( v i )) ( translate (fields R.family.labels (S i)|>.symm.toLinearMap) ( sV i ) ) ) -- hp with Need reader
where Stock' {i:ℕ} {q:ι→ (Bel R.family.book).Field i} {v:(Bel R.family.book).Field i} (p:By ℂ ℱ q v): Tendsto q ℱ (𝓝 v):=by
        let B:= Module.finBasis ℂ ((Bel R.family.book).Field i); rw [← B.equivFun.symm_apply_apply v]; apply Tendsto.congr _ ( B.equivFun.symm.toLinearMap.continuous_of_finiteDimensional.continuousAt (x:=B.equivFun v)|>.tendsto.comp (Stock B p) ) -- fix
        intro i; exact B.equivFun.symm_apply_apply _
-- need brightness
end phases
end YM.SignedWilsonExpansion.Camera
