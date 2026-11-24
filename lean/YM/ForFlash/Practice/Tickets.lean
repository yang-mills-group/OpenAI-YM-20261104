import YM.ForFlash.Practice.Studio
/-! # Applying on an actual path. Transfer to Cash with the SAME truncation. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
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

namespace PortraitForFlash
open Gram Lights Path Wipe Canvass
open FVA2.Register FVA2.GradedFar259 FVA2.GradedFar259.Pose
-- frames
variable {R:PhysicalNext.Repeat.Legato.Run G}{f:Extraction.Order} {S':Table R.family.book}(F:Final R.family f S')(W:ℝ→tower S') (H:(Bel R.family.book).Hierarchy) (lead:Leading F W)
variable {r:ι→ℝ}(hr:Tendsto r ℱ trail) (p:∀ i,0<r i) (Y:Ultrafilter (ℕ×ℕ))(Y₀:(Y:Filter _)≤ (track f).fuse) (Z:WilsonPrescription G) {T:∀ h,Rays G h Z.scheme.hol}
variable {Ω:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))} {J':MS.Land.Prescription (Press.portDeck G)}(Q:Speed.Quoted Z.scheme Z.criterion Ω J')
variable (X₀:ChartRatio G) (Z':(track f).PointLimits R.family S')(z':(track f).Ordered R.family S')
variable (clockP:Coupling G (Date F Z.criterion W))(S₁:Shoe F W Z.store)
-- API from Camera.Pupils
abbrev Delivery (B:Plans a)(Y₁:ℝ)(ξ:ℝ) (b:ℕ)(d:ℕ): Prop:= ∃ v:Page (T:=T) H Y Z.store Z.criterion Q B X₀ W r r p d b ℱ (f:=f),
    sizeP r v.paid.F R.family.S ≤ᶠ[ℱ] payD (cck G∘r) (-ξ) ∧ v.paid.ReserveForFlash ∧ ∀ {n:ℕ},B.hired n → ∀ (d':Fin (n+1)→ℕ), (∀ i,0<d' i∧ d' i≤ d) → ∀ (Z₁:Fin (n+1)→Bool)(x:ι→Shake (n:=n+1)), (∃ δ>0,InBWidth δ Y₁ (cck G∘r) ( Camera.plot r v.paid.F x R.family.S ) ℱ )→ v.paid.BoughtForFlash d' Z₁ x
variable {s:ι→ℝ} {W₀ C δ a₁ b₁:ℝ} {m:ℕ}{K₁:Set (Points n)}{K₂:Set (Points m)}(B₀: Flash.Room W₀ C δ K₁ K₂)
variable (a:Axis) -- nonempty `plans`. earlier implicit global `a`: adjust.
variable (hT:Flash.Aim ℱ G W₀ a₁ b₁ r s) (ha:0<a₁) (hb:0<b₁)
variable (buy:∀ B:Plans a,∀ (Y₁ ξ:ℝ),0<Y₁→ 1/2≤ ξ → ∀ b:ℕ,0<b→Delivery W H p Y Z Q X₀ B Y₁ ξ b d (f:=f) (T:=T) (ℱ:=ℱ))
-- `Aim` name maybe ambiguity. Portrait charges ***every occurrence*** of v together. use true T Date and zero frame. `Store` & Rose.
open FVA2.GradedFar259.Flash
local notation "Late"=> 𝓝[>] (0:ℝ)
local notation "PS"=> (Measure.start Z.scheme Z.criterion d)
include hT Z' z' Y₀ buy B₀ ha hb lead clockP S₁ p
set_option maxHeartbeats 900000 in
lemma delivered (x:ι→Points n)(y:ι→Points m)(hx:∀ᶠ i in ℱ,x i∈ K₁)(hy:∀ᶠ i in ℱ,y i∈ K₂)(w:ℕ)(ζV:6≤d)(sim:G.Simple) : ∃ p' t₁ A x' y',Mesh F W Z ℱ w p' r s t₁ A x x' y y' (d:=d):=by
   let v:= hT.reach; obtain ⟨k,d',kP,dP,X⟩:= Flash.Practice.layout B₀ sim hT hx hy ha hb
   let Φ:=shops Z d (n+m); obtain ⟨B,hP⟩:= Canvass.inhabited ( Wipe.allPut Z.criterion Φ d ) a
   have he:0<k+1:= by linarith
   let Y' :ℝ:= ((w:ℝ)+1)/2
   obtain ⟨V,hv,hr,Q'⟩:= buy B (k+1) Y' he (by unfold Y'; linarith [Nat.cast_nonneg (α:=ℝ) w]) (w+1) (Nat.zero_lt_succ w); let W':= V.paid
   obtain ⟨x',y',ξ,p',q,z,hG⟩:= Flash.Practice.form B₀ sim hT w k d' kP dP X ( show sizeP r W'.F R.family.S ≤ᶠ[ℱ] payD (cck G∘r) (-((w:ℝ)+1)/2) from (by rw [neg_div]; exact hv) ) -- minus via `neg_div`; defeq?
   let τ:= Date F Z.criterion W
   let A (i:ι): Change G d:= 0
   have stands(i:ι){n':ℕ}(t':Tags G d n'): stand ( A i ) ∘ t' = t':=by unfold A; rw [stand0]; rfl
   refine ⟨W'.q, (τ∘r), A,x',y',⟨?_, q,z,?_⟩⟩
   · refine ⟨?_,?_,?_, W'.needed,?_⟩
     · exact tendsto_nhdsWithin_iff.mpr ⟨(clockP.conforms sim).comp v,v.eventually clockP.positive⟩
     · exact ( Fire.coupling sim _ clockP ).isBigO.comp_tendsto v
     · simp_rw [A,map_zero]; exact tendsto_const_nhds
     intro R x a'
     have hm:= boothPrices F W H lead v p Y Y₀ Z.store Z.criterion Q B X₀ Z' z' clockP S₁ V Φ hP (Nat.zero_lt_succ w) ζV R ( visiting Z (n+m) x ) a'
     unfold unpack; simp_rw [stands]; exact ( Path.banquet.mp hm ).isBigO
   intro v'
   have hp:= paidAll F W H lead v p Y Y₀ Z.store Z.criterion Q B X₀ Z' z' clockP S₁ V Φ hP (Nat.zero_lt_succ w) ζV hr (k+1) he (fun {_} k ξ hv=> Q' k (fun _=>d) (fun _=> ⟨by omega, le_rfl⟩) (fun _=>false) ξ hv) (n+m) (leadingP ..) ξ v' ⟨d'/2,half_pos dP,hG⟩ -- implicit n lambda curly!
   simp_rw [stands]; exact hp.isBigO.congr' ( p'.mono fun i hi=>by dsimp only; unfold W' at hi ⊢; rw [hi]; rfl ) (.refl ..)

omit hT Z' z' Y₀ buy B₀ ha hb lead clockP S₁ p
-- consume pupil.D-fees. Covers all positive-length trajectories, transport rest via query.
abbrev Academy (α:Axis):Prop:= ∀B:Plans α,∀ (i:Type)(L₁:Filter i),L₁.NeBot→∀ r:i→ℝ, Tendsto r L₁ trail→∀ (p:∀ j,0<r j)(Y₁ ξ:ℝ)(d b:ℕ),0<Y₁→1/2≤ξ→6≤d→0<b→Delivery W H p Y Z Q X₀ B Y₁ ξ b d (f:=f) (T:=T) (ℱ:=L₁)
variable {A:ι→Points n}
lemma issued_at {ι:Type}{L:Filter ι}{r r' s:ι→ℝ}(e:r'=ᶠ[L] r){k w d:ℕ}{x x':ι→ Points n}{y y':ι→Points m}{A:ι→Change G d}{T:ι→ℝ}(W':Mesh F W Z L w k r' s T A x x' y y') : Mesh F W Z L w k r s T A x x' y y':=by
   have he:g0 G ∘ r' =ᶠ[L] g0 G ∘ r:= e.fun_comp _; have hv:= e.fun_comp (fun x=> g0 G x ^ (w+1)); refine ⟨ ⟨ W'.stamps,W'.budget.congr' (.refl ..) he,W'.chart,W'.repays,?_⟩, W'.payA.congr' (.refl ..) hv,W'.payB.congr' (.refl ..) hv,fun v=>?_⟩
   · intro R h v; apply (W'.compact R h v).congr' _ ( hv.comp_tendsto (tendsto_fst (f:=L)) )
     filter_upwards [ (tendsto_fst (f:=L)).eventually e ] with i hi; unfold unpack; rw [hi]
   refine ( W'.charges v ).congr' (e.mono ( fun i hi=>?_)) hv; dsimp only; rw [hi]
include Z' z' Y₀ lead clockP S₁
lemma coversSchedule (θ:Axis)(A':Academy (T:=T) (f:=f) W H Y Z Q X₀ θ) (sim:G.Simple): Pays F W Z:=by
   intro n m A B hA V hB h
   obtain ⟨C,δ,Hc⟩:= arrange hA V hB h
   filter_upwards [ Hc ] with i H₀
   intro d hd ι ℱ r T a b ha hb I x y hx hy w
   by_cases h : ℱ.NeBot
   · let r' (i:ι):= if 0<r i then r i else 1; have he:r'=ᶠ[ℱ] r:=( I.reach.eventually self_mem_nhdsWithin ).mono fun i hi=> if_pos (show 0<r i from hi)
     have hp(z:ι): 0<r' z:=by unfold r'; split_ifs with ht; exact ht; exact zero_lt_one
     have hP:= I.reach.congr' he.symm; have ht:Aim ℱ G i a b r' T:= ⟨hP,I.high,( he.and I.bud ).mono fun z hi=> by rw [hi.1]; exact hi.2⟩
     obtain ⟨p,t,A,x',y',u⟩:= delivered F W H lead hp Y Y₀ Z Q X₀ Z' z' clockP S₁ H₀ θ ht ha hb (fun B y t z x b v=> A' B ι ℱ h r' hP hp y t d b z x hd v) x y hx hy w hd sim -- hT.include args order
     exact ⟨p,t,A,x',y',issued_at F W Z he u⟩
   have hz: ℱ=⊥:= by simpa only [neBot_iff, not_not, ne_eq] using h
   subst ℱ; refine ⟨ w+1, Date F Z.criterion W∘r,(fun _=> (0:Change G d)), x,y, ⟨⟨ ?_, ?_, ?_, le_refl _, ?_ ⟩, ?_,?_,?_⟩ ⟩
   · simp
   · apply IsBigO.of_bound (1:ℝ); simp
   · simp
   · intro R u v; apply IsBigO.of_bound (1:ℝ); simp [Pose.booth]
   · apply IsBigO.of_bound (1:ℝ); simp
   · apply IsBigO.of_bound (1:ℝ); simp
   intro v; apply IsBigO.of_bound (1:ℝ); simp
end PortraitForFlash
end YM.SignedWilsonExpansion.Camera
end
