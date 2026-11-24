import YM.FVA2.Clef.Flow
/-!
# Uniqueness of the adjustment N from the generator prescription in §kfar

One can already obtain the same `adjust` using the *generator-only* condition
(no lower-grade part), not requiring all scale parameters in the criterion.
See `pure_adjusted` for it actually working and `mark` for uniqueness; note
conditions for the whole adjustment family (including horizon compatibility).
The differential criterion is on the actual X position frame (`gaugeB K T ν`,
see `field_X` etc.). Work with the same MS data. This uses the `casting` convention
(see `Clef/Flow` for the effect of the change of frame).
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Clef
open Function Filter Set MeasureTheory Maxwell Maxwell.Free Maxwell.Wick
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival
open MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open scoped Topology ContDiff BigOperators Classical
open Dframe Reg.Point Reg.Token Reg.Unique Reg.Choice _root_.YM.FVA2.Scale
open YM.FVA2.Scale.Facets Scale.Level Scale.Equator Scale.Measure Scale.Jury
open Scale.Meter Scale.GroupS Scale.Beta Generator.Der Generator.Drive
variable {G:Gauge}{d n i j:ℕ}
-- currently use `Touched` for whole property & unit Base etc, including scaling identity
variable {W X:Arenas G}{A Z:Frames G} {U B:ℝ→Frames G} {p q:ℝ→Cn}
lemma engraved (A:Frames G)(hp:Law X p B)(h:∀ i,Base (A i)) (hu:Touched ( rendition X A ) q U)
    (hr:Scale.remainder ( A d )) {g:Guard G d}(hg:Instant (fun i=> U i d) g 0)(Hx:Native g): A d=1:= by
    obtain ⟨ hq,h1 ⟩:= Scale.Beta.warp _ _ _ hp.toTouched hp.smooth; obtain f:= Generator.Der.walks hp d; obtain he:= adjust_by hp.toTouched h q hu hp.smooth f hg
    apply recur (Scale.Beta.beta p) hq h1 (h d) hr (Generator.Der.stays hp d).1 Hx (Generator.Der.heel hp d) (tag_witness _ _ hg ( fun t=> hu.paid t d )) he
lemma seats_r (h:X=rendition W A)(hu:∀ i,Base (A i)) : rendition X (fun i=> mirror (A i))=W:= by funext i; unfold rendition; rw [h,show rendition W A i=_ from rfl,Facets.acts, (hu i).turn',acts_h]
lemma waking (h:X=rendition W A)(K:Frames G): rendition X K=rendition W ( A * K ):= by funext i; unfold rendition; rw [ h,show rendition W A i=_ from rfl, Facets.acts ]; rfl -- Pi.mul
lemma need_fresh (A Z:Frames G)(h:X=rendition W A)(hp:Law X p B)(hA:∀ i,Base (A i))(hZ:∀ i,Base (Z i))(hu:Touched ( rendition W Z ) q U)
    {Γ:Guard G d} (ht:Scale.remainder (A d)) (hv:Scale.remainder (Z d))(he:Instant (fun i=> U i d) Γ 0)(Hx:Native Γ) : Z d=A d:= by
    let V(i):=mirror ( A i ) * Z i; have hV : rendition W Z=rendition X V:= by
        rw [ waking h ]; suffices e:A*V=Z by rw [ e ]
        exact funext fun i=> ( show Z i=A i * V i from ( by unfold V; rw [ ← mul_assoc,(hA i).turn',one_mul ] ) ).symm
    obtain e:= engraved V hp ( fun i=> (hA i|>.rewind).mul (hZ i) ) ( hV ▸ hu ) ( d:=d ); have k:= (( e ?_ ) he Hx ); swap; · unfold Scale.remainder V; rw [ (hA d|>.rewind).guard (hZ d),(hA d).diagonal_rev,ht,hv,mul_one ]; exact (Scale.Base.one).alone (mul_one _)
    nth_rw 1 [← one_mul ( Z d ), ← (hA d).turn', mul_assoc]; change A d * V d=_; rw [k,mul_one]
-- *only* from opportunity of no lower-grade part in zero-time derivative.
lemma selected (h:X=rendition W A)(hp:Law X p B)(hA:∀ i,Base (A i))(ha:∀ i,Scale.remainder (A i))(hZ:∀ i,Base (Z i))(hu:Touched ( rendition W Z ) q U)(hz:∀ i,Scale.remainder ( Z i )) (h':∀ i,∃ v: Guard G i,Instant (fun j=> U j i) v 0 ∧ Native v): Z=A:= by funext i; obtain ⟨v,hv,H⟩:= h' i; exact need_fresh _ _ h hp hA hZ hu (ha i) (hz i) hv H
lemma inks (hx:Touched W p U)(hp:Touched W p B) : U= B := by funext i; exact (( Scale.once _ _ (hx.led i) (hp.led i) i W hp.whole _ _ (hx.paid i) (hp.paid i) (hx.reads i) (hp.reads i) )).2
section physical
variable {Y: Initialize G}{V₀:Normalize.Store G}{K:Rose.Pick V₀}
variable {T: MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}
variable {S:Prescription (Press.portDeck G)} (h:G.Simple) (H: System.Contract Y K T S)
variable (ν:ℝ)
local notation "B'"=> GroupS.gaugeB K T ν
local notation "A'"=> Measure.adjust Y K
local notation "B₀"=> GroupS.gaugeN Y K T ν
local notation "Q₀"=> Measure.start Y K
local notation "Z₀"=> Measure.outlook Y K
local notation "ζ"=> GroupS.ψ K T ν
include H ν
lemma real : Base ( A' d ):= (H.joint ν d).2.2.scale
lemma strict : Scale.remainder ( A' d ):=(H.joint ν d).2.2.strict
lemma scalesE : Law Z₀ ζ B₀:= ( H.scales ν ).check
include h
lemma length_w : ∀ i j (u:i≤j), Walk u (A' i) (A' j):= by obtain ⟨ hp,hr,hy⟩:= H.toMission.toSchemeV.born; exact fun i j u=> Scale.Measure.grades Y K ν T S h hp hr hy u
lemma growsV : Touched Q₀ ζ B':= by obtain ⟨ hp,hr,hy⟩:= H.toMission.toSchemeV.born; exact Scale.GroupS.scaleX _ _ _ _ _ h hp hr hy
lemma originate : B₀=breeze A' ζ B':= ( inks ( scalesE H ν |>.toTouched ) ( growth ( growsV h H ν ) ( fun _=> real H ν ) ( length_w h H ν ) ) ) -- Z₀ defeq
lemma frequency : let A:=(fun i=>mirror ( A' i )); let W:=Generator.Drive.engraving B₀; Instant (fun i=> B' i d) ( casting ( A d ) (Scale.Beta.beta ζ) ( W d ) ) 0:= by
    intro F W; rw [ show B'=breeze F ζ B₀ from ?_ ]; swap; · exact inks ( growsV h H ν ) (( seats_r (A:=A') ( X:= Z₀ ) ( W:=Q₀ ) rfl (fun _=>real H ν) ) ▸ growth ( scalesE H ν|>.toTouched ) ( A:=F ) ( fun i=>(real H ν).rewind ) ( fun i j u=> ( length_w h H ν i j u ).rewind (real H ν) (real H ν) ) )
    apply casted_c ( scalesE H ν|>.toTouched ) ( fun i=>( real H ν ).rewind ) (fun i j u=> ( length_w h H ν i j u ).rewind ( real H ν ) (real H ν)) ( scalesE H ν|>.smooth ) ( Generator.Der.walks ( scalesE H ν ) d )
lemma field_X : Instant (fun i=> B' i d) (Generator.Drive.engraving B' d) 0:= by obtain hp:= frequency h H ν (d:=d); rw [ Generator.Drive.engraving,derivative_eq hp ]; exact hp
lemma pure_adjusted : Native (casting ( A' d ) (Scale.Beta.beta ζ) (Generator.Drive.engraving B' d)):= by
    obtain he:= casted_c ( growsV h H ν ) ( (fun _=> real H ν) ) ( length_w h H ν ) ( scalesE H ν|>.smooth ) ( field_X h H ν (d:=d) ); rw [ ← originate h H ν ] at he; rw [ he.once ( Generator.Der.walks ( scalesE H ν ) d ) ]; exact Generator.Der.stays ( scalesE H ν ) d|>.1
-- Unique $N`: EXACT generator prescription, stronger than only candidate with smooth $B' etc
lemma mark (α:Frames G)(he:∀ i,Base (α i) ∧ Scale.remainder (α i))(hm:∀ i j (v:i≤j),Walk v (α i) (α j)) (hv:∀ i, Native (casting (α i) (Scale.Beta.beta ζ) ( Generator.Drive.engraving B' i )) ): α = Measure.adjust Y K:= selected ( X:=Z₀ ) rfl ( scalesE H ν ) ( fun _=>real H ν ) ( fun _=> strict H ν ) ( fun i=>(he i).1 ) ( growth (growsV h H ν) ( fun i=> (he i).1 ) hm ) ( fun i=> (he i).2 ) ( fun i=> ⟨ _,casted_c ( growsV h H ν ) (fun i=>(he i).1) hm ( scalesE H ν |>.smooth ) ( field_X h H ν ), hv i⟩ )
end physical
end YM.FVA2.Clef
