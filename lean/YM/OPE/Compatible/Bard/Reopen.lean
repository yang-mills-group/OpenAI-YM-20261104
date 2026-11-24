import YM.OPE.Compatible.Bard.Pole
/-!
# Matching capture at pivot; linear delivery on the long pattern
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal.Arcade
open Function Filter Lattice RG Wilson MeasureTheory MergeProof Finset
open Push Marker Source Accent Ribbon Menu Local Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open PhysicalNext.Repeat.Legato Bandage
open Extra.Multi GridApprox.Nil
open Extra.Trajectories MergeProof.Float Ribbons Ribbons.ManyCopies Ribbons.ManyCopies.Stem
open Mirror Deb Allot Lights Wave Relay
open scoped Topology BigOperators Classical
variable {X V I G' T W : Type} [PartialOrder X][OrderBot X][Fintype X](D:Origin X) {U F K:Finset X}{m j:X→ℕ}
    [Fintype V][DecidableEq V][Fintype W][DecidableEq W][Fintype T][DecidableEq T][Fintype G']
    {G:Gauge}{C:Family G}{p N b d k:ℕ}{l:ℕ→ℕ}{A:Allot C} {z e r:ℝ}
variable {P:Ensemble V}{P':Ensemble T}{E:Track C.path V p}{o:X→ Track C.path V p}
    {E':Track C.path T p}{o':X→Track C.path T p} {f:V ↪ T}{a:T→G'}
    {Q: Extra.Histories.Music (C.labels.level d) C.path N p}
variable (L:Arcade C P' f a D U m j N p P E o b l E' o' k)
    (S:Wave m U K (k+1))(S':Wave m K F k) (x:brim D F)(hX:x.val∈U)
set_option quotPrecheck false
local notation "I₀"=> (C.labels.level d).Index
local notation "hQ"=>C.ref d
local notation "b'"=> ballot C k d
local notation "sX"=>inlet (W:=I₀) D F x.val m k
local notation "J"=> ↥(brim D F)⊕(C.labels.level d).Index
local notation "T₀"=> shades' D F x.val a ((C.labels.level d).Index)
local notation "E₀"=> o∘ columns D ((C.labels.level d).Index) F x.val
local notation "A₀"=>o'∘ columns D ((C.labels.level d).Index) F x.val
local notation "D'"=> x
-- rewrite Tick full stamps
variable {t:brim D F⊕(C.labels.level d).Index→Stem T G (C.S.side k p)} {Y: Lights A P N p (inlet (W:=(C.labels.level d).Index) D F x.val m k) k b E (o∘ columns D ((C.labels.level d).Index) F x.val)}
    {q: T×(brim D F⊕ (C.labels.level d).Index)→ Config G (C.side N p)→ℂ}
local notation "R"=> C.path.rep N p
local notation "ϑ"=> C.S.a (k+1)^d*(β C (k+1)*(4*(1/z)))
include S' L
omit [Fintype G'] in
set_option maxHeartbeats 200000 in
lemma received_here (hA: Solvent (A:=A) Q)(hG:G.Simple)(H:C.Makes)(hk:k ≤ N) (hp:C.ref d ≤ k) (hv:Session P' f Y (gust C.path N p N (birth (ManyCopies.Names T _) (C.path.rep N p N) q) k hk) t (shades' D F x.val a _) E' (o'∘ columns D (C.labels.level d).Index F x.val)) (hr: Integrable (birth (ManyCopies.Names T _) (C.path.rep N p N) q) (prior G _))
    {y:Coefficient (C.labels.level d) (C.side k p)} (hf:y.Format 0 C.params (C.path.rep N p k))(he:(C.labels.level d).coeffSize y.x≤ ϑ)(ht:y.remBound 0 (R k) (kappa C.path k) ϑ) (hz:0<z)
    (hV:e*badge_fee C z k ≤ Y.asks (.inl x))(hL:Stamp (N:=N) P (C.localSection d) (E k) y (Y.tips (.inl x)))
    (hP:∀ i:(C.labels.level d).Index, e^2* ballot C k d ≤ Y.asks (.inr i) ∧ Stamp (N:=N) P (C.localSection d) (E k) ((Q.tone k).plays (sonnet C Q k i)) (Y.tips (.inr i)))
    (hx:0<r) (hx':r ≤ e*badge_fee C z k)(hu:r*(2*owed C z d k)≤ e^2*ballot C k d)(hC:r*‖alto C.path k d‖*owed C z d k ≤ PhysicalNext.Repeat.Legato.Bandage.fly C.path.levels d k) :
    ∃ T':∀ i:ℕ, Solo (C.labels.level d) C.path p i, Fortune C A.W (waybill C.path.levels) N p k d y ϑ (2*ϑ) (owed C z d k) Q A.D T' ∧
    let c:=(T' (C.ref d)).a
    let Z:=fun i=>(T' i).bar Q (-c)
    let q':=(Q.tone k).index c
    let X':=Deb.portion (atopBy T (foldTo (W:=I₀) x)) (spices P' (dyes (-q'))) q
    let w:=update (fun v:brim D F=> Y.asks (.inl v)) x r
    Integrable (birth (ManyCopies.Names T _) (C.path.rep N p N) X') (prior G _)∧ Guided (C.localSection d) C.params C.path N p (C.ref d) k Z A.D (lantern C.path r d k) ∧ ∃ t':brim D F→ Stem T G (C.S.side k p), Owned (curtain (brim D F) a) (C.path.rep N p k) (E' k) P' t' w ((C.path.levels.budget k).supportExponent-3) (gust C.path N p N (birth (ManyCopies.Names T _) (C.path.rep N p N) X') k hk) ∧ Stamp (N:=N) P' (C.localSection d) (E' k) (Z k) (t' x) ∧ (∀ i,(t' i).home=o' i.val k) ∧ ∀ i,i≠x→ t' i=t (.inl i):=by
    let a₀:= o' x.val k; have hz' : 0 < 2*ϑ := mul_pos zero_lt_two (mul_pos (pow_pos (C.S.a_pos _) _) (mul_pos (β_pos ..) (by positivity))); obtain ⟨Z,hZ⟩:= fortuned A.buy.system H Q hA.pull hA.rolls y hp hk hf ht (Q:=2*ϑ) hz' (by linarith only [he]) (E:=owed C z d k) le_rfl -- extra q
    let c:=(Z (C.ref d)).a; let g:=fun i=>(Z i).bar Q (-c); let q':=(Q.tone k).index c; let s:=owed C z d k; have hp':(C.labels.level d).coeffSize q' ≤ 2*s:= bias_price Q hA.pull y hZ ht
    have hα: Screenlet P P' f:=L.fly; have he:= (L.turns k le_rfl hk)
    have hh:(t (.inl x)).home=a₀:=hv.stood _
    have hxM:= Stamp_back hα (hv.ship.known _ (.inl x)) (show Stamp (N:=N) P _ ((E' k) ∘ f) y (cropStem f (t (.inl x))) from (by rw [hv.seen _,he]; exact hL))
    have hxP(i:I₀): Stamp (N:=N) P' (C.localSection d) (E' k) ((Q.tone k).plays (sonnet C Q k i)) (t (.inr i)):= by
        refine Stamp_back hα (hv.ship.known _ (.inr i)) ?_; rw [he, hv.seen]; exact (hP i).2
    obtain ⟨hT,hQ'⟩:= filled_signed hZ hA.pull A.buy.system hx (fun i hi hi'=> hC.trans (fly_le hG d i k hi'))
    let X':= Deb.portion (atopBy T (foldTo (W:=I₀) x)) (spices P' (dyes (-q'))) q
    let B:=sendAll (atopBy T (foldTo (W:=I₀) x)) (spices P' (dyes (-q')))
    have hG' := deliver_birth (atopBy T (foldTo (W:=I₀) x)) (spices P' (dyes (-q'))) (C.path.rep N p N) q
    have hR: Integrable (birth (ManyCopies.Names T _) (C.path.rep N p N) X') (prior G _):= hG' ▸ ((B.toContinuousLinearMap.restrictScalars ℝ).integrable_comp hr)
    obtain ⟨T',hxW,hO⟩:= realize P' (C.localSection d) a₀ H.wilson hk (by rw [← hh]; exact hxM.homes.sym) (hT.ticks _ hp le_rfl|>.1) (hT.ticks _ hp le_rfl|>.2) (H.sections _)
    let t':= update (fun i:brim D F=> t (.inl i)) x T'; let w:=update (fun v:brim D F=> Y.asks (.inl v)) x r
    have hv': t' x=T':= update_self ..; have hg(i): (t' i).home=o' i.val k:=by
       by_cases h:i=x; · rw [h,hv']; exact hO
       rw [show t' i=t (.inl i) from update_of_ne h T' (fun i:brim D F=> t (.inl i))]; exact hv.stood _
    obtain ⟨hL',hK⟩:= score_mark Q x Z hA hZ hf ht hxM hxP (fun i=> (hv.stood _).trans hh.symm) hxW (hO.trans hh.symm)
    have hθ: Owned (curtain (brim D F) a) (C.path.rep N p k) (E' k) P' t' w ((C.path.levels.budget k).supportExponent-3) (B ∘ gust C.path N p N (birth (ManyCopies.Names T _) (C.path.rep N p N) q) k hk):=by
        refine ManyCopies.super x (-q') P' hv.ship (fun i he hi=> opens D _ _ i x he hi S'.after.base) t' (fun i=>?_) (fun i=>?_) ?_ ?_ hL' hK
        · by_cases he:i=x; · rw [he,hv']; exact hxW.homes
          rw [show t' i=t (.inl i) from update_of_ne he T' (fun i:brim D F=> t (.inl i))]; exact hv.ship.known _ _
        · by_cases he:i=x; · rw [he, show w x=r from update_self ..]; exact hx
          rw [show w i=Y.asks (Sum.inl i) from update_of_ne he r (fun i:brim D F=>Y.asks (Sum.inl i))]; exact Y.asks_pos _
        · rintro (i|i); exact (hg i).trans (hv.stood (.inl i)|>.symm); exact (hg x).trans (hv.stood (.inr i)|>.symm)
        rintro (i|i)
        · change w i*‖(1:ℂ)‖ ≤ Y.asks _; rw [norm_one,mul_one]; by_cases h:i=x; · rw [h,show w x=r from update_self ..]; exact hx'.trans hV
          rw [show w i= Y.asks (.inl i) from update_of_ne h r (fun i:brim D F=>Y.asks (Sum.inl i))]
        have hι: ‖q' i‖ ≤ 2*s:= le_trans (single_le_sum (f:=fun i=>‖q' i‖) (fun _ _=>norm_nonneg _) (mem_univ _)) hp'; change w x*‖- (q' i)‖ ≤ _; rw [norm_neg,show w x=r from update_self ..]; exact (mul_le_mul_of_nonneg_left hι hx.le).trans (hu.trans (hP i).1)
    have hy: B ∘ gust C.path N p N (birth (ManyCopies.Names T _) (C.path.rep N p N) q) k hk = gust C.path N p N (birth (ManyCopies.Names T _) (C.path.rep N p N) X') k hk:= hG' ▸ deliver_gust _ _ hr hk
    rw [hy] at hθ; exact ⟨Z,hZ,hR,hQ',t',hθ,hv' ▸ hxW,hg,fun i hi=> update_of_ne hi T' (fun i:brim D F=> t (.inl i))⟩
end YM.OPE.Arboreal.Arcade
