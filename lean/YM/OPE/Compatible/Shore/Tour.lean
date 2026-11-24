import YM.OPE.Compatible.Shore.Spread
/-!
# Follow one hop from a principal to the full company
Only actually walk extra copies on supported steps. Thus no extrapolation
of the displaced secondary tiling to earlier than its alignment.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.ManyCopies
open Function Filter Lattice RG Wilson MeasureTheory
open Push Marker Accent Ribbon Menu Local Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil
open Extra.Trajectories MergeProof.Float Stem
open scoped Topology Classical
variable {V I J W : Type}[Fintype V][DecidableEq V]{G:Gauge}{n n':Side}{H:History G}{N p m:ℕ}
variable {P:Ensemble V}{P':Ensemble W}(M:V ↪ W){w u:ℝ}
lemma Owned.pay_part [Fintype I][DecidableEq I]{X:Config G (H.S.side m p)→ Poly (Names V I)}{b v e}{χ:Guard (Names V I)}{Y}(hs:H.Selected)(ht:m≤N) (h:Owned χ (H.rep N p m) b P Y v e X)(i:V×I): Integrable ((Y i.2).sub (H.rep N p m) i.1) (prior G _):=by
   obtain ⟨Z,hz,_,hv⟩:= h.issues
   let m':=(Names V I).fire i
   have ht:(fun U=>(Z U).part m')=(Y i.2).sub (H.rep N p m) i.1:=funext fun U=> Served.relay (J:=Names V I) (g:=color Y) hv.ship.sold (fun i=>(hv.earned _).spends i.1) (hs.represents N p m ht|>.good.labels) U |>.1 i
   rw [← ht]; exact ((Poly.get m').restrictScalars ℝ).integrable_comp hz
namespace Stem
variable {E' : W→Site (H.S.side N p)}{X:Stem W G (H.S.side N p)}
    {b:W→ Config G (H.S.side N p)→ℂ}
set_option quotPrecheck false
omit [Fintype V][DecidableEq V] in
lemma Budges.covers [Fintype W][DecidableEq W] (hM:Screenlet P P' M)(hH:H.Selected)(hX:Marked (H.rep N p N) E' P' X)
   (h:Budges P H N p u w (E' ∘M) (cropStem M X) (b∘M))(hb:∀ i:W,i≠P'.v → b i=stepUp (P'.move i) (E' i) (b P'.v)): Budges P' H N p u w E' X b:=by
    have hP := h.patent; have hv:∀ U,((H.rep N p N).eval U:ℂ)*b P'.v U=X.sub (H.rep N p N) P'.v U:=by
        intro U; rw [← hM.start]; exact h.writes U _
    refine ⟨h.pos,hX,?_,fun U i=>?_⟩
    · simp only [cropStem,comp_apply,hM.start] at hP; exact hP
    by_cases hi:i=P'.v; · subst i; exact hv U
    rw [marked_sub hH le_rfl hX i hi,hb i hi]; unfold stepUp; rw [← hv, Motion.scalar_mul, show ((↑((H.rep N p N).eval (pull _ _ U)):ℂ))= _ from vac_pull H N p N hH le_rfl _ _ U,show (scalar (P'.move i) (liftVac H N p N U))=(_ :ℂ) from Motion.scalar_real ..]
variable {E:W→ Site (H.S.side m p)}
   {D:GaugeDoor (H.rep N p (m+1)) (H.rep N p m)}
   {Z:Stem W G (H.S.side (m+1) p)}{T:Stem W G (H.S.side m p)}{c:ℂ}
omit [Fintype V][DecidableEq V] in
lemma Journey.extended [Fintype W][DecidableEq W] (hM:Screenlet P P' M)(h:H.Selected)(he:m<N)
    (ht:Marked (H.rep N p (m+1)) ((H.levels.clock.op m p).ratio.embed ∘ E) P' Z)
    (hx:Marked (H.rep N p m) E P' T)(hZ:(H.levels.clock.op m p).ratio.parent ∘ Z.home=T.home)
    (hv:Integrable (Z.sub (H.rep N p (m+1)) P'.v) (prior G _))
    (hA:Journey D (H.levels.clock.op m p) P (cropStem M Z) (cropStem M T) w c): Journey D (H.levels.clock.op m p) P' Z T w c:=by
    refine ⟨hZ,promoted h he ht hv hx ?_, ?_,hA.carries⟩
    · rw [← hM.start]; exact hA.keeps P.v
    rw [← hM.start]; exact hA.permits
end Stem
end YM.MergeProof.Ribbons.ManyCopies
