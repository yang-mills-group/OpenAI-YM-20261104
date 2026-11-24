import YM.Frontier6.Multi.Diff.Starters
import YM.Frontier6.Multi.Diff.Uniform

/- Orbit calls including moving centroids. Needn't ask compact support of
   F after read, but detectors sampled only on strictly smaller clearances.
   Used for continuity/derivatives at all protected supports. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Road
open Function Filter Finset Set MergeProof.Ribbons MergeProof.Acme Fareway Tale Spec
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius
variable {I J V X:Type} [TopologicalSpace X][Fintype V][DecidableEq V]{G:Gauge}{C:Family G}{F:Extraction.Order}{S: Table C.book}
variable (K:Final C F S) {T : Fareway I}{a b r:ℝ} (p: Probe S)(c:E4)
set_option quotPrecheck false

abbrev diagonal (x:V→ E4)(g:Ortho): V ⊕ Fin p.length→ E4:=Sum.elim x (fun i=>(p.roll K g).exterior i+c)
lemma diagonal_in {x:V→ E4}(g:Ortho)(he:clearC r p.exterior)(hv:Injective x)(hc:∀ i,‖x i-c‖ ≤ r): Injective (diagonal K p c x g):=by
    let q:= p.roll K g; have h(j) := clear_exterior (roll_safe K p he g) j; have ht(j i)(h': x i=q.exterior j+c):False:= by have hz:=hc i; rw [h', add_sub_cancel_right] at hz; exact not_le.mpr (h j) hz
    rintro (i|i) (j|j) h; exacts [congr_arg _ (hv h), (ht j i h).elim,(ht i j h.symm).elim, congr_arg _ ((show Injective q.exterior.ofLp from Points.tail_in q.clear) (add_right_cancel h))]
abbrev gPlan (p:Probe S)(q:V→ S.Tag)(g:Ortho): V ⊕ Fin p.length→ S.Tag:= Sum.elim q (p.roll K g).letter
lemma diag_read (x:V→ E4)(v:V→ S.Tag)(g:Ortho) : poll S S (assembly S (diagonal K p c x g) (gPlan K p v g))=(p.roll K g).tip K (written K c (assembly S x v)):=by unfold diagonal gPlan; rw [concatenates]; rfl
lemma diag_cont {q:X→ E4}{pX:X→ V→ E4}{x:X}{g:Ortho}(hc:ContinuousAt q x)(hv:ContinuousAt pX x) : ContinuousAt (fun z:X × Ortho=> diagonal K p (q z.1) (pX z.1) z.2) (x,g):=by
   have hz:ContinuousAt (fun i:X×Ortho=>pX i.1) (x,g):= hv.comp_of_eq continuousAt_fst rfl
   have hQ:ContinuousAt (fun i:X×Ortho=> q i.1) (x,g):= hc.comp_of_eq continuousAt_fst rfl
   have hC(j:Fin p.length): Continuous (fun i:X×Ortho=> (p.roll K i.2).exterior j):= (PiLp.continuous_apply ..).comp ((spinner p.exterior).comp continuous_snd)
   exact continuousAt_pi.mpr fun i=> by rcases i with i|i; exact (continuous_apply i).continuousAt.comp hz; exact (hC i).continuousAt.add hQ
lemma dial_continuous {q:X→ E4}{pX:X→ V→ E4}{x:X}(he:clearC r p.exterior)(hx:ContinuousAt q x)(hC:ContinuousAt pX x)(hp:Injective (pX x))(hv:∀ i,‖pX x i-q x‖ ≤ r)(v:V→ S.Tag) (g:Ortho) : ContinuousAt (fun t:X × Ortho=> (p.roll K t.2).tip K (written K (q t.1) (assembly S (pX t.1) v))) (x,g):=by
   let Y:= V⊕ Fin p.length; let d (i:Y):ℕ:= Sum.elim (fun i=>(v i).1) (fun i=>(p.letter i).1) i; let w(g:Ortho)(i:Y): S.Field (d i):= Sum.rec (motive:=fun i=> S.Field (d i)) (fun i=>(v i).2) (flying K p g) i
   simp_rw [←diag_read]; have hg(g:Ortho) : gPlan K p v g=(fun i:Y=> ⟨d i,w g i⟩):=funext fun i=>by rcases i with i|i <;> rfl
   simp_rw [hg]; have hh:Continuous w:= continuous_pi fun i=>by rcases i with i|i; exact continuous_const; exact (continuous_apply i).comp (fly_cont K p)
   exact Inspect_cont K none d (diag_cont K p hx hC) (diagonal_in K p (q x) g he hp hv) ((hh.comp continuous_snd).continuousAt)

-- patches, for any IRead w/ continuous on open ν (only then take smaller events)
def snug (c:E4)(r:ℝ)(x:V→ E4) : Prop:= Injective x ∧ ∀ i,‖x i-c‖<r
lemma snug.at {c:X→ E4}{q:X→ V→ E4}{x:X}(hC:ContinuousAt c x)(hq:ContinuousAt q x)(hx:snug (c x) r (q x)) : ∀ᶠ y in 𝓝 x,snug (c y) r (q y):= by
    exact (larger hq hx.1).and (eventually_all.mpr fun i:V=> ((((continuous_apply i).continuousAt.comp hq).sub hC).norm).eventually (gt_mem_nhds (hx.2 i)))
lemma snug.apo {d:ℕ}(he: Frontier6.Safe K d r) {x:V→ E4}(hv:snug c r x)(v:V→ S.Tag): Visible K c d (assembly S x v):= visibles K x he hv.1 (fun i=> (hv.2 i).le) v
set_option maxHeartbeats 800000 in
lemma album_continuous {d:ℕ}(he: Frontier6.Safe K d r){q:X→ E4}{pX:X→ V→ E4}{U:Set X}(hU:IsOpen U)(hx:ContinuousOn q U)(hC:ContinuousOn pX U)(hv:∀ i∈U,snug (q i) r (pX i))(v:V→ S.Tag): ContinuousOn (fun z=> album K (q z) d (assembly S (pX z) v)) U:= by
    apply continuousOn_pi.mpr; intro i; apply continuousOn_pi.mpr; intro p; apply continuousOn_pi.mpr; intro b
    let F(t:X):= album K (q t) d (assembly S (pX t) v) i p b; refine ContinuousMap.continuousOn_of_continuousOn_uncurry F ?_
    let p':= p.val.flip K b; let T (t:X×Ortho):= (p'.roll K t.2).tip K (written K (q t.1) (assembly S (pX t.1) v)); have hz:ContinuousOn T (U ×ˢ univ):=by
       rintro ⟨i,g⟩ hp; let hu:= hU.mem_nhds hp.1; let hh:=hv i hp.1; exact (dial_continuous K p' (flip_safe K p.val (he _ p) b) (hx.continuousAt hu) (hC.continuousAt hu) hh.1 (fun i=>(hh.2 i).le) v g).continuousWithinAt
    exact hz.congr (by rintro ⟨i,g⟩ h; exact (displayed K (snug.apo K _ he (hv i h.1) v)).seats _ _ _ _)
lemma absorb_continuous {d:ℕ}(he: Frontier6.Safe K d r){q:X→ E4}{pX:X→ V→ E4}{U:Set X}(hU:IsOpen U)(hx:ContinuousOn q U)(hC:ContinuousOn pX U)(hv:∀ i∈U,snug (q i) r (pX i))(v:V→ S.Tag): ContinuousOn (fun z=> absorb K (q z) d (assembly S (pX z) v)) U:= (detector K d).continuous.comp_continuousOn (album_continuous K he hU hx hC hv v)
end YM.Frontier6.Road
