import YM.Frontier6.Exact.Seat

/-! Explicit exterior/detector collar. Normal pair coordinates. Kernel
continuity and construction of samples selected much before s is chosen. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6
open Spec Function Filter Set Lattice Wilson MeasureTheory
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}
variable (K:Final C F S)(s:StateIndex K) {d e b n:ℕ}

def Safe (d:ℕ)(r:ℝ):Prop:= ∀ (i:Fin (d+1))(p:(hand K i.val).list), clearC r p.val.exterior
lemma Safe.limits (d:ℕ): ∃ r:ℝ, 0 < r ∧ Safe K d r:=by
   choose r hr hQ using fun (i:Fin (d+1))(p:(hand K i.val).list)=> gap_compact (isCompact_singleton (x:=Points.cons 0 p.val.exterior)) (singleton_subset_iff.mpr p.val.clear)
   obtain ⟨a,ha,h⟩:= ((show ∀ᶠ a:ℝ in 𝓝[>] 0,0<a from self_mem_nhdsWithin).and (eventually_all.mpr fun i=>eventually_all.mpr fun p=> (show ∀ᶠ a in 𝓝[>] 0,a≤r i p from mem_nhdsWithin_of_mem_nhds (ge_mem_nhds (hr i p))))).exists
   exact ⟨a,ha,fun i p=> gap_down (hQ i p _ (mem_singleton _)) (h i p)⟩
lemma Safe.down {r a:ℝ}(hf:Safe K d r)(he:e≤d)(ha:a≤r): Safe K e a:=fun i p=>gap_down (hf (Fin.castLE (Nat.succ_le_succ he) i) p) ha
lemma flip_safe {r:ℝ} (p:Probe S)(he:clearC r p.exterior)(b:Bool) : clearC r (p.flip K b).exterior:= by cases b <;> exact he
lemma roll_safe {r:ℝ} (p:Probe S)(he:clearC r p.exterior)(g:Ortho): clearC r (p.roll K g).exterior:= clear_rotates g r p.exterior he

def Collar (r:ℝ) : Set E4:= {x | 0 < ‖x‖ ∧ ‖x‖ ≤ r/2}
lemma collar_shrinks {a r:ℝ}(he:a≤ r): Collar a ⊆ Collar r:=fun _ (hx: _ ∧ _) => And.intro hx.1 (le_trans hx.2 (by linarith only [he]))
lemma collar_eq (r:ℝ): Collar r=Metric.closedBall (0:E4) (r/2) \ {(0:E4)}:=by ext x; simp [Collar,norm_pos_iff,and_comm]
lemma cosize (x:E4): ‖normal2 x‖≤‖x‖:=by
   rw [normal_size]; exact mul_le_of_le_one_left (norm_nonneg _) (by nlinarith only [normalRat_sq]) -- check

def beam (x:E4)(y:Points n): Points (n+2):=Points.cons (normal2 x) (Points.cons (-normal2 x) y)
lemma beam_clear {r:ℝ}{x:E4}{y:Points n}(he:x∈ Collar r)(hc:clearC r y): beam x y∈conf _:= pairs_clear ((cosize x).trans he.2) (normal_ne _ (norm_pos_iff.mp he.1)) hc

@[fun_prop] lemma n2_cont : Continuous normal2:=by unfold normal2 aside; fun_prop
lemma beam_cont : Continuous (fun z:E4 × Points n=> beam z.1 z.2):=by unfold beam Points.cons points; fun_prop
lemma reading_cont' (x:E4)(v:Fin n→ S.Tag)(B:S.Field d){L:Set (Points n)}(h:∀ y∈ L,Points.cons x y∈conf _):
   ContinuousOn (fun y=> reading K s x y v d B) L:= by
   simp_rw [reads_at]; exact (S.class_smooth (state K s) (hierarchy K s).smooth _).continuousOn.comp (show Continuous (fun y:Points n=> Points.cons x y) by unfold Points.cons points; fun_prop).continuousOn (fun x hx=> h x hx)

variable (B:S.Field b)(D:S.Field d)
lemma pair_cont' (v:Fin n→ S.Tag){L:Set (E4 × Points n)}(h:∀ z∈ L,beam z.1 z.2∈conf _):
   ContinuousOn (fun z:E4 × Points n=> pair K B D z.1 s n z.2 v) L:=by simp_rw [pair_at]; exact (S.class_smooth (state K s) (hierarchy K s).smooth _).continuousOn.comp beam_cont.continuousOn (fun x hx=> h x hx)
lemma pair_collar (v:Fin n→ S.Tag)(r:ℝ):ContinuousOn (fun z:E4 × Points n=> pair K B D z.1 s n z.2 v) (Collar r ×ˢ {x:Points n| clearC r x}):= pair_cont' K s B D v (fun x hx=> beam_clear hx.1 hx.2)
set_option maxHeartbeats 200000
lemma pair_probe_cont {r:ℝ}(p:Probe S)(hp:clearC r p.exterior): ContinuousOn (fun z:E4 × Ortho => (p.roll K z.2).tip K (pair K B D z.1)) (Collar r ×ˢ univ):=by
   let x (z:E4 × Ortho):= (z.1,Points.move z.2 p.exterior)
   let f (z:E4 × Ortho)(v:Fin p.length → S.Tag):= pair K B D z.1 none p.length (x z).2 v
   let L:= Collar r ×ˢ (univ:Set Ortho)
   have hx: Continuous x:= continuous_fst.prodMk ((spinner p.exterior).comp continuous_snd)
   have hX:∀ z∈ x '' L, beam z.1 z.2∈conf _:= by rintro z ⟨w,hw,rfl⟩; exact beam_clear hw.1 (clear_rotates w.2 r p.exterior hp)
   have ht(v:Fin p.length→ S.Tag):ContinuousOn (fun z=> f z v) L:= by
     let Z (w:E4 × Points p.length):= pair K B D w.1 none p.length w.2 v
     rw [show (fun z=> f z v)= (Z ∘ x) from rfl]; exact (show ContinuousOn Z (x '' L) from pair_cont' K none B D v hX).comp hx.continuousOn (mapsTo_image x L)
   let V (z:E4 × Ortho): ScaleVec S (fun i=>(p.letter i).1):= flying K p z.2
   have hw :ContinuousOn (fun z=> f z (paint S (fun i => (p.letter i).1) (V z))) L:= VMulti.chords f (fun z _=> pair_multi K none B D z.1 (x z).2) ht V ((fly_cont K p).comp continuous_snd)
   apply hw.congr ; intro x hx; rfl
lemma fixed_spot {r:ℝ}(p:Probe S)(hp:clearC r p.exterior)(b₀:Bool)(x:E4)(hx:x∈Collar r): Continuous (spotlight K (pair K B D x) b₀ p):=by
   let q:=p.flip K b₀
   let z:Ortho→ E4×Ortho:=fun w=>(x,w)
   let L:=Collar r ×ˢ (univ:Set Ortho); have hz:Continuous z:= continuous_const.prodMk continuous_id
   have hX:MapsTo z univ L:= fun y hy=>⟨hx,hy⟩
   let y(x:E4 × Ortho):= (q.roll K x.2).tip K (pair K B D x.1)
   have hy: ContinuousOn y L:=pair_probe_cont K B D q (flip_safe K p hp b₀)
   rw [show spotlight K (pair K B D x) b₀ p=y ∘ z from rfl]
   exact continuousOn_univ.mp (hy.comp hz.continuousOn hX)
lemma pair_observe {r:ℝ}(he:Safe K e r){x:E4}(hr:x∈Collar r): observable K e (pair K B D x):=
   ⟨fun i p b=> ⟨spotlight K (pair K B D x) b p.val,fixed_spot K B D p.val (he i p) b x hr⟩,⟨fun _ _ _ _=> rfl⟩⟩
lemma display_cont {r:ℝ} (he:Safe K e r): ContinuousOn (fun x=> display K e (pair K B D x)) (Collar r):=by
   let f(x:E4):=pair K B D x
   apply continuousOn_pi.mpr; intro i; apply continuousOn_pi.mpr; intro p; apply continuousOn_pi.mpr; intro b
   refine ContinuousMap.continuousOn_of_continuousOn_uncurry (fun x=> display K e (f x) i p b) ?_
   exact (pair_probe_cont K B D (p.val.flip K b) (flip_safe K p.val (he i p) b)).congr (by rintro ⟨x,y⟩ hz; exact (displayed K (pair_observe K B D he hz.1)).seats i p b y)
lemma capture_cont {r:ℝ}(he:Safe K e r) : ContinuousOn (fun x=> capture K e (pair K B D x)) (Collar r):= (detector K e).continuous.comp_continuousOn (display_cont K B D he)
end YM.Frontier6
