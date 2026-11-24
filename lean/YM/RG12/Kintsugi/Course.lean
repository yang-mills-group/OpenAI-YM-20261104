import YM.RG12.Kintsugi.Witness
import YM.RG12.Kintsugi.Zen
/-! # Diagonalizing authentic stations along *arbitrary bad levels*. Retains inverse-column witnesses
(quota & horizon prices). No assertion of quantitative formula at the mesoscopic lenses for
all-coupling orders here: this is for coercivity, for each d after calibrated engineering and
with smooth jets only to any fixed depth.
 -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.RG12.Kintsugi
open Filter Set Function MeasureTheory Analysis Extraction Table Climb Ward Next.UVStress Spec Org Next.Rank Next.Rank.Perch
open Next.Rank.Atlas Next.Rank.East MergeProof MergeProof.East
open scoped Topology BigOperators ContDiff Classical
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(U : Final C f S)(M:∀ d,ℕ→RepChart C d){ϕ:Filter UVIndex}[ϕ.NeBot]
variable {lit:ℕ→Prop}(P:Commission.Port C)(h : Rail.Outbound P lit U.room.cutoff)
variable (hS:Ranked P) (T:MaxwellData C)
local notation "A!"=>C.path.levels
local notation "H!"=>U.room.kernel
local notation "B!"=>Bel C.book
local notation "V!"=>U.sector.derivatives
local notation "p!"=>T.T.W
open Station -- ambiguity

include h hS in
lemma rooted (H:OPE.Facilities C f S) (he:Observing C U.room.cutoff ϕ M)(hf:ϕ≤ f.fuse) (hG:G.Simple) (Bad:ℕ→Prop)
    (hB : ∃ᶠ k in atTop,Bad k ∧ lit k) : ∃ g: ℕ → ℕ,∃ Z:∀ i,TableL C i,
      Tendsto g atTop atTop ∧ (∀ i, Bad (g i) ∧ lit (g i) ∧ Authentic U M P T (g i) i (Z i)) ∧
       ∃ x: Zoom,∀ i, x.r i=Next.Rank.Station.gap (A!) (P.panels i 0).arc (g i):=by
    let Gap (k i:ℕ):= Next.Rank.Station.gap (A!) (P.panels i 0).arc k
    have hY(k i):0<Gap k i:=Next.Rank.Station.gap_pos ..
    let Loc (i:ℕ) (b:ℕ × TableL C i):Prop:=i ≤ b.1 ∧ Bad b.1 ∧ lit b.1 ∧ Authentic U M P T b.1 i b.2
    have hC (i:ℕ) (δ:ℝ)(hδ:0<δ): ∃ b:ℕ × TableL C i, Loc i b ∧ Gap b.1 i<δ:=by
       have hK:= wears U M P h hS T H he hf hG i
       have hg:= Next.Rank.Station.gap_rate (A!) hG (P.panels i 0).arc
       obtain ⟨k,⟨h1,h2⟩,hi,hC,hg⟩:= (hB.and_eventually ((eventually_ge_atTop i).and (hK.and (hg.eventually (gt_mem_nhds hδ))))).exists
       obtain ⟨Z,hZ⟩:=hC h2; exact ⟨(k,Z),⟨hi,h1,h2,hZ⟩,hg⟩
    let V (i:ℕ):={b:ℕ × TableL C i // Loc i b ∧ Gap b.1 i<costHint i}
    let c:V 0:=⟨_,(hC 0 _ (cost_pos _)).choose_spec⟩
    have hv (i : ℕ) (v:V i) :∃ w:V (i+1), Gap w.val.1 (i+1)<Gap v.val.1 i:=by
       obtain ⟨b,hb,hδ⟩:= hC (i+1) _ (lt_min (cost_pos _) (hY v.val.1 i))
       exact ⟨⟨b,hb,hδ.trans_le (min_le_left ..)⟩,hδ.trans_le (min_le_right ..)⟩
    let F (k:ℕ):V k:= Nat.rec c (fun i v=> (hv i v).choose) k
    let g(k):=(F k).val.1
    refine ⟨g,(fun i=>(F i).val.2),tendsto_atTop_mono (f:=fun i:ℕ=>i) (fun i=>(F i).property.1.1) tendsto_id,fun i=> (F i).property.1.2,⟨fun i=>Gap (g i) i,fun i=>hY ..,strictAnti_nat_of_succ_lt (fun i=>(hv i (F i)).choose_spec),?_⟩,fun _=>rfl⟩
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds cost_clears (fun k=>(hY _ _).le) (fun k=>(F k).property.2.le)

variable {g:ℕ→ℕ}{Z:∀ i,TableL C i}{x:Zoom}(ha:∀ i,Authentic U M P T (g i) i (Z i))(hx:∀ i,x.r i=Next.Rank.Station.gap C.path.levels (P.panels i 0).arc (g i))
-- upgrade to same Scaling maps on all compact tests. Don't alter Drop/correction definition
open Spin
abbrev bay (g:ℕ→ℕ)(Z:∀ i,TableL C i)(i:ℕ): Next.UVStress.Panel S:=shore M (g i) i (Z i)
section aligned
local notation "Y!"=> bay (S:=S) M g Z

include ha hx in
lemma approach : Approaches (S:=S) x (Y!) := by
  constructor
  intro n v
  refine ⟨fun k=> (smoothZoom (H!).smooth (panels ((Y!) k) ∘ v) (x.positive k)).sub (smoothDisc T.hT.smooth _),?_⟩
  intro s hK hConf D hp ε hε
  have hh : Tendsto (fun i=>costHint i * Next.UVStress.Station.charge v * D) atTop (𝓝 0) := by
    simpa using (cost_clears.mul_const (Next.UVStress.Station.charge v)).mul_const D
  filter_upwards [eventually_ge_atTop n,eventually_all.mpr (fun i=> eventually_ge_atTop (v i).1),size_ascends.eventually (Work.A05.compact_fits hK hConf),hh.eventually (ge_mem_nhds hε)] with i hk hv hfit hTol t ht hD
  rw [test_sub]
  · rw [hx]; exact ((ha i).limits_ n (hk.trans (Nat.le_add_right ..)) v hv t (ht.trans hfit) D hp hD).trans hTol
  · exact (smoothZoom (H!).smooth (panels ((Y!) i) ∘ v) (x.positive i)).continuousOn
  exact (smoothDisc (T:=B!) T.hT.smooth v).continuousOn
structure Lines (a : (Bel C.book).Hierarchy) (V:DiffPlan (Bel C.book)) (R:Drop (Bel C.book)) : Prop where
   back d v : R d (adjStep V d v)=v
   real d v : R d ((Bel C.book).conj a.spin _ v)=(Bel C.book).conj a.spin d (R d v)
   signed d i v : R d ((Bel C.book).mirror a.spin _ i v)=(Bel C.book).mirror a.spin d i (R d v)
lemma lines (a : (Bel C.book).Hierarchy) (V:DiffPlan (Bel C.book))(hV:V.Inclusions (Bel C.book)) (hv:V.Orientation a.spin) : ∃ R:Drop (Bel C.book), Lines a V R :=by
   choose R hR hr hs using fun d=>signed_section (H:=a) (Nat.le_succ d) hV hv
   exact ⟨R,hR,hr,hs⟩
-- output of the `.equivalences` argument on these exact panels (so can compare to M later!)

include ha hx in
lemma zooms (R:Drop (Bel C.book))(hR:Lines T.hT T.T.W R) :∃ X:Scaling S, X.r=x.r ∧ Approaches (path X) (isoPanel X) ∧ Stable (H!).spin T.hT.spin (V!) (p!) X ∧
      ∀ d,∀ᶠ k in atTop, isoPanel X k d=corrected (V!) (p!) R ((Y!) k) d:=by
  let Q k := corrected (V!) (p!) R ((Y!) k)
  let E:= U.phase.transport
  have hW:=E.injection;have hp:=E.rights;have hV:=T.lit.edges;have hf:=T.lit.hers
  have hh (d:ℕ) : ∀ᶠ i in atTop,StraightAt (H!).spin T.hT.spin ((Y!) i) d:=(eventually_ge_atTop d).mono fun i hi=> (ha i).straight d hi
  have hu d := solid (H:=(H!)) (a:=T.hT) (Y!) hp hf R hR.real hR.signed hh d
  have hA : Approaches x Q := adjusts (H!) T.hT hW hV x R (approach U M P T ha hx)
  have he d : ∀ᶠ k : ℕ in atTop, Bijective (Q k d) := by
    filter_upwards [MeterTest.injects (H!).smooth T.hT hA d] with k hk
    exact ⟨hk,(LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (le_antisymm (LinearMap.finrank_le_finrank_of_injective hk) (cap_given U.room.corrected d))).1 hk⟩
  let w k d := if p : Bijective (Q k d) then LinearEquiv.ofBijective _ p else
    LinearEquiv.ofBijective _ (he d).exists.choose_spec
  let X : Scaling S := ⟨w,fun _ => 1,x.r,fun _ => one_pos,x.positive,x.shrinking,x.limits⟩
  have hX (d) : ∀ᶠ k in atTop, isoPanel X k d=Q k d := by
    filter_upwards [he d] with k hk
    dsimp only [isoPanel,X,w]; rw [dif_pos hk]; rfl
  have hv (k d e : ℕ) (h : d≤e) z : Q k e (T.T.W.rise h z)= (V!).rise h (Q k d z) :=
    balanced (H!) T.hT _ hW hV R hR.back d e h z
  refine ⟨X,rfl,⟨fun n v => ?_⟩,⟨?_,?_,?_⟩,hX⟩
  · refine (hA.values n v).congr (fun k => (smoothZoom (H!).smooth _ (X.positive k)).sub (smoothDisc T.hT.smooth v)) ?_
    filter_upwards [eventually_all.mpr (fun i : Fin n => hX (v i).1)] with k hk
    intro y _; change Next.UVStress.tested _ _ _ _ - _ = Next.UVStress.tested _ _ _ _ - _
    unfold Next.UVStress.tested; rw [show (panels (Q k) ∘ v)=panels (isoPanel X k) ∘ v from funext (fun i => by
      change Sigma.mk (v i).1 (Q k _ _) = Sigma.mk (v i).1 (isoPanel X k (v i).1 (v i).2)
      rw [hk])]; rfl
  · intro d; filter_upwards [hX d,hu d] with k hk ht
    constructor
    · intro h x
      change (isoPanel X k d) _= S.mirror _ _ _ ((isoPanel X k d) _)
      rw [hk]; exact ht.reflects ..
    intro x; change (isoPanel X k d) _= S.conj _ _ ((isoPanel X k d) _)
    rw [hk]; exact ht.bars ..
  · intro d e h
    filter_upwards [hX d,hX e] with k hk he v
    change (isoPanel X k e) _=(V!).rise h ((isoPanel X k d) _)
    rw [he,hk,hv]
  intro d;filter_upwards [hX d] with k hk
  change (isoPanel X k d) _=_
  let h := Nat.zero_le d
  have hU k:Q k 0 ((B!).unit 0)=S.unit 0:= by simpa only [Q,corrected] using (ha k).units
  rw [hk,← T.T.W.fixs hV T.hT.laws h,hv,hU,(V!).fixs hW (H!).laws h]
end aligned
end YM.RG12.Kintsugi
