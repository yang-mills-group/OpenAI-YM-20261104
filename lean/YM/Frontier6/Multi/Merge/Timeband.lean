import YM.Frontier6.Multi.Merge.Funding

/-! Condensation at *all* depths sufficiently large at deep rooms;
    needed for tree commitments. arbitrary legs. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Road.Fork
open Function Filter Finset Set Spec Fareway Tale Lattice Next.Extract Cells MergeProof.Acme
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius
variable {I V:Type} [Fintype V][DecidableEq V]{G:Gauge}{C:Family G}{F:Extraction.Order}{S: Table C.book}{T:Fareway I}
variable {O:V→Type} [heO:∀ i,Fintype (O i)][htO:∀ i,DecidableEq (O i)] [hNm:∀ i,Nonempty (O i)]
variable (K:Final C F S) (hC: Road.Ribbon C F S)
set_option quotPrecheck false
variable {u:I→ Sigma O→ E4}{c:I→ V→ E4}(v:Sigma O→ S.Tag)(z: (Sigma O)×Axis)(t:I→ℝ) (d:ℕ){a b hM p q r w ε:ℝ}
variable (hu:∀ i,Aspect T (fun k=> cutTo i (u k))) (hc:Wide T c a) (h:a<b)(hp:b<p)(hq:p<q)(hr:q<1)
variable (s:I→ StateIndex K) {j k m l:I→ℕ}
lemma cover_cutWalk (i:V) {C:Schedule}(h: CoverWalk u T C j): CoverWalk (fun k=>cutTo i (u k)) T C j:=by
   filter_upwards [h] with k hk; obtain ⟨⟨v,hv⟩,hw⟩:=hk; refine ⟨⟨cutTo i v,?_⟩,fun a=>?_⟩; rw [hv]; rfl; exact (hw a).comp sigma_mk_injective
include hu hc hC h hp hq hr
-- (h:b aft a)(hp etc)
lemma precoast (hh: CoverWalk u T C.S j)(hj: Bench C.S T j r)(hk:Bench C.S T l b)(hP:Bench C.S T k p)(hQ:Bench C.S T m q)
   (he:1<r)(hz:0<p)(hε:0<ε): T.Costs (fun i=> poll S (state K (s i)) (combining K (u i) (c i) v d)) ((∑ i:V,(forestPower (grades (cutTo i v)) q r ε+p)) - d*(q-p)^2):= by
    let X (v':V)(i:I)(c:E4):= assembly S (fun j=> cutTo v' (u i) j+c) (cutTo v' v); let Y(v':V)(i:I)(c:E4):=letter S c ⟨d,absorb K 0 d (seedling (u i) v v')⟩; let Z(v':V):=forestPower (grades (cutTo v' v)) q r ε+p
    have h0(i:V):= fleeting K hC (cutTo i v) d (hu i) (cover_cutWalk i hh) hj hQ hP he hε hr hq hz
    let ξ:= Ultrafilter.of F.fuse; refine (buds K (uC:=c) (ξ:=ξ) (k:=j) s X Y (u:=Z) (r:=fun _=>k) (fun i=>(h0 i).2.1) (fun i=>(h0 i).2.2.1) (fun i=>(h0 i).2.2.2) (fun A F0 h'=> ?_)).cf (Eventually.of_forall fun i=>?_)
    · exact budget_product c _ (Ultrafilter.of_le _) A F0 h' hk (y:=fun _:V=>p) (fun _=>hP) (fun _=>hp) h (((h.trans hp).trans hq).trans hr) hc s hC.grill
    dsimp only; rw [combining_eq]; rfl
lemma timeband (hj: Bench C.S T j r)(hk:Bench C.S T l b)(hP:Bench C.S T k p)(hQ:Bench C.S T m q)(he:1<r)(hz:0<p)(hε:0<ε): T.Costs (fun i=> poll S (state K (s i)) (combining K (u i) (c i) v d)) ((∑ i:V,(forestPower (grades (cutTo i v)) q r ε+p)) - d*(q-p)^2):=by
    exact (shoving K hC v d hu hc (((h.trans hp).trans hq).trans hr) s hj.spacing he).alive hj.spacing.pay (fun _=>C.S.a_pos _) (fun i hi hx=> precoast K hC v d (percolating hu hi he) hc h hp hq hr s (Paces.strides hx) hj hk hP hQ he hz hε)
omit h hp hq hr
lemma dividends (ha:a<1) (w:ℝ): ∀ᶠ d:ℕ in atTop, T.Costs (fun i=> poll S (state K (s i)) (combining K (u i) (c i) v d)) w:=by
    obtain ⟨b,hb,hb'⟩:= exists_between (max_lt_iff.mpr (show _∧_ from And.intro ha zero_lt_one)); obtain ⟨p,hp,hp'⟩:= exists_between hb'; obtain ⟨q,hq,hq'⟩:= exists_between hp'; have h:a<b:= lt_of_le_of_lt (le_max_left ..) hb; have ht:0<b:= (le_max_right ..).trans_lt hb
    obtain ⟨j,hj⟩:= picks C.S C.path.levels.fits.mesh T 2 two_pos; obtain ⟨l,hl⟩:=picks C.S C.path.levels.fits.mesh T b ht; obtain ⟨k,hk⟩:=picks C.S C.path.levels.fits.mesh T p (ht.trans hp); obtain ⟨m,hm⟩:=picks C.S C.path.levels.fits.mesh T q ((ht.trans hp).trans hq)
    let a:=∑ i:V,(forestPower (grades (cutTo i v)) q 2 1 + p); have hz: Tendsto (fun d:ℕ=>(d:ℝ)*(q-p)^2) atTop atTop:= Tendsto.atTop_mul_const (pow_pos (sub_pos.mpr hq) _) tendsto_natCast_atTop_atTop
    filter_upwards [hz.eventually_ge_atTop (a-w)] with k hi; apply (timeband K hC v k hu hc h hp hq hq' s hj hl hk hm one_lt_two (ht.trans hp) zero_lt_one).too; change a-_ ≤ _; linarith only [hi]
-- synchronously for all grade caps sets. Moving labels in Fee theorem later.
end YM.Frontier6.Road.Fork
