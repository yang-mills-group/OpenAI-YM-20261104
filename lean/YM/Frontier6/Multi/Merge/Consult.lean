import YM.Frontier6.Multi.Merge.Timeband

/-! The price order can be fixed per signed channel and **valuation**, independent
    of motion in that forest. Needed only as intermediate (forests get uniform
    epsilons). -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Road.Fork
open Function Filter Finset Set Spec Fareway Tale Lattice Next.Extract Cells MergeProof.Acme
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius
variable {I V:Type} [Fintype V][DecidableEq V]{G:Gauge}{C:Family G}{F:Extraction.Order}{S: Table C.book}
variable {O:V→Type} [heO:∀ i,Fintype (O i)][htO:∀ i,DecidableEq (O i)] [hNm:∀ i,Nonempty (O i)]
variable (K: Final C F S)(hC: Road.Ribbon C F S) {a:ℝ}
set_option quotPrecheck false
include hC
lemma turnover (v: Sigma O→ S.Tag) (ha:a<1) (w:ℝ): ∀ᶠ d:ℕ in atTop, ∀ (I:Type)(T:Fareway I)(u:I→ Sigma O→ E4) (c:I→ V→ E4), (∀ i,Aspect T (fun k=> cutTo i (u k)))→ Wide T c a→ ∀ s:I→ StateIndex K,T.Costs (fun i=> poll S (state K (s i)) (combining K (u i) (c i) v d)) w:=by
    obtain ⟨b,hb,hb'⟩:= exists_between (max_lt_iff.mpr (show _∧_ from And.intro ha zero_lt_one)); obtain ⟨p,hp,hp'⟩:= exists_between hb'; obtain ⟨q,hq,hq'⟩:= exists_between hp'; have h:a<b:= lt_of_le_of_lt (le_max_left ..) hb; have ht:0<b:= (le_max_right ..).trans_lt hb
    let u':=∑ i:V,(forestPower (grades (cutTo i v)) q 2 1 + p); have hz: Tendsto (fun d:ℕ=>(d:ℝ)*(q-p)^2) atTop atTop:= Tendsto.atTop_mul_const (pow_pos (sub_pos.mpr hq) _) tendsto_natCast_atTop_atTop
    filter_upwards [hz.eventually_ge_atTop (u'-w)] with d hi I T u c hu hc s; obtain ⟨j,hj⟩:= picks C.S C.path.levels.fits.mesh T 2 two_pos; obtain ⟨l,hl⟩:=picks C.S C.path.levels.fits.mesh T b ht; obtain ⟨k,hk⟩:=picks C.S C.path.levels.fits.mesh T p (ht.trans hp); obtain ⟨m,hm⟩:=picks C.S C.path.levels.fits.mesh T q ((ht.trans hp).trans hq)
    apply (timeband K hC v d hu hc h hp hq hq' s hj hl hk hm one_lt_two (ht.trans hp) zero_lt_one).too; change u'-_ ≤ _; linarith only [hi]
end YM.Frontier6.Road.Fork
