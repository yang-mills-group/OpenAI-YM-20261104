import YM.OPE.Compatible.Assemblage.Bearing
/-!
# Programs built at a single base, then carried as copies

Actual rotations require coherence for the survivors, not just existence
of some fresh gas estimate. Allow later compression of the gas profile
only over equal barcodes. No individual K rewrite without its matches.
-/
set_option linter.unusedSectionVars true
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.ManyCopies.Stem
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil
open Extra.Trajectories MergeProof.Float
open scoped Topology BigOperators Classical
variable {V I J W :Type} [Fintype V][DecidableEq V]{G:Gauge}{A:History G}
    {N m p:ℕ}{P:Ensemble V}
set_option quotPrecheck false
local notation "a"=> A.rep N p m
local notation "b"=> A.rep N p (m+1)
variable {E:V→ Site (A.S.side m p)}
lemma submit {V : Type} [Fintype V] [DecidableEq V] {G : Gauge} {A : History G}
    {N m p : ℕ} {P : Ensemble V} {E : V → Site (A.S.side m p)} (h:A.Selected)(hn:m≤ N) (X:Config G (A.S.side m p)→ℂ) {Q:ℕ→ Config G (A.S.side m p)→ℂ}(hq:Dominated Q) (o:V→ Site (A.S.side m p)) (he:∀ i,i≠P.v→ o i=affine (P.move i).1 (E i) (o P.v)): ∃ Y:Stem V G (A.S.side m p), Marked (A.rep N p m) E P Y ∧ Y.oil P.v = X ∧ Y.gas P.v=Q ∧ Y.home=o:=by
    let π (i:V):= ((h.represents N p m hn).good.labels.moves (P.move i).1 (E i)).some
    let Z (i:V) j:= stepUp (P.move i) (E i) (Q ((π i).kp.symm j))
    refine ⟨⟨o,fun i=> if i=P.v then X else stepUp (P.move i) (E i) X,fun i=>if i=P.v then Q else Z i⟩,⟨he,?_,?_⟩,if_pos rfl,if_pos rfl,rfl⟩
    · intro i hi; simp only [if_neg hi,if_true,true_and]; refine roam _ _ (π i) (fun j U=>?_); unfold Z;rw [Equiv.symm_apply_apply]
    intro i; change Dominated (if _ then Q else Z i); split; exact hq; exact conduits (P.move i) (E i) _ hq (π i) -- needs explicit
lemma marked_sub {V : Type} [Fintype V] [DecidableEq V] {G : Gauge} {A : History G}
    {N m p : ℕ} {P : Ensemble V} {E : V → Site (A.S.side m p)} {X:Stem V G (A.S.side m p)} (h:A.Selected)(hn:m ≤ N) (he:Marked (A.rep N p m) E P X) (i:V)(ht:i≠P.v) : X.sub (A.rep N p m) i = stepUp (P.move i) (E i) (X.sub (A.rep N p m) P.v):=by
    unfold sub; have hz:(A.rep N p m).activities.Moves (P.move i).1 (E i):= ((h.represents N p m hn).good.labels.moves _ _).some; rw [(he.shine i ht).1]
    exact opals (P.move i) A h hn (E i) (X.oil P.v) hz (he.spends _) (he.spends _) ((he.shine i ht).2)
local notation "μ"=> A.levels.clock.op m p
lemma promoted {X : Stem V G (A.S.side (m+1) p)}{Y:Stem V G (A.S.side m p)}(h:A.Selected)(hn:m<N)(hF: Marked b (fun i=>(μ).ratio.embed (E i)) P X)(he: Integrable (X.sub b P.v) (prior G _)) (hy:Marked a E P Y)(hp:Y.sub a P.v=(μ).push (b).beta (X.sub b P.v)) :
    ∀ i,Y.sub a i=(μ).push (b).beta (X.sub b i):=by
    intro i; by_cases hx:i=P.v; · rwa [hx]
    rw [marked_sub h hn hF i hx, marked_sub h hn.le hy i hx, hp]; have hk:= unison (P.move i) A m N p 0 (E i) _ he
    simp only [blast,pow_zero,one_smul] at hk; exact hk.symm
lemma counterpart {V : Type} [Fintype V] [DecidableEq V] {G : Gauge} {A : History G}
    {N m p : ℕ} {P : Ensemble V} {E : V → Site (A.S.side m p)} {X : Stem V G (A.S.side m p)} (h:A.Selected)(hn:m ≤ N)(he:Marked (A.rep N p m) E P X) (Z':Stem V G (A.S.side m p))(hZ : X.home=Z'.home)(hP:X.oil=Z'.oil)(hQ:∀ i,profile (A.rep N p m).activities (X.gas i)=profile (A.rep N p m).activities (Z'.gas i))(hG:∀ i,Dominated (Z'.gas i)):
    Marked (A.rep N p m) E P Z' ∧ ∀ i,Z'.sub (A.rep N p m) i=X.sub (A.rep N p m) i:=by
    refine ⟨⟨?_,?_,hG⟩,?_⟩
    · rw [← hZ]; exact he.sym
    · simp_rw [← hP,← hQ]; exact he.shine
    intro i; unfold sub; rw [← hP]; exact (coin_port (A.rep N p m) (X.oil i) (hG _) (he.spends _) (hQ i).symm (h.represents N p m hn|>.good.labels))
end YM.MergeProof.Ribbons.ManyCopies.Stem
