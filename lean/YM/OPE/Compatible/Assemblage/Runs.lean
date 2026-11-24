import YM.OPE.Compatible.Assemblage.Singleton

/-!
# A transportable cursor for future marker movements

Roll arbitrary but finite number of levels. Purchases can be recalled
without changing their datum (so in particular all arrays already
parallel with these singers continue together later, after a grouping
with the indicated erosion).
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.ManyCopies.Stem
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil
open Extra.Trajectories MergeProof.Float
open scoped Topology BigOperators Classical
variable {G : Gauge}{A:History G}{V I:Type}[Fintype V][DecidableEq V][Fintype I][DecidableEq I]{N p m k j l:ℕ}
variable {D:∀ N p m:ℕ,m<N→GaugeDoor (A.rep N p (m+1)) (A.rep N p m)}{P:Ensemble V}
abbrev Travel (A:History G)(V:Type)(p:ℕ) := ∀ i:ℕ, Stem V G (A.S.side i p)
abbrev Track (A:History G)(V:Type)(p:ℕ) := ∀ i:ℕ,V→ Site (A.S.side i p)
variable {E o:Track A V p}{Z : Travel A V p}{w:ℕ→ℝ}
set_option linter.unusedSectionVars true
set_option quotPrecheck false
lemma lower_cost {G : Gauge} {V : Type} [Fintype V] [DecidableEq V] {n' n:Side}{t w:ℝ}{S:StepData n n'}{R:Rep G n}{R':Rep G n'}{P:Ensemble V}{D:GaugeDoor R' R}{c:ℂ} {X:Stem V G n'}{X'} (h:Journey D S P X X' w c)(he:t≤w)(hδ:0<t): Journey D S P X X' t c:=by
    refine ⟨h.site,h.keeps,?_,(mul_le_mul_of_nonneg_right he (norm_nonneg _)).trans h.carries⟩
    obtain ⟨p,hp,s,u,hX,hU,hY⟩:= h.permits; refine ⟨p,hp,s,u,?_,?_,hY⟩
    · by_cases hh:0 ≤ s
      · exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he zero_le_two) hh).trans hX
      exact le_trans (mul_nonpos_of_nonneg_of_nonpos (mul_nonneg zero_le_two hδ.le) (le_of_not_ge hh)) zero_le_one
    by_cases hh:0≤ u; · exact (mul_le_mul_of_nonneg_right he hh).trans hU
    exact le_trans (mul_nonpos_of_nonneg_of_nonpos hδ.le (le_of_not_ge hh)) zero_le_one
structure Run (P:Ensemble V) (D:∀ N p m:ℕ,m<N→GaugeDoor (A.rep N p (m+1)) (A.rep N p m)) (N p:ℕ) (k j:ℕ) (E o:Track A V p) (Z:Travel A V p) (w:ℕ→ℝ) : Prop where
   clock : k ≤ j
   ticks : j ≤ N
   fees i:k ≤ i→ i ≤ j → 0< w i
   marks i:k ≤ i→ i ≤ j→ Marked (A.rep N p i) (E i) P (Z i)
   steers i:k ≤ i→ i ≤ j→ (Z i).home=o i
   routes i (hk:k ≤ i)(hi:i<j) : ∃ c:ℂ, Journey (D N p i (hi.trans_le ticks)) (A.levels.clock.op i p) P (Z (i+1)) (Z i) (w (i+1)) c
lemma baseRun {G : Gauge} {A : History G} {V : Type} [Fintype V] [DecidableEq V] {N p : ℕ}
    {D : ∀ N p m : ℕ, m < N → GaugeDoor (A.rep N p (m+1)) (A.rep N p m)} {P : Ensemble V}
    {E o : Track A V p} {Z : Travel A V p} {w : ℕ → ℝ} {i:ℕ}(h:i≤ N)(hr:0<w i)(hp:Marked (A.rep N p i) (E i) P (Z i))(hx:(Z i).home=o i) : Run P D N p i i E o Z w:= ⟨le_rfl,h,fun _ hi he=>le_antisymm he hi ▸ hr,fun _ hi he=>le_antisymm he hi ▸ hp,fun _ hi he=>le_antisymm he hi ▸ hx,fun _ hi he=>False.elim (not_lt_of_ge hi he)⟩ -- orientations
namespace Run
variable (h:Run P D N p k j E o Z w) {w':ℕ→ℝ}{o' E' : Track A V p}{Z': Travel A V p}
include h
omit h in
lemma crop {G : Gauge} {A : History G} {V : Type} [Fintype V] [DecidableEq V] {N p m k j l : ℕ}
    {D : ∀ N p m : ℕ, m < N → GaugeDoor (A.rep N p (m+1)) (A.rep N p m)} {P : Ensemble V}
    {E o : Track A V p} {Z : Travel A V p} {w : ℕ → ℝ}
    (h : Run P D N p k j E o Z w) (hi:k ≤ l)(he:l ≤ m)(hm:m ≤ j) : Run P D N p l m E o Z w :=⟨he,hm.trans h.ticks,fun i hk hq=> h.fees i (hi.trans hk) (hq.trans hm),fun i hk hq=>h.marks i (hi.trans hk) (hq.trans hm),fun i hk hq=>h.steers i (hi.trans hk) (hq.trans hm),fun i hk hq=> h.routes i (hi.trans hk) (hq.trans_le hm)⟩
lemma credit (ht:∀ i:ℕ,k ≤ i→i ≤ j→ 0<w' i)(hp:∀ i:ℕ,k < i→i ≤ j→ w' i ≤ w i) : Run P D N p k j E o Z w':=by
    refine ⟨h.clock,h.ticks,ht,h.marks,h.steers,fun i he hq=>?_⟩
    obtain ⟨a,hA⟩:= h.routes i he hq; exact ⟨a, lower_cost hA (hp _ (lt_of_le_of_lt he i.lt_succ_self) hq) (ht _ (he.trans i.le_succ) hq)⟩
omit h in
lemma shift {G : Gauge} {A : History G} {V : Type} [Fintype V] [DecidableEq V] {N p k j : ℕ}
    {D : ∀ N p m : ℕ, m < N → GaugeDoor (A.rep N p (m+1)) (A.rep N p m)} {P : Ensemble V}
    {E o : Track A V p} {Z : Travel A V p} {w : ℕ → ℝ}
    (h : Run P D N p k j E o Z w) {o' E' : Track A V p} {Z' : Travel A V p} (ht : ∀ i:ℕ,k ≤ i→ i ≤ j→ Z i=Z' i ∧ E i=E' i ∧ o i=o' i): Run P D N p k j E' o' Z' w:=by
    refine ⟨h.clock,h.ticks,h.fees,fun i hk hi=> ?_,fun i hk hi=> ?_,fun i hi hq=>?_⟩
    · rw [← (ht i hk hi).1,← (ht i hk hi).2.1]; exact h.marks i hk hi
    · rw [← (ht i hk hi).1,← (ht i hk hi).2.2]; exact h.steers i hk hi
    rw [← (ht i hi hq.le).1,← (ht (i+1) (hi.trans i.le_succ) hq).1]; exact h.routes i hi hq
omit h in
lemma together {G : Gauge} {A : History G} {V : Type} [Fintype V] [DecidableEq V] {N p m k j : ℕ}
    {D : ∀ N p m : ℕ, m < N → GaugeDoor (A.rep N p (m+1)) (A.rep N p m)} {P : Ensemble V}
    {E o : Track A V p} {Z : Travel A V p} {w : ℕ → ℝ}
    (h : Run P D N p k j E o Z w) (ht:Run P D N p j m E o Z w): Run P D N p k m E o Z w:=by
    refine ⟨h.clock.trans ht.clock,ht.ticks,fun i hi hq=> (le_total i j).elim (h.fees i hi) (fun hz=> ht.fees i hz hq),fun i hi hq=> (le_total i j).elim (h.marks i hi) (fun hz=> ht.marks i hz hq),fun i hi hq=> (le_total i j).elim (h.steers i hi) (fun hz=> ht.steers i hz hq),fun i hi hF=> (lt_or_ge i j).elim (h.routes i hi) (fun hz=> ht.routes i hz hF)⟩ -- hi proof dependent
lemma seams (hy:Z j=Z' j)(ht:Run P D N p j m E o Z' w):
    ∃ Q:Travel A V p, Run P D N p k m E o Q w∧ (∀ i:ℕ,i ≤ j→Q i=Z i)∧ (∀ i:ℕ,j ≤ i → Q i=Z' i):=by
    let Q i:= if i ≤ j then Z i else Z' i; have hw i (he:i ≤ j):Q i=Z i:=if_pos he; have hz i(he:j ≤ i): Q i= Z' i:=by
       obtain h|rfl:=lt_or_eq_of_le he; exact if_neg (not_le.mpr h); exact (hw _ le_rfl).trans hy
    exact ⟨Q,Run.together (h.shift (fun i hi hq=>⟨(hw i hq).symm,rfl,rfl⟩)) (ht.shift fun i hi _=> ⟨(hz i hi).symm,rfl,rfl⟩),hw,hz⟩
end Run
section staircase
variable {p':I→Travel A V p}{o':I→Track A V p}{w':I→ℕ→ℝ}{Y:Config G (A.S.side j p)→Poly (Names V I)}{P:Ensemble V}
    {d t u:ℕ→ℝ}{b:ℕ→ℕ}
    (χ:Guard (Names V I))
variable (hs :∀ x,Run P D N p k j E (o' x) (p' x) (w' x))(hχ:χ.Chordal P.v P.perms)
    (hk:k ≤ j)(hN:j ≤ N)(he:Migrating A k p j E)(hA:A.Selected)
    (hb:∀ i,k ≤ i→ ∀ hi:i<j, Admits (D N p i (hi.trans_le hN)) b (d i) (t i) (u i))
    (F:∀ i:ℕ,V×I→ Site (A.S.side i p)) (hF:∀ i:ℕ,k ≤ i → i ≤ j→∀ x:V×I,F i x=o' x.2 i x.1)
    (hC:∀ i,k ≤ i→ i<j→ Occupancy (F (i+1)) (b i)∧ Occupancy (F i) (b i))
    (hx:∀ i,k ≤ i→ i<j→ χ.Gates (F i) (A.levels.budget i).B (quota V (dropFunds (d i) (fun p=>w' p (i+1)))) (quota V (fun p=>w' p i)) 1)
    (hy:Owned χ (A.rep N p j) (E j) P (fun i=>p' i j) (fun i=>w' i j) ((A.levels.budget j).supportExponent-3) Y)(ht:Integrable Y (prior G _))
include hy ht hx hχ hC hF he hb hA hs hN -- hk maybe unused
lemma whole (hp_:k ≤ m) (hm : m≤ j): Owned χ (A.rep N p m) (E m) P (fun i=>p' i m) (fun i=>w' i m) ((A.levels.budget m).supportExponent-3) (gust A N p j Y m hm) :=by
   have hq(i)(hi:k ≤ i)(ht:i ≤ j): tags (fun a=>p' a i)= F i:= funext fun a=> (congr_fun ((hs a.2).steers i hi ht) a.1)|>.trans (hF i hi ht a).symm
   induction hm using Nat.decreasingInduction with
   | self=> rw [gust_base]; exact hy
   | of_succ i hi ih=>
      have hi' := hp_.trans i.le_succ; have H:= ih hi'; choose c hξ using fun x=> (hs x).routes i hp_ hi
      rw [← he.mare i hp_ hi] at H
      rw [gust_step A N p j Y hi]; exact refill P χ H (gust_live A N p j Y ht hi) hA (hi.trans_le hN) (hb i hp_ hi) (by linarith only) (fun x=>(hs x).marks _ hp_ hi.le) hξ ((hq _ hi' hi).symm ▸ (hC _ hp_ hi).1) ((hq _ hp_ hi.le).symm ▸ (hC _ hp_ hi).2) hχ (fun x=>(hs x).fees i hp_ hi.le) ((hq _ hp_ hi.le).symm ▸ (hx _ hp_ hi)) -- Earth
end staircase
end YM.MergeProof.Ribbons.ManyCopies.Stem
