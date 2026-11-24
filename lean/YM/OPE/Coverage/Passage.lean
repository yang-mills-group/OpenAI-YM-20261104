import YM.Next.PHASE.Passage
import YM.Next.UV_STRESS.Gate

/-!
# Train mixed bounds at calibrated labels along a chosen ordered subfilter

The residue/margin budgeting and generic-gap passage here are the arguments
of `YM.Next.PHASE.Passage` extended to moving labels with fixed-grade limits
(use actual cutoff moments on precisely the same arrays). This extra form
will let the large block costs for each replicated main slot be read from its
own calibrated shelf, NOT charged also to more expensive exterior insertions.
No joint mesh & volume sequence. The subfilter is for taking a fitted-field
limit on a fixed `Family`; ordinary moments still satisfy `PointLimits` there.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace YM.OPE.Coverage.Pass
open Function Set Filter Lattice Cells Extraction Extraction.Gaps Wilson Next.UVStress Next.Phase
open scoped Topology BigOperators Matrix.Norms.Frobenius
private def ceilPoint (t : ℝ) (x : E4) : Cover := fun a => ⌈x a / t⌉

private lemma round_near (t : ℝ) (ht : 0<t) (x y : E4) (K : ℕ) (h : ∀ a : Axis, |y a-x a| ≤ t*K) :
    ∀ a, ((ceilPoint t y - ceilPoint t x : Cover) a).natAbs ≤ K := by
  intro a
  have he {w z : ℝ} (he : w-z ≤ t*K) : ⌈w/t⌉ ≤ ⌈z/t⌉ + (K:ℤ) := by
    rw [← Int.ceil_add_natCast]
    apply Int.ceil_le_ceil
    apply (div_le_iff₀ ht).mpr
    rw [add_mul,div_mul_cancel₀ _ ht.ne']; linarith
  obtain ⟨ha,hb⟩ := abs_le.mp (h a)
  have hh := he hb
  have hh' := he (show x a-y a ≤ t*K by linarith)
  change (⌈y a/t⌉ - ⌈x a/t⌉).natAbs ≤ K
  omega

private lemma round_same {n : Side} (T : Tiling n) (t : ℝ) (ht : 0<t) (x y : E4)
    (H : Pattern (t*T.side.val) x y) (a : Axis) :
    stripe T (wrap n (ceilPoint t x)) a = stripe T (wrap n (ceilPoint t y)) a := by
  obtain ⟨d,hd⟩ := H a
  have he : ceilPoint t x a = ceilPoint t y a + d*T.side.val := by
    have hh : x a/t=y a/t + ((d*T.side.val : ℤ) : ℝ) := by rw [hd]; push_cast; field_simp
    unfold ceilPoint; rw [hh, Int.ceil_add_intCast]
  unfold stripe
  change T.hom (((ceilPoint t x a:ℤ): Per n)-_) = T.hom (((ceilPoint t y a:ℤ):Per n)-_)
  rw [he,map_sub,map_sub,map_intCast,map_intCast,Int.cast_add,Int.cast_mul, Int.cast_natCast,ZMod.natCast_self,mul_zero,add_zero]

private lemma room_cast (S : Schedule) {f k N : ℕ} (p : ℕ) (h : f ≤ k) (hk : k ≤ N) (L n : ℕ)
    (hp : (n:ℝ)*(2*((L:ℝ)*S.a k)) < S.a f) : n*(2*(L*span S hk p)) < span S (h.trans hk) p := by
  apply (Nat.cast_lt (α:=ℝ)).mp; apply lt_of_mul_lt_mul_left _ (S.a_pos N).le
  have hh a (ha : a ≤ N) : S.a N * span S ha p = S.a a := S.embeds_scale (S.toDepth ha p)
  rw [hh]; rw [← hh k hk] at hp; push_cast; linarith

private lemma separated_sites (S : Schedule) {n N p m : ℕ} (hm : m ≤ N)
    (w : Fin n → Cover) (i j : Fin n) (x : Points n) (hx : x=tag (S.a N) w)
    (hoff : ∀ a, off S p (distances x j i a) |distances x j i a|)
    (hgap : S.a m < cubedist (x i) (x j)) :
    span S hm p < separation (wrap (S.side N p) (w i)) (wrap (S.side N p) (w j)) := by
  obtain ⟨a,ha⟩ : ∃ a : Axis, S.a m < |distances x j i a| := by
    by_contra! h
    exact hgap.not_ge ((dist_pi_le_iff (f := WithLp.ofLp (x i)) (g := WithLp.ofLp (x j)) (S.a_pos m).le).mpr
      (fun a => by rw [Real.dist_eq]; exact h a))
  let v := wrap (S.side N p) (w i) - wrap (S.side N p) (w j)
  let z := lift v
  subst x
  have he := Gaps.torus S (z a) (show wrap (S.side N p) (w i-w j) a = wrap (S.side N p) z a by
    rw [map_sub,wrap_lift (x := v)]) (hoff a)
  have hp : |((z a : ℤ) : ℝ)| = ((z a).natAbs : ℝ) := by
    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
  rw [hp] at he
  apply lt_of_lt_of_le _ (component_le v a)
  apply (Nat.cast_lt (α:=ℝ)).mp; apply lt_of_mul_lt_mul_left _ (S.a_pos N).le
  rw [show S.a N * span S hm p = S.a m from S.embeds_scale (S.toDepth hm p)]
  exact ha.trans_le he

variable {ι κ : Type*} [Fintype ι] [Fintype κ] {n : ℕ} (e : ι ⊕ κ ≃ Fin n)

private lemma gapped_open (s r : ℝ) : IsOpen {x : Points n | Gapped e s r x} := by
  rw [isOpen_iff_mem_nhds]
  intro x H
  change Gapped e s r x at H
  have ht i j a (h : a < cubedist (x i) (x j)) : ∀ᶠ y : Points n in 𝓝 x, a < cubedist (y i) (y j) := by
    have hc : Continuous (fun y : Points n => cubedist (y i) (y j)) := by unfold cubedist; fun_prop
    exact hc.continuousAt.eventually (lt_mem_nhds h)
  have h₀ : ∀ᶠ y : Points n in 𝓝 x, ∀ i j : ι, i≠j → s < cubedist (y (e (.inl i))) (y (e (.inl j))) :=
    eventually_all.mpr fun i => eventually_all.mpr fun j => eventually_all.mpr fun h => ht _ _ _ (H.1 i j h)
  have h₁ : ∀ᶠ y : Points n in 𝓝 x, ∀ (i : ι) (j : κ), s < cubedist (y (e (.inl i))) (y (e (.inr j))) :=
    eventually_all.mpr fun i => eventually_all.mpr fun j => ht _ _ _ (H.2.1 i j)
  have h₂ : ∀ᶠ y : Points n in 𝓝 x, ∀ i j : κ, i≠j → r < cubedist (y (e (.inr i))) (y (e (.inr j))) :=
    eventually_all.mpr fun i => eventually_all.mpr fun j => eventually_all.mpr fun h => ht _ _ _ (H.2.2 i j h)
  exact h₀.and (h₁.and h₂)

variable {G : Gauge} (C : Family G)

omit [Fintype ι] in
private lemma margins {N p m k l b P : ℕ} (hm : m≤k) (hk : k≤l) (hl : l≤b) (hb : b ≤ N)
    (x : ι → E4) (z : Fin P → E4) (t : ι → E4)
    (r : κ → Site (C.side N p)) (patterns : ∀ i, ∃ j, Pattern (C.S.a m) (x i) (z j))
    (htags : ∀ i a, |t i a-x i a| ≤ C.S.a k) (headroom : (P:ℝ)*(2*(5*C.S.a k)) < C.S.a m)
    (side : (Fintype.card κ : ℝ)*(2*(3*C.S.a b)) < C.S.a l) :
    let h := (hm.trans hk).trans (hl.trans hb)
    ∃ o : Site (C.side N p),
      (∀ i, Inside ((center C.S p h 0).newly o) (3*span C.S (hk.trans (hl.trans hb)) p)
        (wrap _ (ceilPoint (C.S.a N) (t i)))) ∧
      (∀ j, Inside ((center C.S p (hl.trans hb) 0).newly o) (3*span C.S hb p) (r j)) := by
  intro h; classical
  let T := center C.S p h 0
  let f : k≤N := hk.trans (hl.trans hb)
  let d := span C.S f p
  have hp := C.S.a_pos N
  have hs : C.S.a N * d=C.S.a k := C.S.embeds_scale (C.S.toDepth f p)
  let U (x : E4) := wrap (C.side N p) (ceilPoint (C.S.a N) x)
  have hK : P*(2*(5*d)) < T.side.val := room_cast C.S p hm f 5 P (by norm_cast)
  have hd : 0 < 5*d := Nat.mul_pos (by decide) (C.S.toDepth f p).count.property
  obtain ⟨o,ho⟩ := T.fits_together (fun j => U (z j)) (5*d) hd hK
  let X := T.newly o
  have Xlink : X.kind=.link := rfl
  have he (i) : Inside X (5*d) (U (x i)) := by
    obtain ⟨j,hj⟩ := patterns i
    have H : C.S.a N * X.side.val = _ := C.S.embeds_scale (C.S.toDepth h p)
    rw [inside_stripe X Xlink]; intro a
    rw [show stripe X (U (x i)) a = stripe X (U (z j)) a from round_same X _ hp _ _ (H.symm ▸ hj) a]
    exact (inside_stripe X Xlink _ _).mp (ho j) a
  let Y := center C.S p (hl.trans hb) 0
  have hY : Fintype.card κ*(2*(3*span C.S hb p))<Y.side.val := room_cast C.S p hl hb 3 _ (by norm_cast)
  obtain ⟨w,hw,H⟩ := shift_into Y r o rfl (3*span C.S hb p)
    (Nat.mul_pos (by decide) (C.S.toDepth hb p).count.property) hY
  refine ⟨o + wrap _ w,fun i => ?_,H⟩
  have hy : Y.side.val ≤ d := Nat.le_of_dvd (C.S.toDepth f p).count.property (Around.inherits hk (hl.trans hb))
  have ht := inside_after X Xlink _ w _ d (he i) (fun a => ((hw a).le.trans hy))
    (round_near _ hp (x i) (t i) d (fun a => (htags i a).trans_eq hs.symm))
  rw [show U (x i)+_ = U (t i) from (by unfold U; rw [map_sub]; abel)] at ht
  exact ht

private lemma numeric_bound (H : C.Makes) {N p m k l b P : ℕ} (hm : m≤k) (hk : k≤l) (hl : l≤b)
    (hb : b ≤ N) (x : Points n) (z : Fin P → E4) (v : Fin n → C.book.Token)
    (patterns : ∀ i : ι, ∃ j, Pattern (C.S.a m) (x (e (.inl i))) (z j))
    (headroom : (P:ℝ)*(2*(5*C.S.a k)) < C.S.a m)
    (side : (Fintype.card κ : ℝ)*(2*(3*C.S.a b)) < C.S.a l)
    (A B : ℝ) (hB : 0 ≤ B) (ha : ∀ i, Single C (v (e (.inl i))) A k N p)
    (hf : ∀ j, Single C (v (e (.inr j))) B b N p)
    (y : Points n) (htags : ∀ (i : Fin n) a, |y i a - x i a| ≤ C.S.a k)
    (s : Points n) (hs : s=tag (C.S.a N) (address (C.S.a N) y))
    (hx : Gapped e (C.S.a m) (C.S.a l) s)
    (hoff : ∀ i j a, off C.S p (distances s i j a) |distances s i j a|) :
    let u := address (C.S.a N) y
    ‖C.numeric N p v (fun i => wrap _ (u i))‖ ≤ A ^ Fintype.card ι * B ^ Fintype.card κ := by
  intro u
  let f (i) := e (Sum.inl i); let g i := e (Sum.inr i)
  let X i := wrap (C.side N p) (u i)
  have hg : l≤N := hl.trans hb
  have he := hk.trans hg
  let D := center C.S p (hm.trans he) 0
  let E := center C.S p hg 0
  obtain ⟨o,hox,hoy⟩ := margins (ι := ι) C hm hk hl hb (fun i => x (f i)) z
    (fun i => y (f i)) (X ∘ g) patterns (fun i => htags _) headroom side
  let T := D.newly o; let Y := E.newly o
  have hh : C.numeric N p v X = moment (C.beta N p)
      (fun U => (∏ i : ι, C.seen (v (f i)) (X (f i)) U) * ∏ i : κ, C.seen (v (g i)) (X (g i)) U) := by
    rw [C.num]; unfold moment
    apply MeasureTheory.integral_congr_ae
    refine Eventually.of_forall fun U => ?_
    have hi := Equiv.prod_comp e (fun i => C.seen (v i) (X i) U)
    rw [Fintype.prod_sum_type] at hi; exact hi.symm
  change ‖C.numeric N p v X‖ ≤ _; rw [hh]
  exact cutoff_bound (Y := Y) (T := T) H rfl rfl rfl (Around.inherits (C:=C) (hm.trans hk) hg)
    he hb (Around.inherits (C:=C) hm he) (Around.inherits (C:=C) hl hb)
    (v ∘ f) (v ∘ g) (X ∘ f) (X ∘ g) hox hoy
    (fun i j h => separated_sites C.S (hm.trans he) u _ _ s hs (hoff _ _) (hx.1 i j h))
    (fun i j => separated_sites C.S (hm.trans he) u _ _ s hs (hoff _ _) (hx.2.1 i j))
    (fun i j h => separated_sites C.S hg u _ _ s hs (hoff _ _) (hx.2.2 i j h))
    A B hB ha hf


/-- A calibration at this raw grade read by the subfilter. It might represent
the field by a different `v.2` at each mesh/period; no fixed-preimage budget
on the ordered tail is needed. -/
def Reading (𝓛 : Filter (ℕ×ℕ)) (v : C.book.Token) (A : ℝ) (m : ℕ) :=
    ∃ t: (ℕ×ℕ)→C.book.Ref v.1, Tendsto t 𝓛 (𝓝 v.2) ∧ ∀ᶠ i in 𝓛, Single C ⟨v.1, t i⟩ A m i.1 i.2

omit [Fintype ι] [Fintype κ] in
lemma Reading.moves {𝓛 : Filter (ℕ×ℕ)} {v : C.book.Token} {A : ℝ} {m : ℕ} (h : Reading C 𝓛 v A m)
    (u : Spin.Frame) : Reading C 𝓛 (Spin.token C.book v u) A m := by
   rcases v with ⟨g,w⟩
   obtain ⟨t,ht,hf⟩:=h
   rcases u with ⟨j,-| -⟩
   · have h': Tendsto (fun i=> C.book.mirrorGroup g j (t i)) 𝓛 (𝓝 (C.book.mirrorGroup g j w)):=
        ((C.book.mirrorGroup _ _).continuous_of_finiteDimensional.continuousAt.tendsto.comp ht)
     change Reading _ _ (⟨g,C.book.mirrorGroup g j w⟩:C.book.Token) _ _
     exact ⟨_,h',hf.mono fun i hi=>hi.moves (j,false)⟩
   have h': Tendsto (fun i=> star (C.book.mirrorGroup g j (t i))) 𝓛 (𝓝 (star (C.book.mirrorGroup g j w))):=
        ((C.book.mirrorGroup _ j).continuous_of_finiteDimensional.continuousAt.tendsto.comp ht).star
   change Reading _ _ (⟨g,star (C.book.mirrorGroup g j w)⟩:C.book.Token) _ _
   exact ⟨_,h',hf.mono fun i hi=>hi.moves (j,true)⟩

-- Pass via the same iterated-limit PointLimits, but the numeric inequality
-- and convergence can now both be read in `𝓛`, even when no separate
-- fiber extraction simultaneously works for all prescribed periods.
omit [Fintype ι] [Fintype κ] in
lemma rounded {g : Caps n}(v:Next.UVStress.Bud C g)(H:Extraction.Order)(𝓛 : Filter (ℕ×ℕ)){S:Table C.book}
  (he : 𝓛 ≤ H.fuse) (hs:H.PointLimits C S)(y:Points n)(hy:y∈generic n):
  let r N:= address (C.S.a N) y
  let V:=fun j=> (⟨g j,v j⟩:C.book.Token)
  Tendsto (fun i:ℕ×ℕ=> C.numeric i.1 i.2 V (fun j=>wrap _ (r i.1 j))) 𝓛 (𝓝 (S.read y V)) := by
    intro r V
    obtain ⟨Q,hQ,hP⟩:=hs
    refine Order.along (f:=H) (p:=fun p=> y∈Cyclic C.S p n) (L:=fun N p=>C.numeric N p V (fun j=>wrap _ (r N j))) ?_ |>.mono_left he
    refine (show H.limits (fun p=> y∈Cyclic C.S p n) _ _ from ⟨?_,fun p=>(Q p).read y V,?_,?_⟩)
    · filter_upwards [H.per.cofinal.eventually (room C.S (isCompact_singleton (x:=y)))] with i hi using (no_wrap_tie C.S (hi (mem_singleton y))).2 hy
    · intro p hp
      exact H.evaluated C hQ p n V y hp _ (chosen (S:=C.S) y |>.comp H.mesh.cofinal)
    · apply Metric.tendsto_nhds.mpr; intro ε hε
      filter_upwards [hP n {y} isCompact_singleton (singleton_subset_iff.mpr hy) V ε hε] with i hi
      rw [dist_eq_norm]; exact hi y (mem_singleton _)

/-- The same bound as `Next.Phase.point_bound` using the `Reading` along an
arbitrary prescribed nontrivial subfilter of the ordered cutoffs before the
word passes to the Hilbert estimate. The `Reading` must be simultaneous
among retained tokens, not a cutoff dependent on number of copies. -/
theorem point_finance (H : C.Makes) (f : Extraction.Order) (𝓛 : Filter (ℕ×ℕ)) [𝓛.NeBot] (hL : 𝓛 ≤ f.fuse)
    (S : Table C.book) (ht : S.Smooth) (he : f.PointLimits C S) (m k l b : ℕ) (hm : m≤k) (hk : k≤l) (hl : l≤b)
    (x : Points n) (hc : x∈conf n) (v : Fin n → C.book.Token)
    (hx : Gapped e (C.S.a m) (C.S.a l) x) (P : ℕ) (z : Fin P → E4)
    (patterns : ∀ i : ι, ∃ j, Pattern (C.S.a m) (x (e (.inl i))) (z j))
    (headroom : (P:ℝ)*(2*(5*C.S.a k)) < C.S.a m)
    (side : (Fintype.card κ : ℝ)*(2*(3*C.S.a b)) < C.S.a l)
    (A B : ℝ) (hB : 0 ≤ B)
    (ha : ∀ i, Reading C 𝓛 (v (e (.inl i))) A k)
    (hf : ∀ j, Reading C 𝓛 (v (e (.inr j))) B b) :
    ‖S.read x v‖ ≤ A ^ Fintype.card ι * B ^ Fintype.card κ := by
  classical
  let gr:Caps n:=fun i=> (v i).1
  have heQ (i:Fin n) : ∃ Y:(ℕ×ℕ)→ C.book.Ref (gr i), Tendsto Y 𝓛 (𝓝 (v i).2) ∧
       (∀ j:ι, e (Sum.inl j)=i → ∀ᶠ t in 𝓛, Single C ⟨gr i, Y t⟩ A k t.1 t.2) ∧
       (∀ j:κ, e (Sum.inr j)=i → ∀ᶠ t in 𝓛, Single C ⟨gr i, Y t⟩ B b t.1 t.2) := by
      obtain ⟨j,rfl⟩:= e.surjective i
      rcases j with s|s
      · rcases ha s with ⟨t,ht,hg⟩
        refine ⟨t,ht,?_,?_⟩
        · intro l heq
          exact hg
        intro l heq; cases e.injective heq
      rcases hf s with ⟨t,ht,hg⟩
      refine ⟨t,ht,?_,?_⟩
      · intro l heq; cases e.injective heq
      intro l heq; exact hg
  choose Y hT h₁ h₂ using heQ
  let u t : Fin n→C.book.Token := fun i=> ⟨gr i, Y i t⟩
  have hw : ∀ᶠ t in 𝓛, (∀ i, Single C (u t (e (.inl i))) A k t.1 t.2) ∧
        (∀ j, Single C (u t (e (.inr j))) B b t.1 t.2) :=
    (eventually_all.mpr (fun i:ι=>h₁ _ i rfl)).and (eventually_all.mpr (fun i:κ=>h₂ _ i rfl))
  let W := {s | Gapped e (C.S.a m) (C.S.a l) s}
  have hopen := gapped_open (e := e) (C.S.a m) (C.S.a l)
  have hr := (conf_open _).mem_nhds hc
  have h : ContinuousAt (fun y => S.read y v) x := ((S.smooth_read ht v).continuousOn x hc).continuousAt hr
  haveI : NeBot (𝓝[generic n] x) := mem_closure_iff_nhdsWithin_neBot.mp (Dash.full n x)
  refine le_of_tendsto (h.norm.continuousWithinAt (s := generic n)).tendsto ?_
  have near (i : Fin n) (a : Axis) : ∀ᶠ y : Points n in 𝓝 x, |y i a-x i a| ≤ C.S.a k := by
    have hc : Continuous (fun y : Points n => |y i a-x i a|) := by fun_prop
    exact hc.continuousAt.eventually (ge_mem_nhds (by simpa using C.S.a_pos k : |x i a-x i a| < C.S.a k))
  have hr := eventually_all.mpr (fun i : Fin n => eventually_all.mpr (near i))
  filter_upwards [mem_nhdsWithin_of_mem_nhds (show W ∈ 𝓝 x from hopen.mem_nhds hx),
    mem_nhdsWithin_of_mem_nhds hr,self_mem_nhdsWithin] with y hy htags h_g
  let r N:= address (C.S.a N) y
  let s N:= tag (C.S.a N) (r N)
  let Mk(t:ℕ×ℕ):= C.ensemble gr (fun i=>wrap (C.side t.1 t.2) (r t.1 i))
  have hg0 (Z:Next.UVStress.Bud C gr): Tendsto (fun t:ℕ×ℕ=>Mk t Z) 𝓛 (𝓝 (S.value gr y Z)):=by exact rounded C Z f 𝓛 hL he y h_g
  have hg:=tendsto_multi (fun i => C.book.Ref (gr i)) Mk (fun v=>S.value gr y v) hg0 (fun i=>(v i).2) (fun t i=>Y i t) hT
  obtain ⟨K,hK,hI,Ksub⟩:= exists_compact_subset hopen hy
  change ‖S.value gr y _‖ ≤ _
  refine le_of_tendsto hg.norm ?_
  have hmesh : ∀ᶠ i in f.fuse, s i.1 ∈ K ∧ b ≤ i.1:= by
     rw [Order.fused]; exact Eventually.of_forall fun _=> (f.mesh.cofinal.eventually ((chosen (S:=C.S) y).eventually (mem_interior_iff_mem_nhds.mp hI))).and (f.mesh.cofinal.eventually_ge_atTop b)
  have hper : ∀ᶠ t in f.fuse, ∀ x∈K, ∀ i j a, off C.S t.2 (distances x i j a) |distances x i j a|:= by rw [Order.fused]; filter_upwards [f.per.cofinal.eventually (Gaps.expand_equivalent C.S hK)] with p hp using Eventually.of_forall (fun _=>hp)
  filter_upwards [hw,(hmesh.and hper).filter_mono hL] with t ⟨ha,hf⟩ ⟨⟨hs,hb⟩,h_off⟩
  exact numeric_bound e C H hm hk hl hb x z (u t) patterns headroom side A B hB ha hf y htags (s t.1) rfl (Ksub hs) (h_off _ hs)
end YM.OPE.Coverage.Pass
