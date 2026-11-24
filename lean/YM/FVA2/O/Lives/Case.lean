import YM.FVA2.O.Lives.Win
/-!
# Banks for OPE use (continuum kernel)

`Bank`: combines `Warm`, the rank cut from `collect`, and `Solid`. Verify
operations for all real scales preserve the requisite `Bank` properties.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Lives
open MS Function Filter Set Finset MS.Plane MS.Koszul Flux MeasureTheory MS.Heat MS.Book Convolve Signal
open MS.Breeze MS.Latch MS.Native MS.Osc.Snap MS.Osc MS.Fiddle MS.Garment MS.Garment.Wick MS.Rock MS.Rock.Path MS.City MS.Rake MS.Tone Momentum MS.Landau Detect MS.Color Real
open Ward Job Wire
open scoped Topology ContDiff
variable {G:Gauge}{I E:Type}{F F' H H':Glade G I}{i:I}{s:ℝ}{a b c r:ℤ}
lemma W_cash (h:Warm F false)(f:I→ℂ): Warm (fun i=> f i • F i) false:=⟨ fun i t ht=>Lease.cash _ (h.cost i t ht), fun i u v=> continuous_const.mul (h.walk i u v) ⟩
structure Bank (F:Glade G I)(q:ℤ) : Prop where
    cross : Warm F false
    heat : collect F
    tone (i:I)(s:ℝ) : Solid false (F i s) q
lemma Bank.zero : Bank (0:Glade G I) a:= ⟨CabinF.warm0,collect_z,fun _ _=> solid_zero⟩
lemma Bank.add (h:Bank F a)(hp:Bank H a): Bank (F+H) a:= ⟨CabinF.warm_zip h.cross hp.cross, collect_p h.heat hp.heat, fun i s=> (h.tone i s).add (hp.tone i s) ⟩
lemma Bank.air (h:Bank F a)(f:I→ℝ): Bank (fun i=> (f i:ℂ) • F i) a := by
    obtain ⟨k,hk⟩:= h.heat; refine ⟨ W_cash h.cross _,⟨k, fun i t=> Limit.smul _ (hk i t) ⟩,fun i t=> (h.tone i t).scalar _⟩
lemma Bank.scale (h:Bank F a)(f:ℝ): Bank (f • F) a:= h.air fun _=>f
lemma Bank.neg (h:Bank F a): Bank (-F) a:= by simpa only [neg_one_smul] using h.scale (-1)
lemma Bank.sub (h:Bank F a)(hc:Bank H a): Bank (F-H) a:= by rw [sub_eq_add_neg]; exact h.add hc.neg
lemma Bank.all_fin (s:Finset E){f:E→Glade G I}(hp:∀ i∈s,Bank (f i) a): Bank (∑ i∈s,f i) a:= by classical induction s using Finset.induction_on with| empty=> simpa using Bank.zero| insert i s hi ih=> rw [Finset.sum_insert hi]; exact (hp i (by simp)).add ( ih fun j hj=> hp j (mem_insert_of_mem hj))
lemma Bank.invoice (h:Bank F a): F i s ∈ Wallet G:= Wallet.awake h.cross i s
lemma Bank.A (h:Bank F a): Bank ((both G I).P F) a:= ⟨ WH h.cross, gasP h.heat h.cross, fun i t=> sA ( h.tone i t) h.invoice⟩
lemma Bank.B (h: Bank F a): Bank ((both G I).J F) (a+1):= ⟨ WJ h.cross, gasJ h.heat h.cross, fun i t=> sB (h.tone i t) h.invoice⟩
lemma Bank.X (h:Bank F a)(hp:Bank H b): Bank ( (both G I).X F H ) (a+b):= ⟨ WX h.cross hp.cross, collect_tree (fun _=>lineA G) h.heat hp.heat, fun i t=> sAA (h.tone i t) (hp.tone i t) ⟩
lemma Bank.C (h:Bank F a)(hp:Bank H b): Bank ( (both G I).C F H ) (a+b+1):= ⟨ WB h.cross hp.cross, collect_tree (fun _=>lineB G) h.heat hp.heat, fun i t=> sAB (h.tone i t) (hp.tone i t)⟩
variable {Y X X' Y': T (Glade G I)}
abbrev Banks (F:T (Glade G I))(d:ℤ): Prop := ∀ n,Bank ( F n ) d
lemma Banks.Arbor (h:Banks X a)(hp:Banks Y b): Banks (pairW (both G I).X X Y) (a+b):= fun k=> Bank.all_fin (antidiagonal k) (fun i _=> (h i.1).X (hp i.2) )
lemma Banks.C (h:Banks X a)(hp:Banks Y b): Banks (pairW (both G I).C X Y) (a+b+1):= fun k=> Bank.all_fin (antidiagonal k) (fun i _=> (h i.1).C (hp i.2) )
lemma Banks.res (h:Banks X 0)(hp:Banks Y b): Banks ( (both G I).res X Y ) (b+1):= fun i=> (hp i|>.B).add ( (by simpa only [zero_add] using h.C hp i : Bank _ (b+1)) ) -- simplify
lemma Banks.lives (h:Banks X 0)(hp:Banks Y b): Banks ((both G I).lives X Y) b := fun i=> ( Bank.A (hp i) ).add ( (zero_add b) ▸ h.Arbor hp i )
lemma Velocity.add (h:Velocity F F')(hp:Velocity H H'): Velocity (F+H) ( F'+H'):= fun i t=> (h i t).add (hp i t)
lemma Velocity.scale (h:Velocity F F')(s:I→ℂ) : Velocity (fun i=>s i • F i) (fun i=> s i • F' i):= fun i t=> (h i t).scalar _
lemma Velocity.sub (h: Velocity F F')(hp:Velocity H H'): Velocity (F-H) (F'-H'):= by
    simp only [sub_eq_add_neg]; apply Velocity.add h; suffices he: Velocity (((-1):ℂ) • H) (((-1):ℂ) • H') by simpa only [neg_one_smul] using he
    exact hp.scale fun _=> (-1)
lemma Velocity.sum (s:Finset E){f f':E→ Glade G I}(h:∀ i∈s, Velocity (f i) (f' i)): Velocity (∑ i∈s,f i) (∑ i∈s,f' i):= by intro i t; simp_rw [Finset.sum_apply]; convert Zip.sum _ (F:=fun j=>f j i) (fun j hj=> h j hj i t) using 1; ext; rw [Finset.sum_apply]
lemma Velocity.J (h:Warm F false)(hp:Warm F' false)(he:Velocity F F'): Velocity ((both G I).J F) ((both G I).L F+(both G I).J F') := by
    rw [front G I,LinearMap.add_apply,LinearMap.add_apply,add_left_comm]; exact Velocity.add ( F':=Z G I F') ( fun i t=> ZQ _ (he i t) ) ( orbit_V h hp he realityB realityD line_jet ) -- line_jet ∀ argument order
lemma Velocity.C (h:Velocity F F')(he:Velocity H H'): Velocity ( (both G I).C F H ) ( (both G I).D F H+(both G I).C F' H + (both G I).C F H' ) := tree_velocity h he
lemma Velocity.arbor (h:∀ i,Velocity (X i) (X' i))(hp:∀ i,Velocity (Y i) (Y' i))(k:ℕ): Velocity (pairW (both G I).C X Y k) ((pairW (both G I).D X Y + pairW (both G I).C X' Y + pairW (both G I).C X Y') k) := by simp only [Pi.add_apply,paired,← Finset.sum_add_distrib]; exact Velocity.sum _ (fun i _=>(h i.1).C ( hp i.2 ))
end YM.FVA2.O.Lives
