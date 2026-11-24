import YM.FVA2.O.Fusion.Logs
/-!
# Full multi-mark product (from the rephased connected kernels)

`plenum`: include *all* mark subsets. `plenum_R`: prove the entire
response equation, all formal orders.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Fuse
open MS Function Filter Set Finset MS.Plane MS.Koszul Flux MeasureTheory MS.Heat MS.Book Convolve Signal
open MS.Breeze MS.Latch MS.Native MS.Osc.Snap MS.Osc MS.Fiddle MS.Garment MS.Garment.Wick MS.Rock MS.Rock.Path MS.City MS.Rake MS.Tone Momentum MS.Landau Detect MS.Color Real
open Ward Job Wire MS.Local.Physical MS.Land Lives Puff Serve Rake.Geo Vane Actors
open scoped Topology ContDiff Interval
variable {G:Gauge} {I E W:Type}[LinearOrder W]{L: Planet G I}{B: Deck G}{K:Booked B}{M:MS_Data G K}{q:ℤ}{P:Geo I}{x:Position W I} {p a b:I→QP}{R:W→Rake.Label B}{X:Rake.Dance G I W}{S:Finset W}{n:ℕ}
omit [LinearOrder W] in
lemma unitB : Bank (hori G I).unit 0 := by
    constructor
    · have hp:= Wallet.cash (G:=G); refine ⟨?_, fun i t hx=> continuous_const ⟩; intro i t ht E _ _ w hw hu; let V:=Job.single (camp t); have h : Bound V (fun _=> fieldVal (coin (1:ℂ)) w) 1:= constant_at (show Latch.Lease false false (Job.single Unit) (fun _=>coin (A:= Lane4 G) (1:ℂ)) _ from hp) () V (fun _=>le_rfl) w hw hu; unfold Cape; simp only [Job.cw,one_zpow,Pi.one_apply,one_mul]; exact h
    · refine ⟨0,fun i t=>?_⟩; intro l hv; rcases l with _|_; simp at hv; rfl
    intro i t; constructor
    · exact fun l i k r _=> coin_symm (1:ℂ) (p:=field Landau.parity) l i k r
    · exact fun l _ hl=> Rails.coin _ l hl
    · intro l _ j; exact congr_fun (Mach.Safe.cpig (G:=G) (n:=0) _ j) l
    · intro w _; rcases w with _|_; exact (star_one _).symm; exact (star_zero _).symm
omit [LinearOrder W] in def spring (G:Gauge)(I:Type): Puff.Dynamics (hori G I) := {
    valid:=Velocity
    mono:=fun _ _ _=> hasDerivAt_const ..
    empty:= fun _ _ _=>hasDerivAt_const ..
    plus _ _ _ _ := Velocity.add
    price _ _ x y:= y.scale (fun _=>x)
    duop _ _ _ _ h hp:= dual h hp } -- def not lemma!
omit [LinearOrder W] in
lemma unitC : Banks (glaze G I).unit 0:= by intro i; change Bank (SplitP.refineV SplitP.nat (hori G I).unit i) _; unfold SplitP.refineV; split; exact unitB; exact Bank.zero
lemma chalk (hp:∀ s,Banks (X s) 0)(S:Finset W)(k:ℕ): Banks (((glaze G I).stack (SplitP.marked W)).power X k S) 0:= by
    induction k generalizing S with| zero=> unfold power Actors.stack; dsimp only; unfold SplitP.refineV; split; exact Fuse.unitC; exact fun _=> Bank.zero | succ k IH=>
    intro n; change Bank (SplitP.Lift _ (bond G I) X _ S n) _; rw [ SplitP.loan, Finset.sum_apply ]; exact Bank.all_fin _ (fun i _=> Serve.joins (hp _) ( IH i.2 ) n)
lemma cash_phase (F:Glade G I)(n:ℕ): Actors.phase n • F = ( (n.factorial:ℝ)⁻¹ ) • F:= by
    rw [show Actors.phase n=( ((n.factorial:ℝ)⁻¹ :ℝ) :ℂ) from (by simp [Actors.phase]) ]; rfl
abbrev Meal (F:Rake.Dance G I W):= Cheer (glaze G I) (SplitP.marked W) F
lemma eating (h:∀ s,Banks (X s) 0): Banks (Meal X S) 0:= by intro n; simp only [Meal,Cheer,cheers,wages,Finset.sum_apply,Pi.smul_apply,cash_phase]; exact Bank.all_fin _ (fun i _=> Bank.scale ( chalk h S i n ) _ )
abbrev plenum (x:Position W I)(X:Rake.Dance G I W):= Meal (untap x X)
lemma plenum_R (h:DOrd K P M R x X) (hx:∀ s k,Warm ( X s k ) false ) (s:Finset W): Response (plenum x X s) M P.η 0 := by
    let V:= team M P.η; let U:= untap x X; let T:= (spring G I).extrapolate SplitP.nat; let S:= SplitP.marked W; have he(i: Finset W): Banks (U i) 0:= fun k=> bankTilt (solitude h hx k); refine ⟨ eating he,?_⟩; have hz: U ∅=0:= by unfold U untap; rw [h.1,map_zero]
    have hp: (T.extrapolate S).valid U ((V.liftV S).move U+((2:ℂ)⁻¹) • S.Lift V.join U U):= by
        intro s; change T.valid (U s) (V.move ( U s ) + (2:ℂ)⁻¹ • (SplitP.marked W).Lift V.join U U s); rw [Stencil.halfB V.join U (fun i j=> V.rear (hedge (he i)) (hedge (he j))) hz]; exact rookie h hx
    exact Dynamics.expense T V S (fun i _=> hedge ( he i )) hz hp s
end YM.FVA2.O.Fuse
