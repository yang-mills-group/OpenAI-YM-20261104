import YM.WilsonCoeffUV.Marked.Bounds.Clearance
/-!
# Sequence logarithmic ideal on physical supports

High from WITH all terms and to reopening on allowed configs. Norms on
result even before omitting any first joins on allowed configurations.
 -/
set_option autoImplicit false
set_option maxHeartbeats 520000
noncomputable section
namespace YM.WilsonCoeffUV.Wheel.Mark
open Function PowerSeries Blue Mer Lattice RG Embroider Embroider.Canvas Soil Bank Laurent Cosmos Filter Gauge Power Matrix Precision Wilson Tree Exterior AnalyticNext.QuarticMatch.Sheets Bloch FreeResolvent Work.F08 Metric Shard Realm PathCost Real
open scoped Topology BigOperators
variable {c f:Side}{ι α U V t:Type}{J K I T:Finset ι}{D k K':ι→ℕ}{i j i' j' a e r h N n m b l:ℕ}{G:Gauge}{σ τ u g B C z ρ:ℝ}
variable [DecidableEq ι][Fintype ι]{E W U':Credit}{R:Realm G (e+1) E}{P:Outerm G D}

-- Positivity & log absorption
lemma gale_nn (G:Gauge)(D k K':ι→ℕ)(e:ℕ)(W U E:Credit)(h:1≤ z):0≤galeGate G D k K' e W U E z:=mul_nonneg (mul_nonneg (by norm_num) (zero_le_one.trans (Credit.purchase _ h))) (zero_le_one.trans (Credit.purchase _ h))
omit [DecidableEq ι] [Fintype ι] in
lemma penaltyBound (h:1≤z)(p:0≤ρ)(v:ℝ):0 ≤ penaltyB U' z ρ v:=mul_nonneg (div_nonneg p (mul_nonneg (by norm_num) (zero_le_one.trans (Credit.purchase _ h)))) (Real.exp_pos _).le
-- Wick recursion with ALL configs and full product before openings.
noncomputable def Gears (A:Levels G)(L:ChartRatio G)(K k:ι→ℕ)(N b i:ℕ) (Q:Outerm G D) : Outerm G D:= if _h:i<b then stout A L i N K k (Gears A L K k N b (i+1) Q) else Q
termination_by b-i
decreasing_by omega
omit [Fintype ι] in
lemma gearTop (A:Levels G)(L:ChartRatio G)(Q:Outerm G D) : Gears A L K' k N b b Q=Q:=by rw [Gears,dif_neg (lt_irrefl _)]
omit [Fintype ι] in
lemma gearUp (A:Levels G)(L:ChartRatio G)(Q:Outerm G D)(p:i<b): Gears A L K' k N b i Q= stout A L i N K' k (Gears A L K' k N b (i+1) Q):=by rw [Gears,dif_pos p]
omit [Fintype ι] in
lemma Cog (A:Levels G)(L:ChartRatio G)(bL:b≤N)(Q:Outerm G D)(q:Wellness k Q)(p:G.Simple)(v:LocalRatio L)(u:i≤ b): Wellness k (Gears A L K' k N b i Q):=by
    induction u using Nat.decreasingInduction with
    | self=> rw [gearTop]; exact q
    | of_succ i h ih=> rw [gearUp A L Q h]; exact Seating A L _ p v (lt_of_lt_of_le h bL) ih K'
omit [Fintype ι] in
lemma MeterC (A:Levels G)(L:ChartRatio G)(bL:b≤N)(Q: Outerm G D)(q: Wellness k Q)(p:G.Simple)(v:LocalRatio L)(u:i<b)(x:ι→ Cover): levelsO (Gears A L K' k N b i Q x)=margin A L i N K' k (Gears A L K' k N b (i+1) Q) x:=by
    rw [gearUp A L Q u]; exact Eq.symm (oneStep_log A L _ p v (lt_of_lt_of_le u bL) (Cog A L bL Q q p v u) K' x)

structure Borealis (R:Realm G (e+1) E)(D k K:ι→ℕ)(P:Outerm G D)(m N:ℕ)(W:Credit)(z:ℝ):Prop where
    head : Wellness k P
    field : ∀ S, 1 < S.card→ ∀ i,P i S=0
    main : R.anchor≤ m
    yell : R.y m≤ z
    sing i v : ∀ (u:m≤ i), ∀ _h:i≤ N, ∀ s:ι, shingled v {s} (Gears R.draws R.paid K k N N i P) e (R.mint i (main.trans u)).σ (W.buy (z+snowP R.draws.S m i))
-- core norm infinite m..N

theorem coruscate (h:Borealis R D k K' P m N W z)(b:Cloze D k R U')(v:galeGate G D k K' e W U' E z ≤ρ)(u:m ≤ i)(t:i≤N)(p:ι→Cover)(x:cleared R.draws.S m i ρ p J)(g:1<J.card)(a' : a≤e):
    let y:=snowP R.draws.S m i
    Wig Bank.terrain p (R.mint i (h.main.trans u)).σ (exp (-penaltyB U' z ρ y)) J ((Gears R.draws R.paid K' k N N i P p J).2 a r):=by
   let T:=R.draws.S; have hz:1≤ z:=(R.depth _ h.main).trans h.yell
   let Φ:=fun i=> Gears R.draws R.paid K' k N N i P
   induction t using Nat.decreasingInduction generalizing p J a r with
   | self=> intro y; rw [gearTop,h.field J g p]; exact Wig.zero.more (Real.exp_pos _).le
   | of_succ i hi ih=>
       intro y; rw [gearUp R.draws R.paid P hi]; apply freezing b h.main h.yell u ρ v _ x g
       let z':=snowP T m (i+1); let A:=W.buy (z+z'); have hs: m≤ i+1:=by omega
       have hA:1≤ A:= W.purchase (hz.trans (le_add_of_nonneg_right (sub_nonneg.mpr (scales _ hs))))
       have hp:Wellness k (Φ (i+1)):= Cog R.draws R.paid le_rfl P h.head R.hG R.green hi
       apply furnish b _ hp (h.main.trans u) hi p K' (zero_le_one.trans hA) _ a a' r
       intro w q S t j e' l
       have hy:=heldR R.draws p x t u w
       by_cases z:S=∅; · subst S; rw [hp.quiet' q]; simp only [Finset.card_empty,pow_zero]; exact Wig.zero.more zero_le_one
       by_cases he:1<S.card
       · have he' : exp (-penaltyB U' _ ρ z') ≤ 1:= Real.exp_le_one_iff.mpr (neg_nonpos.mpr (penaltyBound hz ((gale_nn G D k K' e W U' E hz).trans v) z'))
         exact (ih (a:=j) (r:=l) hs q hy he e').more (he'.trans (one_le_pow₀ hA))
       have hx : S.card=1:= Nat.le_antisymm (le_of_not_gt he) (Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr z))
       obtain ⟨s,rfl⟩:= Finset.card_eq_one.mp hx; exact h.sing (i+1) q hs hi s j e' l

-- input to a reconstructed close interval: drop ONLY prohibited square-mark configs in log. Their footprint
-- on all allowed full product tests remains identical. Equality doesn't cover evaluations probing
-- the forbidden region (even in an OPE computation needs separate support property).
def reserveGood (S:Schedule)(m i : ℕ)(ρ:ℝ)(P:Outerm G D) (p:ι→Cover)(J:Finset ι) : Era G (Pen D J) := open Classical in if cleared S m i ρ p J then P p J else 0
omit [DecidableEq ι] [Fintype ι] in
lemma reserveSpec (S:Schedule)(m i)(ρ:ℝ)(p:Wellness k P) : Wellness k (reserveGood S m i ρ P):=by
   refine ⟨fun x=>?_,fun h i'=>?_,fun x y q hx=>?_⟩
   · unfold reserveGood; split; exact p.quiet' _; rfl
   · unfold reserveGood; split; exact p.level' _ _; exact unstamped
   have hv {x y:ι→Cover}(p:cleared S m i ρ x q) (h:∀ i∈ q,x i=y i) : cleared S m i ρ y q:=by
       intro k e n t v; rw [←h k e, ←h n t]; exact p k e n t v
   unfold reserveGood; split
   next v=> rw [if_pos (hv v hx)]; exact p.filial _ _ _ hx
   next V=> rw [if_neg (fun p=>V (hv p fun i p=>(hx i p).symm))]
omit [Fintype ι] in
lemma reserveEligible (S:Schedule)(m i)(ρ:ℝ)(P:Outerm G D)(p:ι→Cover)(u:cleared S m i ρ p I):
    levelsO (reserveGood S m i ρ P p) I= levelsO (P p) I:= levels_g (fun _ x=> if_pos (show cleared S m i ρ p _ from fun i e z g=>u i (x e) z (x g)))

def outset (R:Realm G (e+1) E)(m N:ℕ)(ρ:ℝ)(k K:ι→ℕ)(P:Outerm G D):= reserveGood R.draws.S m m ρ (Gears R.draws R.paid K k N N m P)
theorem earn_cap (h:Borealis R D k K' P m N W z)(b:Cloze D k R U')(v:galeGate G D k K' e W U' E z ≤ρ)(u:m ≤ N) :
    ∀ p J,shingled p J (outset R m N ρ k K' P) e (R.mint m h.main).σ (W.buy z):=by
    let Y:= Gears R.draws R.paid K' k N N m P; let Q:= outset R m N ρ k K' P
    intro p J a e' r; have hz: 1≤z:=(R.depth m h.main).trans h.yell; have hA:1≤ W.buy z:=W.purchase hz
    unfold outset reserveGood; split
    next V=>
      by_cases g:J=∅; · subst J; rw [(Cog R.draws R.paid (K':=K') le_rfl P h.head R.hG R.green u).quiet' p]; simp only [Finset.card_empty,pow_zero]; exact Wig.zero.more zero_le_one
      by_cases p':1<J.card
      · exact (coruscate h b v le_rfl u p V p' e').more ((Real.exp_le_one_iff.mpr (neg_nonpos.mpr (penaltyBound hz ((gale_nn G D k K' e W U' E hz).trans v) _))).trans (one_le_pow₀ hA))
      obtain ⟨x,rfl⟩:=Finset.card_eq_one.mp (Nat.le_antisymm (by omega) (Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr g))); simpa only [snowP,sub_self, add_zero] using h.sing m p le_rfl u x a e' r
    exact Wig.zero.more (zero_le_one.trans (one_le_pow₀ hA))
end YM.WilsonCoeffUV.Wheel.Mark
