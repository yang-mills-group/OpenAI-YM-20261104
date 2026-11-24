import YM.Juniper.Flare.Signs
import YM.Juniper.Voucher.Veer
/-!
 # Periodic MODEL terms for matching **at output** of local E step

 Later will use these stencils with the true shot query \& painting
 costs. For now handle the tax needed to keep any such stencils (e.g.
 formal output, in THEIR OWN support addresses, no common rep assumed yet)
 as the symbol part. Attach its l-roots and all old predicates. This is what
 makes the future operations with arbitrary templates and support budgets
 compatible with stability *after* assembly.
 -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Juniper.Flare
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 PhysicalNext PhysicalNext.Repeat Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March Captain
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Roof Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Marlin Lantern Trio Rain Roost
open Progress.DirectedRecipe Time Refrain Bright
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {X:Metals G} {c : Side} {i j k w D : ℕ}
    {B: BudgetPoint}
variable {a b :ℝ}
-- *finite truncated/rend* stencil. independent of the FG choices. orientations
-- don't need to impose on neighbor *index* bij across periods, only on its
-- ordinary kernel v.Total. Within period need Pack currencies at
-- per-index horizon. HARD names of Canvas not used! future pad on actual.
structure Curtain (G:Gauge)(c:Side) where
    book : Listing G c
    stamp : Collection.Source G c
    sequence : Finset ℕ
    truncation : ∀ i, stamp.logRead i ≠ 0 → i∈ sequence
variable (T:Curtain G c)
local notation "A" => (T.book.read T.stamp)
local notation "F" => T.stamp.logRead
namespace Curtain
-- Glued at coarse scale output ONLY. Introduce planar.UA constructor later
structure TidyC (P:BudgetPoint)(l:ℕ)(d:ℝ):Prop where
    frames : ∀ i∈ T.sequence,(T.book.reg i).support ⊆ neighbors l (T.book.reg i).site
    moves : ∀ (t:Signed)(i:Site c),∃ b: Equiv.Perm ℕ,Voucher.EPerm T.book T.stamp t i b
    income : Meadow.Budget P T.book.reg T.stamp.logRead d

def billed (i:Site c):= T.sequence.filter fun j=> (T.book.reg j).site=i
def root (i:Site c) : Config G c →ℝ:= ∑ j∈ billed T i, T.stamp.logRead j
def maskedRoot (T:Curtain G c)(B:BudgetPoint)(i:Site c) : Config G c→ℝ:= fun V=> ∑ j∈ billed T i, (T.book.read T.stamp|>.regularOccurrence B j V)
lemma liberal (X:Config G c): (A).additive B X=∑ i:Site c,T.maskedRoot B i X:= by
    let u j := (A).regularOccurrence B j X; let D:= T.sequence; unfold Activities.additive; rw [tsum_eq_sum (s:= D) (f:=u) ?_]; swap
    · intro b hb; have hh:= not_ne_iff.mp (mt (T.truncation b) hb); unfold u; change masked _ _ (F b) X=0; rw [hh]; simp [masked]
    unfold maskedRoot billed; simp_rw [Finset.sum_filter]; rw [Finset.sum_comm]; exact Finset.sum_congr rfl (fun i hi=> by simp [u]) -- check label binder
lemma amount (j: Site c) (X:Config G c): (T.root j) X=∑ i∈ billed T j,F i X:= Finset.sum_apply ..
variable {T}
variable {p: ℕ}(h:TidyC T B p a)
include h
private lemma locally_here (i:Site c)(j:ℕ)(hj:j∈ billed T i) : (T.book.reg j).support ⊆ neighbors p i:= (mem_filter.mp hj).2 ▸ h.frames j ((mem_filter.mp hj).1)
lemma masked_root (i: Site c)(V:Config G c)(he:Healthy B.threshold (neighbors p i) V): T.maskedRoot B i V=T.root i V := by
    rw [amount]; exact Finset.sum_congr rfl (fun j hj=> masked_eq _ _ _ _ (he.mono_left (locally_here h i j hj)))
lemma pose (i: Site c): B.Regular (neighbors p i) (T.root i):=
    Meadow.regularA _ fun j hj=> CouplingShape.reg_extend (((h.income).choose_spec.2 j).1) (locally_here h i j hj)
lemma shape (i: Site c): Tidy B (neighbors p i) (T.maskedRoot B i):=
    tidy_sum _ _ _ _ fun j hj=> tidy_mask _ ((h.income.choose_spec.2 j).1) (locally_here h i j hj)
lemma life (i:Site c)(V:Config G c) : ‖T.maskedRoot B i V‖ ≤ a:= by
    obtain ⟨f,hP,hF⟩:=h.income; have hp(j):0 ≤ f j:= (hF j|>.2.1); refine (norm_sum_le ..).trans ((sum_le_sum (g:=fun j=> if (T.book.reg j).site=i then f j*Real.exp (preExponent B * coverNumber B.B (T.book.reg j).support) else 0) ?_).trans (budget_sum (hP i) (T.billed i)))
    intro j hj; rw [if_pos ((mem_filter.mp hj).2)]
    exact (CouplingShape.mask_cost ((hF j).2) V).trans (le_mul_of_one_le_right (hp j) (Real.one_le_exp (mul_nonneg (Song.headline B|>.exponent_pos.le) (Nat.cast_nonneg _))))
lemma primeC (i:Site c)(V:Config G c)(hv:flags B.threshold V=∅): ‖T.root i V‖ ≤ a:= by
    rw [← masked_root h _ _ (show Healthy B.threshold (neighbors p i) V from by unfold Healthy; rw [hv]; simp)]; exact life h i V
omit h in
lemma naturalC (i:Site c)(V:Config G c) : HasSum (fun j=> if (T.book.reg j).site=i then T.stamp.logRead j V else 0) (T.root i V):= by
    rw [amount]; let f j:= if (T.book.reg j).site=i then T.stamp.logRead j V else 0; let b:= billed T i; have he : ∀ j, j∉ b → f j=0:= by
      intro j hj; unfold f; split; next hz=> rw [not_ne_iff.mp (mt (T.truncation j) (fun he=> hj (mem_filter.mpr ⟨he,hz⟩)))]; rfl
      exact rfl
    have hg : ∑ i∈ b,f i =_ := sum_congr (g:=fun j=> T.stamp.logRead j V) rfl fun i hi=> if_pos (mem_filter.mp hi).2
    rw [show ∑ j∈ billed T i,T.stamp.logRead j V=∑ j∈ b,f j from hg.symm]; apply hasSum_sum_of_ne_finset_zero he
lemma mirrors : Mirrors T.root:= by
    intro i s b V; let t:=Lattice.affine s b i; obtain ⟨q,hv,hm,hP⟩:= h.moves s b; let v:=fun j=> if (T.book.reg j).site=t then F j V else 0
    have hv':HasSum (fun i=>v (q i)) (T.root t V):= (Equiv.hasSum_iff (f:=v) q) |>.2 (naturalC (T:=T) t V)
    have hi : Injective (Lattice.affine s b):= (Push.Local.turnSites s b).injective
    refine (naturalC (T:=T) i (pull s b V)).unique (hv'.congr_fun fun j=>?_)
    unfold v; rw [hv,hP]; by_cases he:(T.book.reg j).site=i; · rw [if_pos he,he, if_pos (show affine s b i=t from rfl)] -- check syntax
    rw [if_neg he, if_neg (fun hEq=> he (hi hEq))]

lemma additive_auth (i: Seat c) (V:Config G c): (A).additive B (i.view V)=(A).additive B V:= by
    obtain ⟨p,hq,hk,he⟩:=h.moves i.1 i.2
    let f j:= (A).regularOccurrence B j V
    unfold Activities.additive; rw [← p.tsum_eq f]; exact tsum_congr (fun j=> by
       change masked _ _ (F j) (i.view V)= masked _ _ (F (p j)) V; rw [funext (he j),show ((A).reg (p j)).support=i.spread _ from hk j]; exact (congr_fun (Seat.distribute (x:=i) ..) V).symm) -- «x» global not here
end Curtain
end YM.Juniper.Flare
