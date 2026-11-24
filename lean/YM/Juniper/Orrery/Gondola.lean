import YM.Juniper.Orrery.Wallet
import YM.Juniper.Orrery.Poach
/-!
 # Prepare a Canister of E model at any circumference, with or without
 veil *kept along the TRUE advancement*. The PALE parts are only stand-
 in hard to pass through auxiliary emitters, chosen =0 and independent.
 We propagate from the SHORT part but compare to the full forecast. The
 Canister interface later also used in initializing at the bare top.
 -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Juniper.Orrery
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 PhysicalNext PhysicalNext.Repeat Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Further.PhysicalPeriodLimitF933 Macrame Deck Flare
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Marlin Lantern Trio Roof Roost Input Supply Slide
open Progress.DirectedRecipe UVExtension Oriel Dales Tour Height Averaging
open Whirl Ovens Ovens.Pipes Rack Voucher
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge} {c C:Side} {k n:ℕ} {ρ:ℝ} (P:BudgetPoint)
section preparation
-- request at any scale on arbitrary circumference accepted for the estimates (not the notional minimum physical regulator but enough for all asked auxiliary).
structure View (G:Gauge)(c:Side) where
   root : ℕ→RegularAddress c
   field : ℕ→ Config G c→ℝ

def stampC (V:View G c) : Activities G c:= { Pane.pale c G with E:=V.field, reg:= V.root }
abbrev pod (V:View G c):= prune P.B (stampC V)
structure Canister (G:Gauge)(P:BudgetPoint) (δ χ:ℝ) where
   prior (n:Side):View G n
   windows (n:Side) : ℕ→Finset ℕ
   active (n:Side) (hi:Margin P n) : ∀ i,(pod P (prior n)).E i≠0 → ∀ᶠ j in atTop,i∈windows n j
   access (n:Side)(hi:Margin P n) : ∀ j i,i∈ windows n j → ShortF P.B ((stampC (prior n)).reg i)
   projects (c C:Side)(k:ℕ)(hC:C.val=c.val*k)(hv:Margin P c): ∀ n:ℕ, ∃ p:ℕ→ℕ, Leaves hC p (prior C).root (prior C).field (prior c).root (prior c).field (windows C n) (windows c n)
   -- Imports E only. Absolute positions include pre-required & canonical samemask. δ and χ for FULL un-erased.
   earns (n:Side)(hp:Margin P n): (stampC (prior n)).Valid P δ 0
   erases (n:Side)(hp:Margin P n) : Payment P (prior n).root ((stampC (prior n)).E-(pod P (prior n)).E) χ
variable {χ δ:ℝ}(T: Canister G P δ χ)
include T
lemma frames (h:Margin P c): (pod P (T.prior c)).Valid P δ 0:= pruned (T.earns _ h)
end preparation
section postC
variable (A: Curtain G c) (S:PathData G)(t:Clip)(α Δ:ℝ)
local notation "B"=> P.B
local notation "A₀"=> Collection.fill A.book S t P A.stamp α Δ
local notation "X₀"=> Collection.shelves A.book S P
local notation "Y"=> stampC (View.mk ((X₀).reg) ((A₀).regular))
noncomputable def posted : View G c := ⟨(X₀).reg,(Collection.fill A.book S t P A.stamp α (Averaging.delta (A.book.read A.stamp))).regular⟩
local notation "v"=> Pane.pale c G
local notation "V"=> pod P (posted P A S t α)
local notation "Z"=> stampC (posted P A S t α)
local notation "W"=> Listing.mk A.book.reg ((v).forced) -- parsed
local notation "K"=> Collection.Source.mk A.stamp.logRead ((v).K)
local notation "v*"=> (W|>.read K)
local notation "J"=> numbering (Collection.EKey c)
def places (P:BudgetPoint)(A:Curtain G c)(S:PathData G)(j:ℕ):= (visiting P S A j).map (numbering (Collection.EKey c)).symm.toEmbedding
variable {η a b w:ℝ} (h:A.TidyC P P.B ρ)
include h
set_option maxRecDepth 6000
private lemma pricedC : Collection.Local W P K ρ 0:= by
    let p:= Pane.whey c G P; obtain ⟨f,hf,hb⟩:=h.income
    refine ⟨fun i=> (hb i).1, ⟨p.forced.sym,p.forced.symtest,p.forced.meas,p.forced.meas_test,p.forced.reads,p.forced.reads_test,p.forced.permit⟩,fun s u=> ?_,⟨f,fun i=> (hb i).2,hf⟩,?_⟩
    · obtain ⟨q,hq,hδ,hx⟩:=h.moves s u; let y:= (p.moves s u|>.some)
      exact ⟨⟨q,y.kp,hq,hδ,y.forced_support,y.forced_inventory,y.forced_tests,hx,y.valuesK⟩⟩
    refine ⟨0,fun i=>⟨le_rfl,fun U=> by change ‖(0:ℝ)‖≤ 0; rw [norm_zero]⟩,fun i=>?_⟩
    simp only [Pi.zero_apply,zero_mul, ite_self]; simp [SumBudget] -- unfold Hit? definition
variable (hc:S.Bounds t a b w) (he:WilsonStartup.Decent t P)(hW:Geo.Width P t a)(hG:G.Simple) (hm:Margin P c)
local notation "Δ*"=> (Averaging.delta (A.book.read A.stamp))
local notation "δ!"=> regularNeed G P t a b α ρ
local notation "K'"=> (Collection.fill W S t P K α Δ*)
local notation "C₀"=> (Collection.shelves W S P)
include h hc he hW hG hm
lemma validPost : (stampC (posted P A S t α)).Valid P (regularNeed G P t a b α ρ) 0:= by
    have hA:= Orrery.pricedC P A h; have hp:= hA.fittings hG hc he (by unfold Margin at hm; omega : 20<c.val) α (Averaging.delta (A.book.read A.stamp)); have hk: Δ*=Averaging.delta v*:= rfl -- id of forecast in this arrangement before purity
    obtain ⟨f,hf,hF⟩:= hA.cheap
    have hv : ((C₀).pours (K'))=(Z):=rfl
    rw [← hv]; refine ⟨hp.regular,hp.support,hp.moves, ?_, ?_⟩ -- fields inspect
    · have he':= hA.projects; have h' : P.threshold^2*|Δ*|≤ ρ := by rw [hk]; exact delta_bound hG he'
      have hg (i : EKey c):=Collection.Local.quote_regular hG hc he α Δ* hf hA.smooth i; have hy:= Collection.Local.quote_family hc he hW α Δ* hf hF h' |>.1
      exact ⟨_,fun i=> hg (numbering _ i),fun i=>Cost.equiv (numbering _) (hy i)⟩
    exact (Pane.whey c G P|>.boundK)
omit hG hm hW he hc
include P
omit h
variable (n:ℕ)
omit P in
private lemma present_ever {Y₀:Type} (p:ℕ≃Y₀)(j:Y₀) : ∀ᶠ n in atTop,j∈(range n).map p.toEmbedding:= by
    filter_upwards [eventually_gt_atTop (p.symm j)] with n hn using (mem_map.mpr ⟨p.symm j,mem_range.mpr hn,p.apply_symm_apply j⟩)
include h he
lemma active_post (i:ℕ)(hi:(V).E i≠0) : ∀ᶠ j in atTop,i∈ places P A S j:= by
    obtain ⟨i,rfl⟩:=((J).symm.surjective i)
    change (if ShortF B ((X₀).reg ((J).symm i)) then (archive A.book S t A.stamp α Δ*) ((J) ((J).symm i)) else 0) ≠ _ at hi; rw [Equiv.apply_symm_apply] at hi; split at hi; swap; · contradiction
    rename_i hQ; change ShortF B (incoming A.book S P (J ((J).symm i))) at hQ; rw [Equiv.apply_symm_apply] at hQ
    suffices hg: ∀ᶠ j in atTop,i∈ visiting P S A j by exact hg.mono (fun i hu=> mem_map_of_mem ((J).symm.toEmbedding) hu)
    rcases i with i|i|i
    · apply Eventually.of_forall; intro j; refine (frame_iff P S A j h he.radius i).2 (A.truncation i ?_); intro hx
      change Residual.rebate _ (A.stamp.logRead i) ≠ _ at hi; rw [hx] at hi; apply hi; let f:= Residual.label_sub (A.book.reg i) (0:Config G c→ℝ) 0 0 P (show P.Regular (A.book.reg i).support (0:Config G c→ℝ) from unspent ..) (unspent ..) |>.1; simpa only [sub_self] using f -- f let proof?
    · exact (present_ever (numbering _) i.2).mono (fun j hj=> mem_filter.mpr ⟨inr_mem_disjSum.mpr (inl_mem_disjSum.mpr (mem_product.mpr ⟨mem_univ _,hj⟩)),hQ⟩)
    exact (present_ever (numbering _) i.2).mono (fun j hj=> mem_filter.mpr ⟨inr_mem_disjSum.mpr (inr_mem_disjSum.mpr (mem_product.mpr ⟨mem_univ _,hj⟩)),hQ⟩)
omit h he
lemma applause (j:ℕ) (i:ℕ) (hi:i∈places P A S j): ShortF B ((stampC (posted P A S t α)).reg i) := by
   obtain ⟨k,hk,rfl⟩:=mem_map.mp hi; change ShortF B (incoming A.book S P (J ((J).symm k))); rw [Equiv.apply_symm_apply]; exact (mem_filter.mp hk).2
end postC
end YM.Juniper.Orrery
