import YM.Juniper.Voucher.Bundle
import YM.Juniper.Voucher.Pole
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Juniper.Voucher
open UVExtension
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open PhysicalNext PhysicalNext.Repeat
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Marlin Lantern Trio Roof Roost
open Progress.DirectedRecipe Time Rain
open Wick Lamppost YM.UVExtension.Concert
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open Guild Tabernacle
open Whirl PhysicalNext.Repeat.Graces
open Oriel Charted Dales Tour
open Refrain Marlin
-- estimate lifted to alternate pre projection seats. support pays. perm oriented. No modeling selection based on actual; hard legitimately kept.
variable {G:Gauge}{c:Side}{P:BudgetPoint}(W: Listing G c)
    (h: Collection.Source G c)(p:ℕ)(v : Trio.Offer G c) {a b δ:ℝ}
local notation "Z"=> pluck P (lodge W 0 p)
local notation "V"=> poursP P (lodge W 0 p) (bison h 0 v)
local notation "H"=> Marlin.leanU c
def overlay (x: Collection.Source G c) : Collection.Source G c := ⟨(bison x 0 (0:Trio.Offer G c)).regular,(V).hardRead⟩ -- P implicit?
lemma overlay_std (k:ℕ) (x:Collection.Source G c)(X:Listing G c): (overlay W h p v x (P:=P)).logRead = (overlay X x k v x (P:=P)).logRead:=rfl
local notation "ξ"=> overlay W h p v (P:=P)
-- update P keys static still tension.
lemma blanko (Y:Type) (M : Y→RegularAddress c): Meadow.Budget P M (0:Y→ Config G c→ℝ) 0:= by
    refine ⟨fun _=>0,fun i=>?_,fun i=> ⟨CouplingShape.reg_const _,VerifiedReset.sup_le (CouplingShape.sup_const _) (le_of_eq abs_zero)⟩⟩; simp [SumBudget]
omit P in
lemma nothing (i:Marlin.Door c): choir (0: Offer G c) i=0:=by simp [choir]
variable (x : Collection.Source G c)
lemma budgetH (hE: Meadow.Budget P W.reg x.logRead a): Meadow.Budget P (Z).reg (overlay (P:=P) W h p v x).logRead a:=by
   simpa only [mul_zero,add_zero] using! Marlin.reg_bison W 0 p x 0 (0:Trio.Offer G c) hE (blanko (P:=P) (G:=G) _ _)
lemma budgetSub (he: Meadow.Budget P W.reg (h-x).logRead b): Meadow.Budget P (Z).reg (((V)-ξ x).logRead) b:= by
    have hx: ((V)-ξ x).logRead=(ξ (h-x)).logRead:= by
       ext i u; let T:=choir (0:Offer G c); change Sum.elim h.logRead T (H i) u-Sum.elim x.logRead T (H i) u=(Sum.elim (h.logRead-x.logRead) T (H i)) u; cases H i; rfl; simp only [Sum.elim_inr,sub_self,T,nothing,Pi.zero_apply]
    rw [hx]; exact budgetH W h p v (h-x) he
open Averaging
lemma proj_blank (p':RegularAddress c) (B':BudgetPoint): projection p' (0:Config G c→ℝ) axes01 axes01=0:= by
   let Y':= (0:Config G c→ℝ); have hh:B'.Regular p'.support Y':= CouplingShape.reg_const _
   have he:= projection_sub p' hh hh axes01 axes01; rwa [sub_self,sub_self] at he
lemma billŌ (hg : Meadow.Budget P W.reg x.logRead δ)(hG:G.Simple): Averaging.delta ((Z).read (ξ x))= Averaging.delta (W.read x):= by -- tsum sum 0 requires Summable!
   have hp:= merchant hg; have he:= Yard.projects_ledger hp.1 hp.2
   let f:= Averaging.censusAt (W.read x) 0 axes01 axes01; let g(z:Civ c):= Sum.elim f 0 z; have he (i:ℕ):censusAt ((Z).read (ξ x)) 0 axes01 axes01 i=g (H i):= by
      unfold censusAt; change (if (Sum.elim W.reg (sea 0) (H i)).site=0 then projection (Sum.elim _ _ (H i)) (Sum.elim x.logRead (choir (0: Offer G c)) (H i)) axes01 axes01 else 0)=_; cases H i; exact rfl; next=> simp only [Sum.elim_inr,g,nothing,proj_blank (p':=_) P,ite_self,Pi.zero_apply]
   unfold Averaging.delta Averaging.total; simp_rw [he]; rw [Equiv.tsum_eq,Summable.tsum_sum (f:=g) (show Summable f from (Yard.projects_ledger (P:=W) hp.1 hp.2).seriesAt hG ..) Summable.of_finite]; simp only [g,Sum.elim_inl,Sum.elim_inr,Pi.zero_apply,tsum_zero,add_zero]; rfl

-- co-orientation (EP map only; choose KP post ANY Movement satisfying Lore), keep physical K plucked.
variable {X:Listing G c}{u y:Collection.Source G c} {s: Signed}{i:Site c}
def markPerm (π : Equiv.Perm ℕ)(s:Signed)(i:Site c): Equiv.Perm ℕ:= congo (Marlin.leanU c) (Marlin.reel s i π)
lemma focused (g:Offer G c) {w : ℕ}{π:Equiv.Perm ℕ} (u:Collection.Source G c)(hp:EPerm W x s i π): EPerm (pluck P (lodge W p w)) {u with logRead:= (bison x g v).regular} s i (markPerm π s i):= by
   let p':=markPerm π s i; let e(z:Civ c):= Marlin.reel s i π z; let T:= Sum.elim W.reg (sea p); let f:= Sum.elim x.logRead (choir g)
   have hh j:(T (e j)).site=Lattice.affine s i (T j).site∧ (T (e j)).support=(T j).support.image (Lattice.affine s i)∧f (e j)=f j∘pull s i:= by
      rcases j with j|j; · exact ⟨hp.1 _,hp.2.1 _,funext (hp.2.2 j)⟩
      exact Song.spirit (leap p) g s i j
   have hx j:H (p' j)= e (H j):= Refrain.perch ..
   refine ⟨fun j=> ?_, fun j=> ?_, fun j q=>?_⟩
   · exact (show (T (H (p' j))).site = _ from (hx j).symm ▸ (hh (H j)).1)
   · exact (show (T (H (p' j))).support=_ from (hx j).symm ▸ (hh (H j)).2.1)
   exact (show f (H (p' j)) q=_ from (hx j).symm ▸ congr_fun (hh (H j)).2.2 q) -- edit

-- recombine E permutations freely after pluck. hard family movement required only for SAME hardRead.
lemma join_moves {π:Equiv.Perm ℕ} (hv:EPerm X y s i π)(he:y.hardRead=u.hardRead) (hp:(X.read u).Moves s i): ∃ F : (X.read y).Moves s i,F.ep=π ∧ F.kp=hp.kp:= by
   refine ⟨⟨π,hp.kp,hv.1,hv.2.1,hp.forced_support,hp.forced_inventory,hp.forced_tests,hv.2.2,fun i x=>?_⟩,rfl,rfl⟩; change y.hardRead _ _= y.hardRead _ _; rw [he]; exact hp.valuesK i x
abbrev void (G:Gauge) (c:Side): Collection.Source G c:= ⟨0,0⟩
local notation "U"=> void G c
lemma project_cap {Y:Listing G c}(hg : Meadow.Budget P Y.reg y.logRead δ)(hG:G.Simple): Averaging.delta ((package W X Y).read (stack x U y))=delta (Y.read y):= by
   have hp:=merchant hg; let f:= Averaging.censusAt (Y.read y) 0 axes01 axes01; let g(z:ℕ⊕ℕ):= Sum.elim (0:ℕ→ℝ) f z; let h:=numbering (ℕ⊕ℕ)
   have hu i: censusAt ((package W X Y).read (stack x (U) y)) 0 axes01 axes01 i=g (h i):= by
      unfold censusAt; change (if (Sum.elim X.reg Y.reg (h i)).site=0 then projection _ (Sum.elim (fun _=>0) y.logRead (h i)) axes01 axes01 else 0)=_
      -- change projection label
      change (if (Sum.elim X.reg Y.reg (h i)).site=0 then projection (Sum.elim X.reg Y.reg (h i)) _ axes01 axes01 else 0)=_
      cases (h i); next j=> simp only [Sum.elim_inl,g,proj_blank (p':=_) P,ite_self,Pi.zero_apply]
      next=> rfl
   unfold Averaging.delta Averaging.total; simp_rw [hu]; rw [Equiv.tsum_eq,Summable.tsum_sum (f:=g) summable_zero (show Summable f from (Yard.projects_ledger (P:=Y) hp.1 hp.2).seriesAt hG ..)]; simp only [g,Sum.elim_inl,Sum.elim_inr,Pi.zero_apply,tsum_zero,zero_add]; rfl
lemma leanBudget {A B:Listing G c} {u y u':Collection.Source G c}(h:Meadow.Budget P A.reg u.logRead a)(he:Meadow.Budget P B.reg (y-u').logRead b):
    Meadow.Budget P (package W A B).reg ((stack x u y - stack x (U) u').logRead) (a+b):= by
   rw [show (stack x u y-stack x U u').logRead=(stack x u (y-u')).logRead from funext fun k=>?_]; swap
   · change Sum.elim u.logRead y.logRead (numbering _ k)-Sum.elim (0:ℕ → Config G c→ℝ) u'.logRead (numbering _ k)=Sum.elim u.logRead (y.logRead-u'.logRead) (numbering _ k); cases numbering (ℕ⊕ℕ) k
     · simp
     rfl
   exact payroll_pack W h he

variable {b':Site c}
lemma void_perm (π:Equiv.Perm ℕ)(hx:EPerm W x s b' π): EPerm W (U) s b' π:=⟨hx.1,hx.2.1,fun _ _=>rfl⟩
end YM.Juniper.Voucher
