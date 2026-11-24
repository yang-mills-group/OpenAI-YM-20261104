import YM.AllOrder.Plateau.Div
import YM.AllOrder.Plateau.Reflex
import YM.AllOrder.Horizon.Files
/-!
# Plateau local bounds reserve on same Shape Fields before moving `β` curves
-/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Plateau.Line
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration PhysicalNext Repeat Height Song Geo RG.Shoot
open Push.Uniform Blaze Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Marlin Lantern Trio Roof Roost
open Shop Further.PhysicalPeriodLimitF933
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {X: Metals G} (D: Rolls X.p) (C : Targets X.p X.K) {P: Protection D}{i j : ℕ}
set_option quotPrecheck false
local notation "p"=> (X.p.profile j)
local notation "q"=> (X.p.profile i)
local notation "K"=> X.p.kernel
local notation "M" => X.O
local notation "O"=> X.oga
local notation "B"=> Pane.cloak D j
local notation "b" => Shop.parking (Shop.tall i) ((C j i).halo)
local notation "Ω" => D.L j
abbrev precinct (h:4≤j):= Plateau.Ticket (Mural.sheet X.p D h) (X.p.kernel) X.O p q B
abbrev Bank (h:4≤j):= Plateau.Folio (Mural.sheet X.p D h) (X.p.kernel) X.O X.oga p q B i
-- orientation multipliers. beyond weights.PHe. true mesh character call for K.
def laurels (x:ℝ):= betaF G x (D.L j) ^ (Shop.output 2 (2*Shop.edgeW i))
def breadth (x:ℝ):= let z:= Trio.base b (radiusB x); ∑ a:Stars, |Slide.ray a| *((2:ℝ)^((X.p.profile i).order) * (1+(z:ℝ))^((X.p.profile i).power*(X.p.profile i).order) * Boulevard.ticket ((X.p.profile i).order) (laurels D (j:=«j») (i:=i) x)) -- j shadow fix
local notation "τ"=> Plateau.Line.breadth D C (j:=j) (i:=i)
local notation "T"=> laurels D (i:=i) (j:=j)
abbrev sage (z:ℝ):= betaF G z Ω ^ Shop.output 2 (3*edgeW i)
lemma loud : Rate G (D.L j) (Shop.output 2 (2*Shop.edgeW i)) (τ):= by
 unfold breadth; dsimp only; apply Trio.sparks; intro l; let g:= (X.p.profile i).order; have ht := ((Trio.rows G (D.L j) b).2.2.1.uses); have hh :(Rate G Ω 0 (fun x=> (2:ℝ)^g*(1+(Trio.base b (radiusB x):ℝ))^((X.p.profile i).power*g))):= ((((Rate.const 1).add ht).pow _).mul_left _).weaken (by simp)
 exact (((hh.mul (((Rate.power (G:=G) (L:=Ω)).mul_left (g.factorial:ℝ)).mul_right _)).mul_left _).weaken (zero_add _).le)

def Plus (h:4≤j)(U:Bank (i:=i) D h)(x:ℝ) := (∀ k:ℕ,k≤ i→ slenderK (Mural.sheet X.p D h) (X.p.kernel) X.O X.oga p q B b U x ((X.p.profile i).order + i+3) k) ∧ Real.exp (Trio.stout q * coverTicket b) * τ x ≤ sage (i:=i) (j:=j) D x
lemma peak (hi:4≤ i)(hJ:4≤j) (hU:Nonempty (precinct D (i:=i) hJ))(hG:G.Simple) : ∃ U:Bank D (i:=i) hJ, ∀ᶠ u:ℝ in atTop, ∀ v:ℝ,u ≤ v → Plus D C hJ U v:= by
 let Z:=Mural.sheet X.p D hJ; obtain ⟨U⟩:=Plateau.Folio.ok Z (X.p.kernel) X.O X.oga p q B (X.p.has Z) (N:=i) hG (by omega) hU; have he x (hx:x∈Finset.range (i+1)):=Plateau.awning Z (X.p.kernel) X.O X.oga p q B b U (k:=x) (j:=(X.p.profile i).order+i+3) (Nat.le_of_lt_succ (mem_range.mp hx)) (by rw [mem_range] at hx; omega) (by omega) hG
 have ht:∀ᶠ t:ℝ in atTop,Plus D C hJ U t:= by
    filter_upwards [(eventually_all_finset (Finset.range (i+1))).mpr he, (Rate.mul_left (loud D C (j:=j) (i:=i)) (Real.exp (Trio.stout q* coverTicket b))) (Shop.output 2 (3*edgeW i)) (by unfold Shop.output; linarith [edge_pp i])] with t ht hζ; exact ⟨fun k hk=> ht k (mem_range.mpr (by omega)),(le_abs_self _).trans hζ⟩
 obtain ⟨x,hx⟩:=eventually_atTop.1 ht; exact ⟨U,eventually_atTop.2 ⟨x,fun u hu v hv=>hx _ (hu.trans hv)⟩⟩

def Walks (x:ℝ):Prop:= ∀ (_:4≤ i)(h:4≤j), Nonempty (precinct (i:=i) D h) → ∃ U:Bank (i:=i) D h, ∀ x'≥x, Plus D C h U x'
lemma timing (hG:G.Simple): ∀ᶠ t in atTop,Walks D C (i:=i) (j:=j) t:= by
 by_cases hi:4≤ i; swap; · exact Eventually.of_forall fun i H _=> (hi H).elim
 by_cases hj:4≤j; swap; · exact Eventually.of_forall fun k _ h => (hj h).elim
 by_cases hv: Nonempty (precinct (i:=i) D hj); swap; · exact Eventually.of_forall fun k _ _ h => (hv h).elim
 obtain ⟨U,H⟩:=peak D C hi hj hv hG; exact H.mono fun k hk _ _ _=>⟨U,hk⟩
local notation "F≀"=>Walks D C
def Reserve (Y:Delays P):Prop:= ∀ j i, StepStages j i → Walks D C (i:=i) (j:=j) (Y.betaEntry j)
lemma gift (V:Delays P)(hG:G.Simple): ∃ W:Delays P,DelayLe V W ∧ ∀ Y:Delays P,DelayLe W Y → Reserve D C Y:= by
 obtain ⟨x,-,hv,hV⟩:= collect_upper V.betaEntry _ (fun j=> eventually_transitions j _ _ (fun i hi => timing D C (i:=i) (j:=j) hG))
 refine ⟨{ V with betaEntry:=x},⟨hv,le_rfl,le_rfl,le_rfl⟩,fun W hW j i h hi hj hU=>?_⟩; exact hV j _ (hW.beta _) i h hi hj hU
end YM.AllOrder.Plateau.Line
