import YM.RGComparison01.Library

/-!
 # Finitely many shelves, charging lifts to readonly author

 Entry from tagged masked partners on each comparable pair primitive.
 `Visible` on each R with SAME β. Provides the actual auxiliary ghost
 tickets from the physical support. -/

set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01.Library
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter
open PhysicalNext PhysicalNext.Repeat Deck Stellar Mint Greenbelt Boulevard Trio
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Extra.Iteration Song Refrain Reserves OmitClusters
open Divides Input Org Supply PriceCompiler Next.Scheduling Progress.DirectedRecipe Time Opera
open RG.Supply RG.Shoot Push.Uniform Sienna Pane
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {X : Metals G} {D : Rolls X.p} {A : Alloy X D} (F : Roost.Factor A)
variable {c f C F' : Side} {m n N k r M : ℕ} {β : ℝ}
variable (h : f.val=c.val*(A.B.a.S.block m).val) (H : F'.val=C.val*(A.B.a.S.block m).val)
    {R: RG.Rep G f} {R' : RG.Rep G F'}
    (I : Boulevard.Chartlet F.shape A N m h R) (I' : Boulevard.Chartlet F.shape A N m H R')
local notation "J" => (A.B.a.clock.J (m+1))
local notation "E" => (A.B.a.clock.J m)
local notation "B" => radiusB (A.B.a.clock.hatBeta m)
local notation "Q" => F.shape
local notation "O" => Chi.canonical
local notation "p" => A.B.a.budget m
local notation "Y" => A.B.a.budget (m+1)
local notation "γ" => A.B.kin.alpha N m
set_option quotPrecheck false
local notation "t" => A.B.a.clock.hatBeta m
variable (Z : Ribbon R n) (Z' : Ribbon R' n)

abbrev pitch (A : Alloy X D) (m:ℕ) := 100*(1+radiusB (A.B.a.clock.hatBeta m))

/-- use render service here. Old K and scalar at virtual product sides unobserved.
 Includes real R and solitary auxiliaries. -/
structure Visible (A : Alloy X D) (m N:ℕ) {c f:Side} (h:f.val=c.val*(A.B.a.S.block m).val)
    (R : RG.Rep G f) (β:ℝ) : Prop where
  leg : R.path= A.B.kin.path N (m+1)
  clips : R.clip = (A.B.a.params (m+1)).clip
  home : R.p=A.B.a.budget (m+1)
  earns : R.activities.Valid R.p (A.B.a.clock.allowance (m+1)) (A.B.a.clock.forcedAllowance (m+1))
  holds : R.beta=β
  site : pitch A m ≤ c.val

section afford
lemma original (hm:m<N) (he:Library.pitch A m ≤ c.val) (hβ:β∈band A.B.a (m+1)) :
    ∃ H: Boulevard.Chartlet F.shape A N m h (virgin (orchestra A N h) Y β), SeekR F.shape A N m h H :=
  Pane.affords A N h hm he F.shape F.pledging.conducts.income.grow.1 F.pledging.conducts.full hβ
lemma framed (hm:m<N) (hv:Visible A m N h R β) (hβ:β∈ band A.B.a (m+1)) :
    ∃ H: Boulevard.Chartlet F.shape A N m h R, SeekR F.shape A N m h H := by
  have he := Pane.ingots A N h hm hv.site hβ
  have hZ : betaF G t (panel A m h).patch.L = A.B.a.clock.hatBeta (m+1):= Eq.symm (Application.clock_next A.B.a m 0)
  have hp : Intake (asks A m) (orchestra A N h) t R := by
    have hP : incomingE G (panel A m h).patch.L t = A.B.a.clock.allowance (m+1):= by unfold incomingE; rw [hZ]; rfl
    have ha : incomingK G (panel A m h).patch.L t = A.B.a.clock.forcedAllowance (m+1):= by unfold incomingK Delay.fineMonitor; rw [hZ]; rfl
    have hr := hv.earns; rw [← hP,← ha] at hr
    refine ⟨he.ready,⟨hv.leg,hv.clips,by rw [hv.home]; exact he.received.3⟩, ⟨?_,hr⟩,?_,he.height,?_,?_⟩
    · rw [hv.leg,hv.clips]; exact he.cap.paths
    · rw [hv.home]; exact he.exponent
    · rw [hv.home]; exact he.sizes
    rw [hv.holds]; exact he.window
  exact ((F.shape.consumes _ _ (step_paid A.B.a m)).2.2.2 t ((F.pledging.conducts.income.grow.1 _).trans (A.B.valid.pays m))).2 _ _ _ _ (Pane.accepts A N h hm hv.site)|>.2 (Pane.ovation A N h hm F.pledging.conducts.full) _ hp
end afford

local notation "Zm" => deck c C
local notation "Zc" => (deck c C)*(A.B.a.S.block m)

-- primitive match for a PAIR. does not require additional vertices to
-- constructively compare; enough product ghost with agreed maps on each pair.
def Permit (A : Alloy X D) {c f C F':Side} (N m:ℕ) (h : f.val=c.val*(A.B.a.S.block m).val) (H : F'.val=C.val*(A.B.a.S.block m).val)
    {R:RG.Rep G f} {R':RG.Rep G F'} (β:ℝ) (Z : Ribbon R n) (Z' : Ribbon R' n) :=
    let C' := (deck c C)*(A.B.a.S.block m)
    ∃ (R'' : RG.Rep G C') (Z'' : Ribbon R'' n), Visible A m N (c:=deck c C) rfl R'' β ∧
      (∃ θ : Z''.Node→Z.Node,Ribbon.Drops Z Z'' (Deck.fineP (P:= (A.B.a.clock.op m 0).patch) h (show C'.val=(deck c C).val*(A.B.a.S.block m).val from rfl) (show (deck c C).val=c.val*C.val from rfl)) θ) ∧
      (∃ θ' : Z''.Node→Z'.Node,Ribbon.Drops Z' Z'' (Deck.fineP (P:= (A.B.a.clock.op m 0).patch) H (show C'.val=(deck c C).val*(A.B.a.S.block m).val from rfl) (show (deck c C).val=C.val*c.val from mul_comm ..)) θ')

section city
lemma compatible (hm:m<N) (hb:β∈ band A.B.a (m+1)) (hp:Visible A m N h R β) (hp':Visible A m N H R' β)
    (r k:ℕ) (hr:1≤r) (hc:4*hall F m n r+16≤c.val) (hC : 4*hall F m n r+16≤C.val)
    (hq : Permit A N m h H β Z Z') :
    Trio.Compatible ((Drawing.cabinet I' Z').tot O r k γ) ((Drawing.cabinet I Z).tot O r k γ) p (hall F m n r) := by
  obtain ⟨R'',Z'',hh,⟨θ,hθ⟩,θ',hθ'⟩ := hq; obtain ⟨Y',hy⟩ := framed F rfl hm hh hb
  intro x y U V hx hV ht; exact relate F h H I I' Z Z' hm hc hC hr R'' Z'' Y' (hh.leg.trans hp.leg.symm) (hh.leg.trans hp'.leg.symm) (hh.holds.trans hp.holds.symm) (hh.holds.trans hp'.holds.symm) (hh.home.trans hp.home.symm) (hh.home.trans hp'.home.symm) hθ hθ' hy x U y V hx hV ht

lemma library (hm:m<N) (hb:β∈band A.B.a (m+1)) (hp : Visible A m N h R β) (hI : SeekR F.shape A N m h I)
    (r k:ℕ) (hr:1≤r) (hc:4*hall F m n r+16≤c.val) {W W' : Slide.Stars→Side} (g : ∀ i,(W' i).val=(W i).val*(A.B.a.S.block m).val)
    (u : ∀ i, RG.Rep G (W' i)) (a : ∀ i, Chartlet F.shape A N m (g i) (u i))
    (s : ∀ i,Ribbon (u i) n)
    (he:∀ i,Visible A m N (g i) (u i) β) (hh:∀ i, 4*hall F m n r+16≤(W i).val)
    (hk : ∀ i, Permit A N m h (g i) β Z (s i)) (hF:∀ i j, Permit A N m (g i) (g j) β (s i) (s j)) :
    Trio.CompatibleP p (hall F m n r) ((Drawing.cabinet I Z).tot O r k γ) (fun i=> (Drawing.cabinet (a i) (s i)).tot O r k γ) :=
  ⟨fun i x k₀ b V=> Cabinet.rotates (Drawing.cabinet (a i) (s i)) O r k γ x V k₀ b, fun i j => compatible F (g j) (g i) (a j) (a i) (s j) (s i) hm hb (he j) (he i) r k hr (hh j) (hh i) (hF _ _), fun i=> compatible F _ _ I (a i) Z (s i) hm hb hp (he i) r k hr hc (hh i) (hk i),fun x=> Cabinet.fire (Drawing.cabinet I Z) p (Plev.canopy F h hm hI).1 r k x rfl|>.sites⟩

end city
end YM.RGComparison01.Library
