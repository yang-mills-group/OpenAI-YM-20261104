import YM.RGComparison01.Splurge

/-!
# Cross-period bridge on low reflections on ACTUAL input model

 Handles any Posts on each input with E engagement (extra Ribbon).
 Extension to non-comparable periods with common-multiple auxiliary bridge;
 no assumption that the whole R.eval is transplanted. Larger/Walls
 size lower. -/

set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01.Library
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter
open PhysicalNext PhysicalNext.Repeat Deck Stellar Mint Greenbelt Boulevard
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Extra.Iteration Song Refrain Reserves OmitClusters
open Divides Input Org Supply PriceCompiler Next.Scheduling Progress.DirectedRecipe Time Opera
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {X : Metals G} {D : Rolls X.p} {A : Alloy X D} (F : Roost.Factor A)
variable {c f C F' : Side} {m n N k r M : ℕ}
variable (h : f.val=c.val*(A.B.a.S.block m).val) (H : F'.val=C.val*(A.B.a.S.block m).val)
    {R: RG.Rep G f} {R' : RG.Rep G F'}
    (I : Boulevard.Chartlet F.shape A N m h R) (I' : Boulevard.Chartlet F.shape A N m H R')
local notation "J" => (A.B.a.clock.J (m+1))
local notation "E" => (A.B.a.clock.J m)
local notation "B" => radiusB (A.B.a.clock.hatBeta m)
local notation "Q" => F.shape
local notation "O" => Chi.canonical
abbrev spread (m n : ℕ) :=
  let x:= radiusB (A.B.a.clock.hatBeta m)
  Mint.width (F.target (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)).halo x (x+n)
abbrev hall (m n r : ℕ) := Cabinet.studio (spread F m n) r (radiusB (A.B.a.clock.hatBeta m))
local notation "b" => Library.spread F m n
local notation "p" => A.B.a.budget m
local notation "Y" => A.B.a.budget (m+1)
local notation "γ" => A.B.kin.alpha N m
set_option quotPrecheck false
local notation "t" => A.B.a.clock.hatBeta m
variable (Z : Ribbon R n) (Z' : Ribbon R' n)
section one
variable (hC:C.val=c.val*M)
    {θ : Z'.Node→Z.Node}
variable (hp : R'.path=R.path) (hR : R'.beta=R.beta) (hz:R'.p=R.p) (hr : Ribbon.Drops Z Z' (Deck.fineP («P»:= (A.B.a.clock.op m 0).patch) h H hC) θ)
include X F h H I I' hp hR hr hz
lemma transverse (hm:m<N) (hc : 4*Library.hall F m n r+16≤c.val) (hℓ: 1≤r) (x: Site C) (V:Config G c) (hv:RG.flags (Pressure.temp t) V=∅) :
    Cabinet.tot (Drawing.cabinet I' Z') O r k γ x ((normal (Deck.divides hC) hC).links V) = Cabinet.tot (Drawing.cabinet I Z) O r k γ (splitter (Deck.divides hC) x) V := by
  have he:2≤ c.val:= by omega
  have h₀ : 4*Cabinet.garage (b) r<c.val:= by unfold Library.hall Cabinet.studio at hc; omega
  have ht : 2*(b+3)<c.val:= by
    have hx : 1 ≤ r*r := Nat.mul_pos hℓ hℓ
    dsimp only [Cabinet.garage] at h₀; nlinarith only [hx,h₀]
  let W:=F.pledging
  have hh:= W.jewels _ _ (A.B.valid.pays m) _ (PriceCompiler.step_paid A.B.a m)
  obtain ⟨c₀,d,v,s,z,u₀,r₀,k',Y',l,q,⟨H₀,h₂⟩,h₁,h₃⟩:= hh.2 _ _ _ (Pane.orchestra A N h) I.laws.data.funds (Pane.ovation A N h hm W.conducts.full) _ I
  obtain ⟨c₁,d',v',s',z',u₁,r',k'',p',l',q',⟨H₁,he'⟩,ha,hX⟩:= hh.2 _ _ _ (Pane.orchestra A N H) I'.laws.data.funds (Pane.ovation A N H hm W.conducts.full) _ I'
  have ht:= Drawing.relay (I':=I') (I:=I) («Q»:=A.B.a.clock.kernel) (h:=h) (H:=H) hC he hp Z Z' hr hz hR ht
  exact Relay.itinerary ht h₀ rfl V hv H₀ H₁ x γ k hR
end one

-- importer for product multiple (new ghost, same stage/tube, SAME β and path model)
section staples
include F h H I I'
abbrev deck (c C : Side) := c*C
local notation "Zc" => (deck c C)*(A.B.a.S.block m)
local notation "Zm" => deck c C
lemma relate (hm:m<N) (hc : 4*Library.hall F m n r+16≤c.val) (hC : 4*Library.hall F m n r+16≤C.val) (hℓ : 1 ≤ r)
    (R'' : RG.Rep G ((deck c C)*(A.B.a.S.block m))) (Z'' : Ribbon R'' n) (J' : Chartlet F.shape A N m (show (Zc).val=(Zm).val*(A.B.a.S.block m).val from rfl) R'')
    (hp:R''.path= R.path) (hp': R''.path= R'.path) (hb:R''.beta= R.beta) (hb': R''.beta=R'.beta) (hK:R''.p=R.p) (hK' : R''.p=R'.p)
    {θ : Z''.Node→ Z.Node} (he:Ribbon.Drops Z Z'' (Deck.fineP («P»:= (A.B.a.clock.op m 0).patch) h (show (Zc).val=(Zm).val*(A.B.a.S.block m).val from rfl) (show (Zm).val=c.val*C.val from rfl)) θ)
    {θ' : Z''.Node→Z'.Node} (he':Ribbon.Drops Z' Z'' (Deck.fineP («P»:= (A.B.a.clock.op m 0).patch) H (show (Zc).val=(Zm).val*(A.B.a.S.block m).val from rfl) (show (Zm).val=C.val*c.val from mul_comm ..)) θ')
    (hJ : Boulevard.SeekR F.shape A N m rfl J') (x : Site C) (V:Config G C) (y:Site c) (W:Config G c) (hV:RG.flags (Pressure.temp t) V=∅) (hw: RG.flags (Pressure.temp t) W=∅)
    (hd:Agrees (Lattice.box (hall F m n r)) (expandAt x V) (expandAt y W)) : Cabinet.tot (Drawing.cabinet I' Z') O r k γ x V=Cabinet.tot (Drawing.cabinet I Z) O r k γ y W:= by
  let f':=Cabinet.tot (Drawing.cabinet J' Z'') O r k γ; let v : (Zm).val=c.val*C.val:=rfl; let v' : (Zm).val=C.val*c.val:= mul_comm ..
  have hv := Plev.canopy F rfl (H:=J') hm hJ |>.1
  let u:= Lattice.translate y W; let w:= Lattice.translate x V
  have ht := transverse F h rfl I J' Z Z'' v hp hb hK he hm hc hℓ (0:Site Zm) u (by unfold u; rw [← pull_one]; exact Pane.tranquility W hw ..) (k:=k)
  have hx := transverse F H rfl I' J' Z' Z'' v' hp' hb' hK' he' hm hC hℓ (0:Site Zm) w (by unfold w; rw [← pull_one]; exact Pane.tranquility V hV ..) (k:=k)
  rw [map_zero] at hx ht
  have he : (p).Regular (neighbors (hall F m n r) (0:Site Zm)) (f' 0):= Cabinet.fire (Drawing.cabinet J' Z'') p hv _ _ _ rfl
  have hM : f' 0 ((normal (Deck.divides v') v').links w)= f' 0 ((normal (Deck.divides v) v).links u):= by
    apply he.sites; refine Slide.readNear 0 (by have hh: c.val ≤ (Zm).val:= Nat.le_mul_of_pos_right _ C.pos; omega) ?_; rw [Slide.rolls,Slide.rolls,map_zero,map_zero]; unfold w u; rw [Slide.increases,Slide.increases]; exact hd
  unfold u at ht hM; unfold w at hx hM
  rw [← pull_one, Cabinet.rotates] at ht; rw [← pull_one, Cabinet.rotates] at hx;
  simp only [Lattice.affine, Signed.act_one,zero_add] at hx ht
  rw [← hx,← ht]; convert hM <;> rw [pull_one]
end staples
end YM.RGComparison01.Library
