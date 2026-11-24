import YM.AllOrder.Horizon.Packing
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Shop
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Bid Planned.JetPort PhysicalNext Repeat Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Roof Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Trio Lantern High Roost
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {X: Metals G} {D: Rolls X.p} (A : Alloy X D) (F: Factor A) {c f : Side} {m n N : ℕ}
local notation "a" => A.B.a
local notation "J" => (A.B.a.clock.J (m+1))
local notation "I" => (A.B.a.clock.J m)
local notation "L" => (D.L J)
local notation "x₀" => (A.B.a.clock.hatBeta m)
local notation "z" => betaF G x₀ L
local notation "V" => A.B.a.budget m
local notation "P" => (F.target J I)
local notation "R" => F.shape
local notation "Ω" => (F.expense J I)
local notation "B" => radiusB x₀
set_option quotPrecheck false
local notation "W" => (A.B.a.params m).clip
local notation "γ" => (A.B.kin.alpha N m)
local notation "O" => Chi.canonical
set_option quotPrecheck false
local notation "E" => X.p.profile I
local notation "u" => (tall I)
local notation "Y" => (parking u (P).halo)
local notation "d" => (Meadow.studio Y B)

variable {η : ℕ→ℕ→ℝ} (H : Lodge D F.shape η A.delay)
variable {β : ℝ} (π:f.val=c.val*(A.B.a.S.block m).val) {U:RG.Rep G f} (Z': Chartlet F.shape A N m π U) (hz:SeekR F.shape A N m π Z') (hm:m<N)
local notation "S'" => Pane.panel A m π
local notation "Σ₀" => orchestra A N π
local notation "V₁" => (A.B.a.budget (m+1))
local notation "χ" => Chi.canonical
local notation "Y₀" => (F.shape.o J I|>.K)

local notation "u₀" => (A.B.kin.path N (m+1))
local notation "T0" => Pane.orchestra A N
variable {C K:Side} (H':K.val=C.val*(A.B.a.S.block m).val)
  {U': RG.Rep G K} (Z'':Chartlet F.shape A N m H' U')
  (hϕ : U.path=A.B.kin.path N (m+1)) (hq : U'.path=A.B.kin.path N (m+1))
  (he : U.p= A.B.a.budget (m+1)) (hg : U'.p= A.B.a.budget (m+1)) (hβ: U.beta∈ band A.B.a (m+1)) (hvβ: U.beta=U'.beta)

abbrev ledgerV (k:ℕ) := chamber (strands (tall I) (steady Z' u k)) χ k γ
local notation "Π" => A.B.a.S.block m
local notation "d0" => Meadow.studio Y B
include H hm hϕ he

lemma fanout {M:ℕ} (he':U.beta=β) (hC':C.val=c.val*M) (ht:4*d+16≤c.val) (k:ℕ)
    (Zt:Chartlet F.shape A N m H' (Pane.virgin (Pane.orchestra A N H') (V₁) β)) (x:Site C) (V':Config G c) (hV:flags (V).threshold V'=∅): ledgerV A F H' Zt k x ((normal (Deck.divides hC') hC').links V')=ledgerV A F π Z' k (Macrame.splitter (Deck.divides hC') x) V':= by
  obtain ⟨C0,d',v',b',r',s',w',H₀,h',j,n,M',hx⟩:= appointed A F H π hm Z'; obtain ⟨C0',b,v,U0,T,u',w,z',q,c'',i,N',hp⟩:= appointed A F H H' hm Zt
  let A' := A.B.a.params (m+1); let B' := B
  have ht': clusterBound u (Mint.width (P).halo B B) u + Mint.width (P).halo B B ≤ d:= traffic u _ _ (V).B_pos
  exact compared (T:=(T0 π)) (T':=(T0 H')) hC' (show 2 ≤ c.val from (by omega)) hϕ.symm rfl he.symm he'.symm O V' hV M' N' u k x γ ht' (by omega)
include hq hg hβ hvβ
lemma afloat (k:ℕ) (hc:4*d+16≤c.val) (hC:4*d+16≤C.val) : Compatible (ledgerV A F π Z' k) (ledgerV A F H' Z'' k) V d:= by
  intro x y Q' W' hQ hW hE
  let Cb := c*C; let Fb:= Cb * (Π); have hM:Fb.val=Cb.val*(A.B.a.S.block m).val:=rfl; have hN: Cb.val=c.val*C.val:=rfl; have hN': Cb.val=C.val*c.val:= mul_comm ..
  have he' : c.val ≤ Cb.val:=Nat.le_mul_of_pos_right _ C.pos
  obtain ⟨Zb,Hb⟩:= Pane.affords A N hM hm (show 100*(1+radiusB x₀) ≤ Cb.val from Z'.laws.data.room.buys.trans he') F.shape F.pledging.conducts.income.grow.1 F.pledging.conducts.full hβ
  let Y1 := Lattice.translate x Q'; let Y2:= Lattice.translate y W'; let Z:= normal (divides hN) hN; let Z2:= normal (divides hN') hN'
  have h1:flags (V).threshold Y1=∅:= by unfold Y1; rw [← pull_one]; exact Pane.tranquility Q' hQ ..
  have h2:flags (V).threshold Y2=∅:= by unfold Y2; rw [← pull_one]; exact Pane.tranquility W' hW ..
  have hK:= palaces A F H hM Zb Hb hm k (0:Site Cb)
  calc
    _ = ledgerV A F π Z' k 0 Y1 := by unfold Y1; unfold ledgerV; rw [← pull_one, High.turns]; simp [Lattice.affine]
    _ = ledgerV A F hM Zb k 0 (Z.links Y1):= by rw [fanout A F H π Z' hm hM hϕ he rfl hN hc k Zb 0 _ h1,_root_.map_zero] -- let Z unfolding rw?
    _ = ledgerV A F hM Zb k 0 (Z2.links Y2):= by
      apply hK.sites _ _ (Slide.readNear (Z:=d) 0 (by omega) ?_); rw [Slide.rolls,Slide.rolls,map_zero,map_zero]; unfold Y1 Y2; rw [increases,increases]; exact hE
    _ = ledgerV A F H' Z'' k 0 Y2:= by rw [fanout A F H H' Z'' hm hM hq hg hvβ.symm hN' hC k Zb 0 _ h2,_root_.map_zero]
    _ = _ := by unfold Y2; unfold ledgerV; rw [← pull_one, High.turns]; simp [Lattice.affine]
end YM.AllOrder.Shop
