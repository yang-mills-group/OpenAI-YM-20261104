import YM.Integration.ManuscriptQLocalSpringTicket

/-! Expose the physical usability evidence used by the original spring deposit,
with exactly the source menu and pupil bought on that original cash. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Mallow.Many
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork Roof Daisy Charity Rain Roost Lotus
open UVNext.CouplingReset Animals Marlin Progress.DirectedRecipe Ovens Ovens.Pipes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} (g:G.Simple) {X:Metals G} {D: Rolls X.p} {A : Alloy X D}
    {R: Factor A} {l v:ℝ} {N m n:ℕ}(hm:m<N) {Q: In A.B.a m n} (H: Spring R N m n l v Q)
local notation "I" => Icc l v
local notation "L" => D.L (A.B.a.clock.J (m+1))
local notation "Θ" => A.B.a.S
local notation "J" => A.B.a.clock.J (m+1)
local notation "Jp" => A.B.a.clock.J m
local notation "K" => A.B.a.params m
local notation "wT" => radiusB (A.B.a.clock.hatBeta m)
local notation "k" => Rain.lint R.target A m
local notation "e" => Trio.base k wT
local notation "gV" => A.B.kin.alpha N m
local notation "B" => A.B.a.budget m
local notation "d" => H.ordinal
local notation "Y" => R.target J Jp
local notation "Ze" => R.expense J Jp
local notation "Cμ" => (R.shape.μ J Jp)
local notation "y" => A.B.a.clock.hatBeta m
local notation "O" => Chi.canonical
local notation "X₀" => H.H.base
variable (x: Icc l v)
local notation "hx" => x.property
local notation "W" => houseS H x
local notation "f'" => H.H.sister x
local notation "Tap0" => graft H.H H.knows H.W d x.val
open YM.Merge
open MergeProof Menu
variable (hE : (Q x).p.supportExponent≥100)(hN : 100≤(H.result x).p.supportExponent) (hS: Arrives R.shape A.delay) (hF:Pungent R.shape A.delay)
open YM.LocalTaylorR2 Orbit _root_.YM.Marker MergeProof.Accent
variable (hP : Mallow.RG12.Earned (Mallow.orbitD G) R.shape A.delay) (lP:ℕ)
variable {ι P:Type} [DecidableEq P] [Fintype P][Fintype ι]
  (C:_root_.YM.Marker.Census P)(b₀:ι→Menu.Hat C (Q x))(o:P→ Site (A.B.a.S.side (m+1) n))(r:P→ℝ)
set_option quotPrecheck false
local notation "o₀"=> (A.B.a.clock.op m n).ratio.parent ∘ o
local notation "F"=> H.result x
local notation "B'"=> (B).supportExponent
local notation "b₁"=> F -- unused
local notation "s₀"=> Mallow.straw Cμ L G y
local notation "P'"=> (A.B.a.budget m)
local notation "F'"=> A.B.a.clock.op m n
local notation "tx"=> (A.B.a.clock.hatBeta (m+1))
local notation "u₀"=> Mallow.station tx
local notation "u'"=> CalendarStep.loss J
local notation "Θ'"=> (houseS H x)
local notation "M'"=> fun i=> (b₀ i).M
local notation "M₀"=> fun i=> Menu.sumFee (b₀ i) r
local notation "M₁"=> fun i=> Menu.sing (b₀ i) r
local notation "g'"=>pupilK H x M' M₀

include hE hN hS hP hm g

theorem physicalMenuUsable (hb:∀i,0<r i) (hs:Extra.Multi.Occupancy o₀ (J+1))
    (plain:Menu.Offer o b₀ r ((Q x).p.B) ((Q x).p.supportExponent-4) u₀) :
    ∃ income volume decay : ℝ, Photo.Usable M' Θ' Chi.canonical (H.result x) M₀ (pupilK H x M' M₀) income volume decay := by
  let Rπ := houseS H x
  have hC := hS _ _ (A.B.valid.pays m) _ (step_paid A.B.a m)
  let Gx := minted_same R.shape hP
  have hK := Gx.word _ _ (A.B.valid.pays m) _ (step_paid A.B.a m)
  have hz : tx = betaF G y L := beta_eq A.B.valid m
  have hHop : Palette.shipPrice L Y y (J+1) u₀ := hz.symm ▸ hK.shipping
  have hΞ := Opera.protocol A.B hm R.pledging.conducts.full (n:=n)
  obtain ⟨a',ba,q,t',z,F'₀,t₃,t₄,t₅,t₆,node',hB,hA,N₀,hN'⟩ :=
    hC.1.2 _ _ _ _ hΞ (Q x) _ (houseS H x)
  have he : (B).supportExponent+3 ≤ (Ze).earn := by
    have he' := (R.pledging.agenda _ _ (step_paid A.B.a m)).1
    rw [Rain.jersey (A:=A) (m:=m)|>.2.2.1]
    linarith
  have plot (offered : ι → Menu.Hat C (Q x))
      (h₁ : Menu.Offer o offered r ((Q x).p.B) ((Q x).p.supportExponent-4) u₀) :
      Palette.Plot (fun i => (offered i).M) Θ' (fun i => Menu.sumFee (offered i) r) := by
    apply Photo.bidding Rπ C r hb offered o hC.1.1
    · rw [Rπ.laws.intake.sizes, Rπ.laws.data.funds.length_eq]
      exact hB.covers
    · change 4 ≤ (Y).exp+_+_
      change 100 ≤ B' at hN
      linarith only [he,hN,(Ze).worth,(Ze).first,(Ze).second,(Y).usable,(Y).pos]
    · exact hE
    · exact hz.symm ▸ hK.nonneg
    · exact h₁
    · exact hs
    · exact hHop
  have hV:=plot b₀ plain
  have hv:=Many.usable g hm H x M' M₀ N₀ hS hB hV
  exact ⟨_, _, _, hv⟩
end YM.PhysicalNext.Repeat.Mallow.Many

namespace YM.Integration.WilsonRootedPhysicalUsable
open Function Filter Finset Set Lattice Wilson RG RG.Shoot
open Push Push.PriceCompiler Pressure Pressure.Tube Progress.DirectedRecipe
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open LocalTaylorR2 LocalTaylorR2.Orbit LocalTaylorR2.Candle RG01.Survive MergeProof
open scoped Classical BigOperators
variable {G : Gauge} (R : Run G) {N period m : ℕ} {hm : m < N}
  (P : ActualRunSpring.Packet R N period m hm)
  {T : Campaign R} {Δ : Daisy.Charity.RG12.Decal G}
local notation "phaseOrder" => R.alloy.B.a.clock.J (m+1)
local notation "fineBeta" => R.alloy.B.a.clock.hatBeta (m+1)
local notation "fineCoupling" => Pert.Asymptotics.regulatorRun R.family N period (m+1)
local notation "fineRep" => P.input P.point.val
local notation "coarseRep" => P.spring.result P.point.val
local notation "stepData" => R.alloy.B.a.clock.op m period
local notation "physicalHouse" => Mallow.houseS P.spring P.point

/-- Actual physical run, actual funded source bill and true coarse deposition.
The same authentic spring determines every linked ticket and every retained
coarse forced partner on the independently chosen coarse sample. -/
theorem physical (hG:G.Simple) (paid:R2I.Funded ((Mallow.orbitD G).paired Δ) R T)
    {V ι:Type} [DecidableEq V] [Fintype V] [Fintype ι] (Γ:Marker.Census V)
    (a:ι→Menu.Hat Γ (fineRep)) (o:V→Site (R.alloy.B.a.S.side (m+1) period)) (w:V→ℝ)
    (hw:∀i,0<w i) (occupies:Extra.Multi.Occupancy ((stepData).ratio.parent ∘ o) (phaseOrder+1))
    (offer:Menu.Offer o a w (fineRep).p.B ((fineRep).p.supportExponent-4) (Mallow.station fineBeta)) :
    ∃ e a' t : ℝ, Merge.Photo.Usable (fun i=>(a i).M) physicalHouse Push.SectorMeasure.Chi.canonical
      (P.spring.result P.point.val) (fun i=>Menu.sumFee (a i) w)
      (Mallow.Many.pupilK P.spring P.point (fun i=>(a i).M) (fun i=>Menu.sumFee (a i) w)) e a' t := by
  obtain ⟨earned,bounds⟩:=ManuscriptQLocalMarkedGradeTail.campaign R paid
  have same:(fineRep).p=R.alloy.B.a.budget (m+1):=(P.spring.knows P.point.val P.point.property).1.point
  have hin:100≤(fineRep).p.supportExponent:=same.symm ▸ bounds (m+1)
  exact Mallow.Many.physicalMenuUsable hG hm P.spring P.point hin (bounds m) R.b.r earned Γ a o w hw occupies offer
end YM.Integration.WilsonRootedPhysicalUsable
end
