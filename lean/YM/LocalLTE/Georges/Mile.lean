import YM.LocalLTE.Georges.Lucy
import YM.LocalLTE.Estate.Call
/-! # Dual use of actual cards. Same emissary as in Mallow Hahn. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Mallow
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork Roof Daisy Charity Rain Roost Lotus Blush
open UVNext.CouplingReset Animals Marlin Progress.DirectedRecipe Ovens Ovens.Pipes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge}{X:Metals G}{D:Rolls X.p}{A:Alloy X D}
local notation "L"=> A.B.a
local notation "y" i=> A.B.a.clock.hatBeta i
set_option quotPrecheck false
structure Ranch (R:Factor A) (P τ:ℕ) (e:ℝ) where
    allocation : Funding R P e
    heritage : Trail allocation τ
    health : Cready allocation heritage
    adorn : Adorn allocation heritage
    merchandise : Merchandise R.shape heritage.footprint heritage.ψ A.delay
    preview : Preview allocation
variable {R:Factor A}{P τ:ℕ}{e:ℝ}
structure Turf (R:Factor A) (N m n:ℕ) where
    p :ℕ
    ac :ℕ
    e : ℝ
    ranch : Ranch R p ac e
    day: Set ℝ
    request:ℝ
    choice: In L m n
    career: Career ranch.allocation N m n day request choice
    v :ℝ
    k :ℕ
    k' :ℕ
    held : v ∈ day
    force : ∀ hm:m<N,Film ranch.allocation ranch.heritage ranch.preview career k k' hm
namespace Turf
variable {N m n:ℕ}(T:Turf R N m n)
local notation "W₀"=> T.ranch.allocation
local notation "H'"=> T.career
local notation "tag"=> Mallow.spread (A.B.a) N T.ac n (m+1)
abbrev inPort:= T.choice (T.career.holds.latch T.v)
abbrev houseB : Guide A.B R.shape N m n T.inPort:= T.career.hearth T.ranch.allocation T.v
abbrev output:= T.career.Voy T.ranch.allocation T.ranch.heritage T.k' tag T.k T.v
abbrev pupilD := Career.waxA W₀ T.career T.ranch.heritage T.k' tag T.v -- binder k
abbrev lamp (M:Leaf T.inPort):= T.pupilD M T.k
abbrev door := Career.stencilA W₀ T.career T.ranch.heritage T.k' tag T.v T.k
lemma senses : Lives A.B.bake N (m+1) n T.inPort ∧ T.inPort.beta∈band A.B.a (m+1):= T.career.turns _ (T.career.holds.latch T.v).2
variable (g:G.Simple)(hm:m<N)(hR:Arrives R.shape A.delay)
include g hm hR
lemma opensV : MergeProof.SoundDoor (A.B.a.clock.op m n) T.door:= T.career.soundA T.ranch.allocation T.ranch.heritage hm T.k' tag T.v T.held T.ranch.adorn (T.force hm).motion (T.force hm).cards hR T.ranch.merchandise g ((T.force hm).spring _ T.held) -- order
local notation "T!"=> T.houseB
variable (U': Cloud T.inPort)(a: Site (A.B.a.S.side m n))(o:ℂ){j:ℕ}{F:Labels.Frame G j}(S: YM.Source.SectionData F)
local notation "P'"=> T.output
local notation "B"=> A.B.a.budget m
local notation "M!"=> (screen (T!) U' (T.lamp U'.live) (T.lamp U'.pale) o F)
local notation "δ"=> Real.sqrt (A.B.a.clock.forcedAllowance m)
local notation "V₀"=> D.L (A.B.a.clock.J (m+1))
local notation "I"=> A.B.a.clock.J m
local notation "J"=> A.B.a.clock.J (m+1)
local notation "P₀"=> scope T! U' a
local notation "X'"=> (R.target J I)
local notation "u"=> (R.shape.μ J I)
local notation "v₁"=> straw u V₀ G (A.B.a.clock.hatBeta m)
local notation "y0"=> A.B.a.clock.hatBeta m
local notation "f0"=> (δ)⁻¹*(‖o‖*(jewelDebt U'.live X' V₀ y0+jewelDebt U'.live X' V₀ y0)*v₁)
local notation "c"=> marvel (Q:=R.target J I) («L»:=V₀) (x:=y0) U'
lemma lightB (ha:a∈ U'.live.crest.image (A.B.a.clock.op m n).ratio.parent) : (M!).Format a P₀ T.output ∧ (M!).eval a P₀ S T.output=o • ((A.B.a.clock.op m n).push T.inPort.beta U'.milk)∧ ∀ r:ℝ,(∃ s:T.houseB.fragrances→ℝ, SumBudget (fun i=> Local.reservedMass B (locus U'.live T.houseB a i) (s i)) r ∧ ∀ i,prince U'.live T.houseB i→ (B).supBounds a (locus U'.live T.houseB a i) (pane T.houseB U' o i) (s i)) → YM.Planned.GuardedAtom.Deck M! a P₀ T.output δ (‖o‖*(c+c)+r) f0:=by
   have h:= T.force hm; exact T.career.posedA T.ranch.allocation T.ranch.heritage hm T.k' tag T.v T.held T.ranch.adorn h.motion h.cards a hR T.ranch.merchandise g (h.spring _ T.held) U' ha o S -- order edit
omit g hm hR
-- spring auxiliary with same house to reuse other pointwise estimates; no equality of outputs needed (or promised).
local notation "QF"=> (fun _:ℝ=> T.inPort)
local notation "ZeroF"=> (⟨0,(Set.left_mem_Icc.mpr (le_refl 0))⟩:Set.Icc (0:ℝ) 0)
include hm
lemma drink : ∃ S:Spring R N m n 0 0 (fun _=>T.inPort), houseS S ZeroF=T.houseB:=by
   let C:= T.ranch.allocation; let B':= T.houseB; have h:=T.senses
   have he : Curve (A.B.a.budget (m+1)) QF (Set.Icc (0:ℝ) 0):= (Urns.uniform_curve (A.B.a.budget (m+1)) T.inPort).mono (Set.subset_univ _)
   let F' := R.pledging
   let X:Roof.Embrasure (U:=A) (Y:=R.shape) (N:=N) QF (Set.Icc 0 0) 0:=
       { houses := fun _=> B', honors:= fun _=> T.career.holds.honors _, he:=(ZeroF).2, sister := fun _=> Meadow.intern B', agrees:=fun _=>rfl }
   let W:= Classical.choice (Rain.learns (R:=R.shape) (A:=A) hm F'.conducts.income.grow.1 F'.conducts.full)
   obtain ⟨d,hD,hE⟩:= (Rain.topped F' hm X he (fun _ _=>h) R.inn (R.settles _ _) R.floor W isCompact_Icc).exists
   exact ⟨⟨he,fun _ _=>h,X,W,d,T.career.forest,fun i hi=>⟨hE i hi,hD i hi⟩⟩,rfl⟩
end Turf
end YM.PhysicalNext.Repeat.Mallow
