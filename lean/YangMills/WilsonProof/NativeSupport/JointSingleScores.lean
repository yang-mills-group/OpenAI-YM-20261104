import YangMills.WilsonProof.NativeSupport.JointExpansion
import YangMills.WilsonProof.NativeSupport.JointOldScores
import YangMills.WilsonProof.NativeSupport.JointLinearTariff

/-! Equality of the complete regular support and forced barcode sums for
one inherited switch, including the quiet coefficient. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.InletSusceptibility.NativeSwitch
open Function Finset Marker Merge.Switch Extra.Trajectories
open scoped Classical BigOperators
variable {I : Type} [Fintype I]

theorem kept (f g : Ways I) (i : I) (same : ∀ D : Finset I, D⊆{i} → jet f D=jet g D) :
    sound (singleProbe i) f=sound (singleProbe i) g := by
  rw [sound,sound,mapScores_apply,mapScores_apply]
  apply sum_congr rfl
  intro D _
  by_cases thin : D⊆{i}
  · rw [same D thin]
  · obtain ⟨j,hj,out⟩:=Finset.not_subset.mp thin
    have ne:j≠i:=fun e=>out (mem_singleton.mpr e)
    have zero : (∏ j∈D,singleProbe i j)=0 := prod_eq_zero hj (if_neg ne)
    rw [zero,smul_zero,smul_zero]
end YM.Integration.InletSusceptibility.NativeSwitch
namespace YM.Integration.InletSusceptibility.SelectedKernel

open Merge Merge.Palette JointLeaves
open Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Supply
open PhysicalNext.Repeat Mallow Lotus Ovens Motion Switch Merge.Palette
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {ι:Type}[Fintype ι]{G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C : ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (M:ι→Lotus.Leaf R)(Y:Cash W x μ L Q o C T R) (χ: Chi) (A:Rep G c) (marks : ι→Finset (Bond c)) (test : ι→Bond c→ℝ→ℝ) (rA:ι→ℝ) (K:ℝ → Finset ι → Code G c)



open NativeSwitch
theorem inherited_spine (i : ι) (old : marks i=∅) :
    spine M Y χ marks test rA (Stock.census Unit) (singleProbe i)=
      Photo.spine M Y χ rA (Stock.census Unit) (singleProbe i) := by
  funext P cfg
  unfold spine Photo.spine MergeProof.Accent.tally
  apply tsum_congr
  intro twig
  apply kept
  intro s sub
  exact old_regular_score M Y χ marks test rA s (fun j hj=>(mem_singleton.mp (sub hj)) ▸ old) _ cfg
end YM.Integration.InletSusceptibility.SelectedKernel
namespace YM.PhysicalNext.Repeat.Mallow.Many.Measured

open YM.Integration.InletSusceptibility
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
variable {ι:Type}[Fintype ι](M:ι→Lotus.Leaf (Q x))(rA:ι→ℝ)
variable (marks : ι→Finset (Bond (A.B.a.S.side m n))) (test : ι→Bond (A.B.a.S.side m n)→ℝ→ℝ)
variable (borel : ∀ i,∀ b∈marks i,Measurable (test i b))
variable (unit : ∀ i,∀ b∈marks i,∀ e0∈Set.Icc 0 (Push.BetaTransport.linkCap (A.B.a.clock.op m n)),‖test i b e0‖≤1)
variable (scope : ∀ i,∀ b∈marks i,(A.B.a.clock.op m n).ratio.embed b.1∈(M i).crest)
local notation "V" => SelectedKernel.shoot M W Chi.canonical marks test rA H.H.base f'
local notation "D₀" => lens H.H
local notation "T₀" => Collection.shelves H.X' (A.B.kin.path N m) B
set_option quotPrecheck false
local notation "T'" => Collection.branch H.X' (A.B.kin.path N m) (A.B.a.params m|>.clip) B (H.V' x) gV
local notation "M₁" => A.B.kin.path N m
local notation "g₂" => tempe (A:=A) (Z:=R.expense) (C:=R.target) (m:=m)
local notation "p" => (Marlin.tithe (2*e) g₂ B (Trio.coverTicket k))
local notation "P!" => (X.p.profile Jp)
-- base.χ.f tilt. R anchor. fuel from Verge
variable {b v₁ b₁ t q t₁ t₂ A₁ b₂ w : ℝ}{n':ℕ} (T:Captain (houseS H x) (X.p.profile (A.B.a.clock.J m)).order t q v₁ t₁ A₁ b₂ t₂ b₁ b n' Chi.canonical)
variable (hR: Arrives R.shape A.delay) (h:Herd (houseS H x) T.conduit A₁ b₁ n')
    (hp:Bikes (R.target (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)) (D.L (A.B.a.clock.J (m+1))) (R.shape.μ (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)) (A.B.a.clock.hatBeta m) (R.expense (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)|>.earn) w b₁ (X.p.profile (A.B.a.clock.J m)|>.order) n')
-- actual exponent/weather includes Beam supports.We leverage T.renewed exactly. term at latch.
local notation "z₀" => (Real.exp (-(Y).mark L Cμ y)*(2*Daisy.pledgeQ L Y Cμ y b₁ (P!).order n'))
variable (h₀:Palette.Plot M (houseS H x) rA)



open YM.Integration.InletSusceptibility.NativeSwitch Merge Marker Extra.Trajectories
theorem inherited_chain (i : ι) (old : marks i=∅) :
    Photo.chain (H.result x) (pupilK H x M rA marks test) (Stock.census Unit) (singleProbe i)=
      Photo.chain (H.result x) (Many.pupilK H x M rA) (Stock.census Unit) (singleProbe i) := by
  funext P cfg
  unfold Photo.chain MergeProof.Accent.tally
  apply tsum_congr
  intro twig
  apply kept
  intro s sub
  exact old_forced_score H x M rA marks test s (fun j hj=>(mem_singleton.mp (sub hj)) ▸ old) _ cfg
end YM.PhysicalNext.Repeat.Mallow.Many.Measured
