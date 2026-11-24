import YangMills.WilsonProof.NativeSupport.JointExpansion
import YangMills.WilsonProof.NativeSupport.NativeSwitchLinear

/-! At a mask containing only inherited switches the measured tagged push,
both forced recodings and all corresponding jets coincide with the original
mounted operators. This identifies the actual linear term of the measured
step on old inputs. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
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


private theorem old_value (f g : Switch.Ways ι) (t : ℝ) (ht : 0<t)
    (D : Finset ι) (same : ∀ s⊆D,f t s=g t s) : Switch.decode f t D=Switch.decode g t D := by
  have all (s : Finset ι) (hs : s⊆D) : Switch.decode f t s=Switch.decode g t s := by
    induction s using Finset.strongInductionOn with
    | _ s ih =>
      have full := (congrFun (Switch.decodes (X:=f) t ht) s).trans
        ((same s hs).trans (congrFun (Switch.decodes (X:=g) t ht) s).symm)
      change ∑ i∈s.powerset,t^i.card*Switch.decode f t i=
        ∑ i∈s.powerset,t^i.card*Switch.decode g t i at full
      have inside : s∈s.powerset := mem_powerset.mpr (Finset.Subset.refl s)
      rw [←add_sum_erase _ _ inside,←add_sum_erase _ (fun i=>t^i.card*Switch.decode g t i) inside] at full
      have rest : ∑ i∈s.powerset.erase s,t^i.card*Switch.decode f t i=
          ∑ i∈s.powerset.erase s,t^i.card*Switch.decode g t i := by
        refine sum_congr rfl fun i hi=>congrArg (t^i.card*·) ?_
        have sub:=mem_powerset.mp (mem_of_mem_erase hi)
        exact ih i (Finset.ssubset_iff_subset_ne.mpr ⟨sub,ne_of_mem_erase hi⟩) (sub.trans hs)
      rw [rest] at full
      exact mul_left_cancel₀ (pow_pos ht _).ne' (add_right_cancel full)
  exact all D (Finset.Subset.refl D)

theorem old_jet (f g : Switch.Ways ι) (D : Finset ι)
    (same : ∀ t,∀ s⊆D,f t s=g t s) : Switch.jet f D=Switch.jet g D := by
  have eq := Filter.map_congr (Switch.approached.mono (fun t ht=>old_value f g t ht.1 D (same t)))
  unfold Switch.jet Filter.limUnder; rw [eq]

theorem old_color (r : Finset ι) (hr : ∀ i∈r,marks i=∅) (t : ℝ) (U : Config G c) :
    color M marks test Y χ U (Palette.ways rA t r)=Palette.color M Y χ U (Palette.ways rA t r) := by
  apply clear
  intro i active
  exact hr i (by by_contra hi; exact active (if_neg hi))

theorem old_tone (r : Finset ι) (hr : ∀ i∈r,marks i=∅) (t : ℝ) (i : Y.fragrances) (U : Config G c) :
    tones M Y χ marks test rA i U t r=Photo.tones M Y χ rA i U t r := by
  unfold tones Photo.tones song Palette.song
  rw [old_color M Y χ marks test rA r hr,old_color M Y χ marks test rA ∅ (by simp)]

theorem old_regular_score (r : Finset ι) (hr : ∀ i∈r,marks i=∅) (i : Y.fragrances) (U : Config G c) :
    Switch.jet (tones M Y χ marks test rA i U) r=Switch.jet (Photo.tones M Y χ rA i U) r :=
  old_jet _ _ r fun t s sub=>old_tone M Y χ marks test rA s (fun i hi=>hr i (sub hi)) t _ _

variable {R' : RG.Rep G f} (J : Cash W x μ L Q o C T R') (D : Match.Alliance J Y 1 0)
theorem old_shoot (r : Finset ι) (hr : ∀ i∈r,marks i=∅) (t : ℝ) :
    shoot M Y χ marks test rA J D t r=Palette.shoot M Y χ rA J D t r := by
  unfold shoot Palette.shoot shootK Palette.shootK
  apply congrArg (Progress.DirectedRecipe.stuff (Refrain.visa J D))
  funext i U
  exact congrArg (fun y=>Y.smilesMill U y i.val) (old_color M Y χ marks test rA r hr t U)
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


theorem old_pupil (r : Finset ι) (hr : ∀ i∈r,marks i=∅) (t : ℝ) :
    pupilK H x M rA marks test t r=Many.pupilK H x M rA t r := by
  have step (v : ℝ) : shiftK H x M rA marks test v r=Many.shiftK H x M rA v r :=
    congrArg (fun code=>solid (Marlin.hak D₀) B (spice Tap0 code))
      (SelectedKernel.old_shoot M (houseS H x) Chi.canonical marks test rA H.H.base (H.H.sister x) r hr v)
  exact congrArg (fun f=>final.frigid T₀ T' f B t) (funext step)

theorem old_forced_score (r : Finset ι) (hr : ∀ i∈r,marks i=∅) (l : ℕ) (U : Config G (A.B.a.S.side m n)) :
    Switch.jet (fun t s=>pupilK H x M rA marks test t s l U) r=
      Switch.jet (fun t s=>Many.pupilK H x M rA t s l U) r := by
  apply SelectedKernel.old_jet
  intro t s sub
  rw [old_pupil H x M rA marks test s (fun i hi=>hr i (sub hi))]
end YM.PhysicalNext.Repeat.Mallow.Many.Measured
