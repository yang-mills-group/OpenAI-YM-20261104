import YM.QuadraticLocal.Germ.Stash
/-!
# Held-test qlocal push — STATIC collars in each marked word before summation

Use mould `Lesson`: families reporting over T with pointwise integral congruence; graded by
slot occurrence WORD (not just set of marked positions). VerifiedReset predictor has same rules
inside regular good chart and WHOLE forced bits. Including absent/gasKey as well as repeated
letters. The uniform comparison budgets alone don't give these equalities.

Extension of the supplied RemainderComparison/Solos/Hues, here generalized in budget and also
checking each genuine stencil's provenance, reusing its uniform dominator and local-continuation
proofs. Global captions have no flagged extension costs in this argument.

As a tidy diagnostic: `.dew` gives ALL held properties on an open neighborhood of every healthy
field. This avoid losing linearity of germs exactly at boundary by inferring more than what the
mask permits. No assertion about the unmasked nominal solutes everywhere at every step.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Collar
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Contract Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse PhysicalNext.Repeat Gas
open Coat Matter ProbabilityTheory Poll Pond Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open Itinerary Animals March Captain Greenbelt Stained Ursell Trees Reserves
open Merge Palette Next.Scheduling OmitClusters AnalyticBridge.VerifiedReset
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {θ ι : Type} {R₀ : θ→Type*} [∀ i, NormedAddCommGroup (R₀ i)] [∀ i,NormedSpace ℝ (R₀ i)]
variable {α:Type*}{G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C : ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (H:Cash W x μ L Q o C T R) {q A B b e u v d L' Gp:ℝ}{j n k s J I:ℕ}(χ:Chi)
open Lyric Mosaic Sleet Serif Typeface
open Solos (tart)
variable (M:ι→Portrait R α)
variable (Ll:Lesson ι α) (Hpc: ∀ (U:Config G f) i, Ll.Knows {i} (fun a=> ((brand M a i).ingredient U)))
local notation "V'" z:max=> brand M z
variable (y:α)(X:Coat T F) (i:Drums (brand M y) S)
local notation "q₂"=> i.val.val
variable (N:Captain H j q d v u A b r B e n χ)
variable {E₁:Type}[NormedAddCommGroup E₁][NormedSpace ℝ E₁][FiniteDimensional ℝ E₁]
variable (U:E₁→ Config G c)(p:Molecule S)(a:E₁)(hx:X.x=x)(hk:X.width=o.K)(hF:X.χ=χ)(h:U a=X.V)(hp:Mode U a j v)
variable (hU:Healthy (Pressure.temp x) (H.unionP p) X.V)
local notation "St"=> edgesM S (H.unionP p) (X.B)
set_option quotPrecheck false
local notation "P₀"=> prism T x χ o.K
local notation "I₁"=> podium S G (H.unionP p) X.B
local notation "G↑" u=> (team (V' u) i)
-- Uniform z S.Setup Neighborhood.H Needed all α for recover outside-parameter junk
include H Hpc N h hp hx hk hF -- hU ? needed? no chutes .planted ensure boosts
omit Hpc
set_option maxHeartbeats 200000 in
lemma rollick (b':S.Choices) :
    let Z := (planted X p).taggedL b'; let K:=(F.order G).prod Z.dice
    ∀ᶠ t in 𝓝 a, ∀ z: α,let G₀:=(team (brand M z) i); let f:= G₀.carat (edgesM S (H.unionP p) X.B) Z (U t) A Q.table p W o.a Q.halo
                                            ; Integrable f K ∧ G₀.cinema (vary Z (U t)) p W o.a Q.table Q.halo (podium S G (H.unionP p) X.B)=∫ x,f x ∂K:=by
    intro Z K
    have hQ:=H.laws.data
    have hm : Z.manifest:=planted_valid X p
    have ht:Z.x=x:=hx
    have hh:= N.oboe.flow F Z ht hF hk hm E₁ U a h hp
    have hH:Cash W Z.x μ L Q o C T R:= ht.symm ▸ H
    have hA:8*o.a*Pressure.fiery G Z.x S.patch.L≤ A/2:=by rw [ht,hQ.funds.length_eq]; exact N.oboe.mode
    have hz_b:=congr_arg radiusB ht
    let L' := team (tart H M y) (show Lyric.Drums (tart H M y) S from i)
    have he:= (L'.boosts Z p hH hk hm St hh N.oboe.conduit hA).2
    obtain ⟨s,hs⟩:= hh.sails
    filter_upwards [he,Silica.nearby Z N.oboe.conduit hh.lifts hs] with y' hy hX
    intro z G₀ f'
    have hΖ: ShellAccess S G Z.x W Z.width o.γ:=by rw [ht, show Z.width=o.K from hk]; exact H.laws.data.access
    have hF': Integrable f' K :=by
       let Z' p:=f' p
       have he:Measurable Z':= (team (V' z) i).docks Z (U y') St N.oboe.conduit hX measurable_fst measurable_snd hH.laws.intake hΖ Q.table_exists p
       apply hy.mono he.aestronglyMeasurable (ae_of_all _ (fun v=> Solos.pend H M y Z i z St p (U y') v))
    refine ⟨hF',?_⟩; unfold K; rw [integral_prod _ hF',← chargedU _ X.B]; refine (team (V' z) i).transition Z (U y') St N.oboe.conduit hX p (hQ.localP _ Z ht hk hm).sails.fullC Q.buys (H.unionP p) (show ground R T Q.halo Z.B p ⊆ H.unionP p from ?_) (ht.symm ▸ hQ.room) hH.laws.intake hΖ Q.table_exists rfl
    rw [show Z.B= _ from hz_b]; exact Subset.rfl

include Hpc hU
set_option maxHeartbeats 200000 in
lemma beyond (hv:(roster p).flags=∅) : ∀ᶠ z in 𝓝 a, Ll.Knows q₂ (fun b=> (team (brand M b) i).picture (vary X (U z)) p W o.a Q.table Q.halo):=by
    have hB : X.B=radiusB x:=congr_arg radiusB hx
    filter_upwards [eventually_all.mpr (fun t=> rollick H χ M y X i N U p a hx hk hF h hp t), Team.gathers X p H N.oboe hx hk hF hv hU hp h] with z he hL
    simp_rw [hL]; unfold Team.grove; simp_rw [show (vary X (U z)).B=radiusB x from hB]; split_ifs
    · let f (s:S.Choices)(p':α):=(team (brand M p') i).cinema ((preps (vary X (U z)) (roster p)).taggedL s) p W o.a Q.table Q.halo (podium S G (ground R T Q.halo (radiusB x) p) (radiusB x))
      apply Ll.pitch; refine Ll.seats _ f fun s _=>?_
      let Z:=(planted X p).taggedL s
      have hh(P:α): f s P=∫ q, (team (brand M P) i).carat St Z (U z) A Q.table p W o.a Q.halo q ∂((F.order G).prod Z.dice):=by
         refine Eq.trans ((team (brand M P) i).casin X p H hx hv hU s (U z) (U z) (fun _ _ _=> rfl)).symm ?_
         rw [← show X.B=_ from hB]; exact (he s P).2 -- choose occurrence radiusB!
      change Ll.Knows _ (fun z=> f s z)
      simp_rw [hh]; exact Ll.meal (fun v=> solar M Ll Hpc y Z i (U z) p St v) (fun v=>(he s v).1)
    exact Ll.nil _
omit a hU h hx hF hk hp
local notation "t'" => Pressure.temp x
-- express Mode on neighborhood in field coordinates, not just each direction independently.
variable {V:Config G c}(p':H.ThinP) (hu:Healthy (Pressure.temp x) (H.smallAt p') V)
include hu
lemma city : ∀ᶠ z in 𝓝 V, Ll.Knows q₂ (fun k=>toe (brand M k) H χ p' i z):=by
    refine Solos.kick j v N.position _ V fun U hx hp=> ?_
    filter_upwards [eventually_all.mpr (fun r:Greenbelt.Reserve S=> beyond H χ M Ll Hpc y (prism T x χ o.K V (allot r)) i N U p'.val 0 rfl rfl rfl hx hp hu p'.prop.2)] with z hz
    apply Ll.pitch; exact Ll.seats _ (fun (a:Greenbelt.Reserve S) b=> (team (brand M b) i).picture (prism T x χ o.K (U z) (allot a)) p'.val W o.a Q.table Q.halo) (fun i _=> hz i)
end YM.RemainderComparison.Collar
