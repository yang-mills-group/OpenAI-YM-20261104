import YM.QuadraticLocal.Germ.Justice
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
open WickReps Flues Progress.DirectedRecipe
-- callbacks at ANY footprint ANY test value. For model receipts need OWN shutter.Still open
variable (y:α)(l:ι→ℝ)(Z:Set ι)(ε:ℝ)
variable (N:Captain H j q d v u A b r B e n χ)
local notation "t'" => Pressure.temp x
local notation "Vy"=> brand M y
local notation "A₀"=> Creek.theater H χ M y l Z ε
local notation "L↑"=> Muse.sits Z l ε
include Hpc N
set_option maxHeartbeats 200000 in
lemma vacant (V:Config G c)(i:Sleet.Staff (brand M y) H) (hp:Healthy (Pressure.temp x) (reachability (H:=H) i.fst) V): ∀ᶠ z in 𝓝 V,Ll.Knows (((etude Vy H χ i.1 i.2).letters)) (fun b=> ∏ j,toe (brand M b) H χ (i.1.2 j) (i.2 j) z):=by

    have hz(j): Healthy t' (H.smallAt (i.1.2 j)) V:= hp.mono_left (subset_biUnion_of_mem (H.smallAt ∘ i.1.2) (mem_univ j))
    filter_upwards [eventually_all.mpr (fun j=> city H χ M Ll Hpc y (i.2 j) N (i.1.2 j) (hz j))] with x hx
    let P j:=(i.2 j).val.val; let F j (v:α):=toe (brand M v) H χ (i.1.2 j) (i.2 j) x
    have he : ((etude Vy H χ i.1 i.2).letters)=∑ j,P j:=rfl
    rw [he]; exact Ll.stack Finset.univ P F (fun j _=> hx j) 
omit N Hpc in
lemma arming(i: Sleet.Staff (brand M y) H)(P':α)(V:Config G c) : ((A₀).solvent P' i V)=(etude Vy H χ i.1 i.2).stock L↑ * Lyric.string (brand M P') H χ i.1 i.2 V:=by
    -- definal maneuvers force pol type
    unfold Creek.theater; dsimp only; unfold Verse.emit;
    rw [show (etude (brand M P') H χ i.1 i.2).stock L↑=(etude Vy H χ i.1 i.2).stock L↑ from congr_arg ((fun q:Multiset ι=> (q.map L↑).prod)) (Creek.paper H χ M y P' l Z ε i).symm]; rfl
set_option maxHeartbeats 200000 in
lemma dew (V:Config G c)(i:Sleet.Staff (brand M y) H) (hp:Healthy (Pressure.temp x) ((A₀).halls i) V): ∀ᶠ z in 𝓝 V,Ll.Knows (((A₀).marks i)) (fun b=> (A₀).solvent b i z):=by
    rw [Creek.point H χ M y l Z ε _] at hp
    have hz:=vacant H χ M Ll Hpc y N V i hp
    refine hz.mono fun x hx=> ?_
    have hQ: (A₀).marks i=(etude Vy H χ i.1 i.2).letters:= Creek.paper H χ M y y l Z ε i
    simp_rw [fun p:α=> arming H χ M y l Z ε i p x]; rw [hQ]; unfold Lyric.string
    exact Ll.pitch _ (Ll.pitch _ hx)
lemma scene (V:Config G c) (p:H.Chapter) (s:Mosaic.Stone (brand M y) H p) : Ll.Knows (( (panel Vy H χ p s).letters)) (fun b=>(Mosaic.panel (brand M b) H χ p s).utter V):=by
    cases p with
    | inl p => exact act_h H χ M Ll Hpc y s p.val V
    | inr p =>
        let S:Sleet.Staff Vy H:=⟨p,s⟩
        -- with LT=1 get value. Inspect.Ev flags
        change Ll.Knows _ (fun b=> -Lyric.cut (brand M b) H χ p s V)
        let f b j:=act (brand M b) H χ V (p.2 j).val (s j)
        have he(b:α): -Lyric.cut (brand M b) H χ p s V= -cadence H p*∏ j,f b j:= by rw [← Lyric.scripted (brand M b) H χ p s N V,neg_mul] -- edit args
        simp_rw [he]; apply Ll.pitch
        let P j:= (s j).val.val; have hz : ((panel Vy H χ (.inr p) s).letters)= ∑ j, P j:=rfl
        rw [hz]; exact Ll.stack univ P (fun i b=>f b i) (fun j _=>act_h H χ M Ll Hpc y (s j) (p.2 j).val V) 
lemma lush (V:Config G c) (p:H.Chainbook)(s:Mosaic.Scene (brand M y) H p): Ll.Knows ((parade Vy H χ p s).letters) (fun b=> (parade (brand M b) H χ p s).emit l V):=by
    let f:=fun (i:↥p.fst) (j:Slots H p i)=> (Mosaic.panel Vy H χ i.val (s i j)).letters
    have he (w:α)(i:H.Chapter)(j:Stone Vy H i): (Mosaic.panel (brand M w) H χ i j).letters=(Mosaic.panel Vy H χ i j).letters:=by cases i<;> rfl
    have hz (i:↥p.fst) (j:Slots H p i) : Ll.Knows ((f i j)) (fun b=> (Mosaic.panel (brand M b) H χ i.val (s i j)).emit l V):=by unfold Verse.emit Verse.stock; simp_rw [he]; exact Ll.pitch _ (scene H χ M Ll Hpc y N V i.val (s i j))
    have hs : ((parade Vy H χ p s).letters)=∑ i,∑ j,(f i j):= rfl
    simp_rw [fun b:α=> Mosaic.wheel (brand M b) H χ l p s V]; split_ifs
    · rw [hs]; apply Ll.stack; intro i _; simp_rw [div_eq_inv_mul]; exact Ll.pitch _ (Ll.stack univ _ _ (fun j _=> hz i j))
    exact Ll.nil _
variable [Countable ι]
variable {R':Rep G f} (H':Cash W x μ L Q o C T R')(D:Match.Alliance H' H 1 0)(P':BudgetPoint) (E₀:ℕ→RegularAddress c)(V₀:ℕ → Config G c→ℝ)
local notation "K'" => kettle H χ M y l Z ε H' D E₀ V₀
local notation "Ω" => Flues.funnel H M y H' D
lemma radiant (i:ℕ)(V:Config G c): Ll.Knows (((K').score i)) (fun b=> (K').glow b i V) := by
    by_cases hi:i∈ Set.range Ω
    · obtain ⟨j,rfl⟩:=hi; unfold Flues.kettle; dsimp only; simp_rw [Progress.DirectedRecipe.stuffed]
      exact lush H χ M Ll Hpc y L↑ N V _ j.snd
    unfold kettle; dsimp only; simp_rw [Progress.DirectedRecipe.blank Ω _ hi]; apply Ll.nil
end YM.RemainderComparison.Collar
