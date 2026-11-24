import YM.QuadraticLocal.Arches
import YM.RemainderComparison.Solo.Brink
/-!
# The scalar belonging to the true log alphabet

All torus sizes and arbitrary masks. No positivity of the FULL vacuum;
use the `homestead` furnished and the same `prism`'s data as for Carillon.
Even when porting along actual trajectory we prefer avoiding the `upkeep`
division here. This proves the factor can be known before Mark evaluation.
Powers never reintroduced on log labels unused at the projection.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Lanes
-- Use same M and data throughout. Countable ι handles address combinations per load.
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse PhysicalNext.Repeat Gas
open Coat Matter ProbabilityTheory Poll Pond Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open Itinerary Animals March Captain Greenbelt Stained Ursell Trees Reserves
open Merge Palette Next.Scheduling OmitClusters AnalyticBridge.VerifiedReset
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open RemainderComparison RemainderComparison.Lyric RemainderComparison.Mosaic RemainderComparison.Muse RemainderComparison.Sleet RemainderComparison.Serif RemainderComparison.Typeface RemainderComparison.Flues
open GridRenewal.Rain
open Marker Mallow Ovens Progress.DirectedRecipe
variable {ι V' : Type} {α:Type*}
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Tree.Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ μ x κ w C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (H:Cash W x μ L Q o C T R) {q A B b e u v d L' Gp:ℝ}{j n k s J I:ℕ}(χ:Chi)
variable (U:Pad H j χ) {τ κ K Y γ V T0:ℝ}
variable (M:ι→Portrait R α) (x' y:α) (l:ι→ℝ)
variable (h:Roles H χ U k s J I a d e K σ Y γ V T0) (hh:Motto (brand M x') l 0 H τ K Y I)
local notation "Vx"=> brand M x'
local notation "Vy" => brand M y
variable {R':Rep G f} (H':Cash W x μ L Q o C T R')(D:Match.Alliance H' H 1 0)
    (P':BudgetPoint)(hp : P'.B=radiusB x) (ht:P'.threshold=Pressure.temp x)
    (E₀:ℕ→RegularAddress c)(V₀:ℕ → Config G c→ℝ)
variable [DecidableEq V']{Jm:Marker.Census V'}
local notation "Φ" => Poly Jm
variable (z:ι→Marker.Poly Jm) {gP:V'→ℝ} (hZ : Chorus Jm gP Set.univ z k)
local notation "Z"=> (Set.univ:Set ι)
local notation "F'"=> TuneR (brand M y) Z l 0 z S

namespace Theatre
open RemainderComparison.Solo
local notation "l₀"=> sits Z l 0
-- constrained prices recorded elsewhere; choose only identity-germ conversion here.
variable {tCp dCp qCp:ℝ} {nCp:ℕ}
variable (hR: Cash.Renewed nCp qCp tCp dCp H)
private lemma notesUnique (E:ι→Leaf R)(j:H.fragrances)(u:Syllable E H j) (h: notes E H j u = 0): u=echo E H j:= by
    funext i; apply Subtype.ext; change (u i).val=∅; apply Finset.card_eq_zero.mp; apply Nat.eq_zero_of_le_zero; rw [← h]; exact single_le_sum (f:=fun i=> (u i).val.card) (fun _ _=>Nat.zero_le _) (mem_univ i)
local notation "η"=> brand M y
local notation "φ"=> Serif.glyph (brand M y) H χ Z l 0 z
local notation "ψ"=> Solo.echo η H
include hZ U
lemma reading_unmarked (p : H.fragrances)(w:Syllable η H p)(V':Config G c):
    (φ ⟨p,w⟩ V').part Jm.quiet= if w= ψ p then Complex.ofReal (H.trainedPool χ V' p) else 0:= by
    let k:= (jewel η H χ p w).letters
    by_cases ht' : Lyric.notes η H p w=0
    · rw [notesUnique H η p w ht',if_pos rfl]
      let u := ψ p; have hb: (jewel η H χ p u).letters=0:= Multiset.card_eq_zero.mp (by
         change (etude η H χ p u).letters.card=0; rw [Muse.scores]; exact (Solo.calls η H l p).1)
      have hu : (jewel η H χ p u).utter V'= H.trainedPool χ V' p:= by
         change Lyric.cut η H χ p u V'=_; unfold Lyric.cut; rw [Solo.songs]; exact (congr_fun ((U.S.N.permitAverage p).2.2.2.1) V').symm
      unfold Serif.glyph Verse.paint; rw [Poly.part_smul]; change (↑((jewel η H χ p u).emit l₀ V'):ℂ)* (Verse.controls Z z (jewel η H χ p u).letters).part Jm.quiet =_
      unfold Verse.emit Verse.stock; rw [hb, hu]; simp [Verse.controls]
    rw [if_neg (fun (h:w=ψ p)=> ht' (h.symm ▸ (Solo.calls η H l p).1))]; have ht: k≠0:= fun h=> ht' (((Muse.scores η H χ p w).symm).trans (Multiset.card_eq_zero.mpr h)); have hp (v: Multiset ι) (hv:v≠0) : (Verse.controls Z z v).part Jm.quiet=0:= by
          cases v using Multiset.induction_on with
          | empty=> simp at hv
          | cons i s => simp [Verse.controls,silent z hZ]
    unfold Serif.glyph Verse.paint; rw [Poly.part_smul, hp k ht, mul_zero]
include hZ
local notation "ℓ"=> Syllable η H
lemma roles_one (V:Config G c)(i : H.fragrances): (∑' v:Syllable η H i,(φ (Sigma.mk i v) V).part Jm.quiet) = Complex.ofReal (H.trainedPool χ V i):= by
 simp_rw [reading_unmarked H χ U M y l z hZ]; rw [tsum_ite_eq]
omit hZ U
private lemma tally {α:Type*}(G:Marker.Census V')(v:α→Type*) (f:(i:(Σ i,v i))→Poly G) (hv:Summable f) (z:α→ℝ) (hz: ∀ i:α, (∑' x:v i,(f (Sigma.mk i x)).part G.quiet) = Complex.ofReal (z i)) : (∑' i,f i).part G.quiet = (↑(∑' i,z i):ℂ):= by
    have ht:Summable (fun i=> (f i).part G.quiet):= ((Poly.get G.quiet).summable hv)
    rw [Poly.share hv,(Summable.tsum_sigma ht)]; simp_rw [hz]; rw [Complex.ofReal_tsum]
include U
include hR h hh hZ hp ht
variable (h₁:P'.order≤j)(h₂:P'.power≤J)
set_option maxHeartbeats 600000 in
lemma player (hm: P'.order ≤ j)(hT: P'.power ≤ J)(V:Config G c): let f:= fun i=> φ i V;
        (∑' i,f i).part Jm.quiet=Complex.ofReal (Real.log (H.homesteadPool χ V)):=by
    intro f₁
    have hS:= (Serif.summit (η) H χ Z l 0 U h (Typeface.outputs H M x' y l 0 hh) z hZ P' hp ht hm hT V).1; have hh : Summable f₁:=hS
    rw [(H.threshold_logPool χ V hR).1]
    exact tally Jm (Syllable (η) H) f₁ hh (fun i=> H.trainedPool χ V i) (roles_one H χ U M y l z hZ V)

end Theatre
end YM.QuadraticLocal.Lanes
