import YM.Integration.WilsonOriginalNullWord
import YM.QuadraticLocal.Glow
import YM.MergeProof.Jetty

/-! Sum the actual finite source assignments of each individual outgoing cluster. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalNullFiniteTap
open Function Filter Set Lattice RG Pressure Tree Wilson Finset MeasureTheory
open PhysicalNext Repeat Legato Graces
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork Roof Daisy Charity Rain Roost Lotus Blush Mallow
open UVNext.CouplingReset Animals Marlin Progress.DirectedRecipe Ovens Ovens.Pipes
open Extra.Histories Next.Foundations Labels Peak Mercury
open AllOrder AllOrder.Transit WheelP AllOrder.Floe
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

open Merge Merge.Palette
variable {G : Gauge} (R : Run G) {N per i : ℕ}
    (Ψ : ∀ j, RG.Rep G (R.family.side j per))

open Marker RemainderComparison RemainderComparison.Lyric RemainderComparison.Mosaic
open RemainderComparison.Serif MergeProof.Accent

theorem term (live : i < N)
    (S : Mallow.Spring R.kit N i per 0 0 (fun _ => Ψ (i+1)))
    {I V : Type} [Fintype I] [Fintype V] [DecidableEq V]
    (C : Marker.Census V) (rows : I → Lotus.Leaf (Ψ (i+1))) (w : I → ℝ)
    (σ : I → Poly C) (v : V → ℝ) {k : ℕ}
    (hw : ∀ j, 0 ≤ w j)
    (hσ : Chorus C v Set.univ σ k) (hblank : ∀ j, (σ j).part C.quiet = 0) :
    let K := Mallow.houseS S WilsonOriginalNullHouse.point
    ∀ z : K.fragrances, ∀ U : Config G (R.family.side i per), ∀ a : V,
      (Mosaic.poem rows K Chi.canonical Set.univ w σ z U).part (C.fire a) =
        ∑ j, ((w j * RG.masked (Pressure.temp (R.alloy.B.a.clock.hatBeta i))
          (K.bookFoot (.inr z)) (matin (rows j) K z Chi.canonical) U : ℝ) : ℂ) *
          (σ j).part (C.fire a) := by
  intro K z U a
  have stage := step_paid R.alloy.B.a i
  have ticket := R.b.r _ _ (R.alloy.B.valid.pays i) _ stage |>.1.2
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, cap, _⟩ :=
    ticket _ _ _ _ (Opera.protocol R.alloy.B live R.kit.pledging.conducts.full (n:=per)) _ _ K
  have hwave (t : ℝ) (s : Finset I) :
      Verse.wave Set.univ w t s = Palette.ways w t s := by
    classical
    funext j
    by_cases hj : j ∈ s <;> simp [Verse.wave, Verse.roll, Switch.click, Palette.ways, hj]
  have hmed : Mosaic.med rows K Chi.canonical Set.univ w z U =
      Palette.song rows K Chi.canonical w z U := by
    funext t s
    unfold Mosaic.med Verse.opera
    rw [hwave]
    exact (Mosaic.canon rows K Chi.canonical cap _ z U).symm
  have made : Switch.sound σ (Mosaic.med rows K Chi.canonical Set.univ w z U) =
      Mosaic.poem rows K Chi.canonical Set.univ w σ z U := by
    unfold Mosaic.poem
    simp_rw [← Verse.tones _ Set.univ w σ hσ.square]
    let term i := Mosaic.jewel rows K Chi.canonical z i
    rw [show Mosaic.med rows K Chi.canonical Set.univ w z U =
      ∑ j : Syllable rows K z,(term j).opera Set.univ w U from by ext; simp [Mosaic.med,term]]
    exact Switch.summed σ Finset.univ _ _ (fun j _ => Switch.Paid.toPoint _
      (Verse.earns _ Set.univ w (Mosaic.kronor rows K w z j)
        ((norm_nonneg _).trans (Mosaic.drinks rows K Chi.canonical cap w hw z j U))
        (Mosaic.drinks rows K Chi.canonical cap w hw z j)) U)
  rw [← made, hmed]
  let c := Palette.song rows K Chi.canonical w z U 0 ∅
  let base := Photo.tones rows K Chi.canonical w z U
  have hsplit : Palette.song rows K Chi.canonical w z U = base + (fun _ _ => c) := by
    funext t s
    simp [base, c, Photo.tones]
  have base_model := ((podE K rows U Chi.canonical z).1 w).choose_spec
  have fix_model := ((Switch.constant (ι:=I) (fun _ : Unit => c) (norm_nonneg c)
    (fun _ => le_rfl)).works ()).choose_spec
  have added : Switch.sound σ (base + fun _ _ => c) =
      Switch.sound σ base + Switch.sound σ (fun _ _ => c) :=
    Switch.add_sounds σ base_model fix_model
  rw [hsplit, added, Switch.const_sounds]
  change ((Switch.sound σ base).part (C.fire a) + (Poly.bead C c).part (C.fire a)) = _
  have zero : (Poly.bead C c).part (C.fire a) = 0 := by
    change (Poly.send C.quiet (↑c : ℂ)).part (C.fire a) = 0
    simp [Poly.part_send, C.fire_hot a]
  rw [zero, add_zero, quality (fun _ : Unit => base) σ () a hblank]
  simp_rw [show ∀ j : I, Switch.jet base {j} = w j * RG.masked _ _ _ U from
    fun j => WilsonOriginalNullWord.grouped R Ψ live S rows w j z U]
  rfl

open RemainderComparison.Muse RemainderComparison.Sleet
private lemma single_sum {V : Type} [Fintype V] [DecidableEq V] {C : Marker.Census V}
    {A : Type*} {B : A → Type*} [∀ i, Fintype (B i)] (f : (i : Sigma B) → Poly C)
    (h : Summable f) (v : V) :
    (GridRenewal.Rain.fresh (∑' i, f i)).part (C.fire v) =
      ∑' a, ∑ b, (f ⟨a,b⟩).part (C.fire v) := by
  let φ := Poly.get (C.fire v)
  have hs : Summable (fun i => (f i).part (C.fire v)) := (φ.hasSum h.hasSum).summable
  have drop : (GridRenewal.Rain.bead C ((∑' i, f i).part C.quiet)).part (C.fire v) = 0 := by
    change (Poly.send C.quiet _).part (C.fire v) = 0
    simp [Poly.part_send, C.fire_hot v]
  change (∑' i, f i).part (C.fire v) - (GridRenewal.Rain.bead C ((∑' i, f i).part C.quiet)).part (C.fire v) = _
  rw [drop,sub_zero,Poly.share h,hs.tsum_sigma]
  exact tsum_congr fun i => tsum_fintype _
theorem original (live : i < N)
    (S : Mallow.Spring R.kit N i per 0 0 (fun _ => Ψ (i+1)))
    {I V : Type} [Fintype I] [Fintype V] [DecidableEq V]
    (C : Marker.Census V) (rows : I → Lotus.Leaf (Ψ (i+1))) (w : I → ℝ)
    (σ : I → Poly C) (v : V → ℝ) {k : ℕ}
    (hw : ∀ j, 0 ≤ w j)
    (hσ : Chorus C v Set.univ σ k) (hblank : ∀ j, (σ j).part C.quiet = 0)
    (U : Config G (R.family.side i per))
    (funded : Summable (fun j => Serif.glyph rows (Mallow.houseS S WilsonOriginalNullHouse.point)
      Chi.canonical Set.univ w 0 σ j U)) :
    let K := Mallow.houseS S WilsonOriginalNullHouse.point
    ∀ a : V,
      (GridRenewal.Rain.fresh (∑' j, Serif.glyph rows K Chi.canonical Set.univ w 0 σ j U)).part
        (C.fire a) =
        ∑' z : K.fragrances, ∑ j, ((w j * RG.masked (Pressure.temp (R.alloy.B.a.clock.hatBeta i))
          (K.bookFoot (.inr z)) (matin (rows j) K z Chi.canonical) U : ℝ) : ℂ) *
          (σ j).part (C.fire a) := by
  intro K a
  have weights : Muse.sits Set.univ w 0 = w := by
    funext j; simp [Muse.sits,Verse.marked]
  rw [single_sum _ funded]
  refine tsum_congr fun z => ?_
  have merged := term R Ψ live S C rows w σ v hw hσ hblank z U a
  rw [← merged]
  unfold Mosaic.poem
  rw [Poly.part_sum]
  apply Finset.sum_congr rfl
  intro j _
  unfold Serif.glyph
  rw [weights]

end YM.Integration.WilsonOriginalNullFiniteTap
