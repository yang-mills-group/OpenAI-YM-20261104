import YM.MS.Graphical.Block
import YangMills.WilsonProof.NativeSupport.YM.MS.Graphical.Sector
import YangMills.WilsonProof.NativeSupport.YM.MS.Graphical.Lines
import YM.MS.Image.Globe

/-!
# Prepare and minimally subtract a connected scale sector

This is a forest prescription in which nodes can pay for a **sum** over
slots/internal states. Use renormalized children (but still at the
same dimensional z); the sum of amplitudes including the counterterm
insertions is read under the integral. A counterterm vertex itself goes on
*loop index zero*. This and the different scale exponents and loop measures
at different page indices are essential; for example adding a pure pole to
the very page `ℓ>0` it came from is not OK.

Here is a convenient form of sector MS subtraction. No need to split this step
down into amplitudes with particular internal state assignments.
At the node, use all the counterterm insertions from the children and do the
analytic integration in the length of **this** line (`Sector.lean`). Use
principal part of the result at `y=s=0`, summed over pages. `selectCT` below
does just this Laurent coefficient extraction on graph integrals (in `z`),
including the counterterm minus sign.
Add that counterterm (negative of the PP) as a local vertex
(for marked, a marked vertex).
Thus the renormalized amplitude of *this sector family* is also a sum. This defines
a scale-ordered subtraction, not the prescription of multiplying pole parts
of overlapping momentum graphs. Later, higher nodes never use only the tree of
bare vertices when there is a proper pole; `V` and `W` in `bridgeForce` are
the sums with the pole pages included. This also holds in `closeForce`.

We prove among other things that the resulting sum (`Parade` of pages in the
filed conventions) has holomorphic germ at **every** log mass parameter and
finite positive IR length, and that the subtraction is genuinely local. Here
use the iterated endpoint integration of our sector prescription (see `Sector`).
For realizing the products with counterterm insertions by simultaneous cutoff,
see `Spinneys` and `SectorsAtCut`.

Lean guide to two different senses of dimension: `ClockD ... r` carries a cap
`r` on *external field list length* (in the germ), not `m`, number of extra pairs
of axes used to test the tensor! All statements about analytic
subtraction here are on actual z germs, *before* restricting to the physical
space of axis readings, and include all the auxiliary spaces `SectorP m`.
`height h` (bulk 4) sets allowed Taylor degrees. All computations are in fixed
conventions for the regulator and field weights, not just after projection.
-/

set_option autoImplicit false
noncomputable section
namespace YM.MS.Graphical
open Filter Set Function Finset MeasureTheory
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color
open _root_.YM.MS.Shine Hem Mell Pearl Train Signal Book Convolve Garment.Wick Dock
open scoped Topology ContDiff Interval Classical

variable {G : Gauge} {V X F H : Flats G} {k m n h ℓ : ℕ} {z : ℂ} {f p : Coat G} {b : Bool}
    {q r t : ℤ}


lemma scaleIntegral_zero_input (h ℓ : ℕ) (s : ℝ) (z : ℂ) :
    scaleIntegral ℓ h s z (0 : Mob G) = 0 := by
  have he t : cutIntegral ℓ h s t z (0 : Mob G) = 0 := by
    ext; simp [cutIntegral, scalingShell_eq, ←cert, analyticTail, tad0]
  ext m w
  apply (show Tendsto (fun t => cutIntegral ℓ h s t z (0 : Mob G) m w) atBot (𝓝 0) from ?_
    ).limUnder_eq
  simp_rw [he]; exact tendsto_const_nhds

lemma integrateShell_page (V : Flats G) (h j : ℕ) (z : ℂ) :
    integrateShell h V j z = scaleIntegral j h 0 z (V j z) := by
  unfold integrateShell
  rw [Finsupp.sum_apply, Finsupp.sum, Finset.sum_apply]; by_cases hj : j ∈ V.support
  · rw [Finset.sum_eq_single j]
    · rw [Finsupp.single_eq_same]
    · intro b hb H; rw [Finsupp.single_eq_of_ne (Ne.symm H)]; rfl
    exact fun H => (H hj).elim
  rw [Finsupp.notMem_support_iff.mp hj, Pi.zero_apply, scaleIntegral_zero_input]
  refine Finset.sum_eq_zero fun i hi=>?_ ; rw [Finsupp.single_eq_of_ne (show j ≠ i from fun hz=> hj (hz.symm ▸ hi))]; rfl

/-- Apply the UV limit (fixed IR length and all child results prepared). Also
justifies the scale-one normalisation of the output. Usually used with V the
ordered bridge or cycle force. -/
theorem integrateShell_removal (hv : ClockD b q r V) (ht : Return V 0 h) (ℓ : ℕ) :
    ∀ᶠ z in dotty, ∀ s y, (∀ m, ∀ w : Legs (Shore G m),
        Tendsto (fun cut => weight z ℓ y * cutIntegral ℓ h s cut z (V ℓ z) m w)
          atBot (𝓝 (hikeP z h ℓ y s (integrateShell h V ℓ z) m w))) ∧
        hikeP z h ℓ y s (integrateShell h V ℓ z) = weight z ℓ y • scaleIntegral ℓ h s z (V ℓ z) := by
  filter_upwards [removal (V ℓ) ((hv ℓ).fine.tune.mer.price) h ℓ (fun he => he.symm ▸ ht)] with i hi
  intro s y
  have he : hikeP i h ℓ y s (integrateShell h V ℓ i) = weight i ℓ y • scaleIntegral ℓ h s i (V ℓ i) := by
    rw [integrateShell_page,hikeP,(hi 0).2, (hi s).2,posing]
  rw [he]
  exact ⟨fun m w => ((hi s).1 m w).const_mul _, rfl⟩

private lemma integrateShell_eq_wheels (hv : ClockD b q r V) (ht : Return V 0 h) :
    Pact (wheels V h) (integrateShell h V) := by
  intro ℓ; filter_upwards [removal (V ℓ) ((hv ℓ).fine.tune.mer.price) h ℓ
    (fun he => he.symm ▸ ht)] with i hi; rw [loopy, integrateShell_page, (hi 0).2, posing]

lemma return_congr (hF : Pact F V) (hp : Return F f h) : Return V f h := by
  unfold Return; filter_upwards [hp,hF 0] with i hi H; simpa only [← H] using hi

lemma integrateShell_clock (hv : ClockD b q r V) (ht : Return V 0 h) :
    Vibe h (integrateShell h V) V ∧ ClockD b q r (integrateShell h V) ∧
    Return (integrateShell h V) 0 h := by
  obtain ⟨h0,h1,h2⟩ := scooter hv ht
  obtain H := integrateShell_eq_wheels hv ht
  exact ⟨vibe_trans h0 H (fun _ => EventuallyEq.rfl), clockWind h1 H, return_congr H h2⟩





theorem poleBound_valid (ht : Merg X) : Rent X (poleBound X) := by
  unfold poleBound; rw [dif_pos (tallP ht)]; exact Nat.find_spec _

lemma counterterm_mint (ht : Merg X) (h : ℕ) : selectCT h X = -Mint (poleBound X) X := by
  unfold selectCT Mint; congr 1; apply Finset.sum_congr rfl; intro i hi
  congr 1; simpa only [posing,add_zero] using
    (chosen (n := i) (press_pick (poleBound_valid ht) h 0 0)).symm

/-- The Pole and the renormalized family realize `Dock.Joint`: the inhomogeneous
length-flow law (`advance`), finiteness of the sum of pages with their scale factors
at every `y,s` (`toll`), meromorphic and pure pole conditions, pole homogeneity,
and the UV boundary of the zeroth page. No discarding evanescent tensors!
For the pole equal to its local Taylor projection see `ct_polynomial`.
`hv` is on the input *forced* coefficient (`V`) (see `Diagram.ordered`). -/
theorem block (hv : Coal b h q r V) :
    let R := integrateRen h V
    Joint h V R.pages 0 R.ct ∧ ClockD b q r R.pages ∧ Cap0 b q r R.ct := by
  intro R
  let X := integrateShell h V
  let u := poleBound X
  obtain ⟨H,hJ,hB⟩ : Vibe h X V ∧ ClockD b q r X ∧ Return X 0 h :=
    integrateShell_clock hv.eye hv.force
  obtain hb := poleBound_valid (Moony.toast (clockMoon hJ)); change Rent X u at hb
  have hm := mintCap hJ hb
  have hh := minted_home hb H hv.real
  have he : R.ct = -Mint u X := counterterm_mint (Moony.toast (clockMoon hJ)) _
  have hp : R.pages = X-Finsupp.single 0 (Mint u X) := by
    change X + Finsupp.single 0 R.ct = _
    rw [he, Finsupp.single_neg, sub_eq_add_neg]
  rw [hp, he]
  have hX : ClockD b q r (X-Finsupp.single 0 (Mint u X)) :=
    fun i => (hJ i).sub (Cap0.heap.single hm 0 i)
  refine ⟨{advance := ?_, toll := correspondent hb H hv.real, wet := Moony.toast (clockMoon hX),
           ice := (cone G).neg_mem (minted _ X), back := fun i=>(hh i).neg,
           worth := hm.neg.fine.tune.mer, sip := ?_}, hX, hm.neg⟩
  · simpa only [sub_zero] using vibe_sub H (vibe_root hh)
  simpa only [sub_eq_add_neg] using sip_sub hB (sip_root hh)

lemma ct_polynomial (hv : Coal b h q r V) (z : ℂ) :
    (integrateRen h V).ct z = Tad ((integrateRen h V).ct z) h := by
  let X := integrateShell h V
  obtain ⟨H,M,Xf⟩:= block hv
  apply Home.complete (H.back z); rw [show (integrateRen h V).ct = -Mint (poleBound X) X from
    counterterm_mint (Moony.toast (clockMoon (integrateShell_clock hv.eye hv.force).2.1)) _]
  rw [Pi.neg_apply]
  have ht : Merg X := Moony.toast (clockMoon (integrateShell_clock hv.eye hv.force).2.1)
  have hh := Mint_price (poleBound_valid ht) z
  simpa only [neg_one_smul] using (cost_k hh (-1))

lemma stay_congr (hx : Stay h F) (hp : Pact F X) : Stay h X :=
  fun y t => Live.congr (hx y t) (Train.prom hp h t y)

lemma coal_congr (hx : Coal b h q r F) (hp : Pact F H) : Coal b h q r H :=
  ⟨clockWind hx.eye hp, stay_congr hx.real hp, return_congr hp hx.force⟩

theorem close_coal (hx : ClockD b q r V) (hp : Stay h V) :
    Coal b h q (r-2) (closeForce V) :=
  coal_congr (mine hx hp) (pact_sym (closeForce_eq V (clockMoon hx)))

theorem bridge_coal (hF : ClockD b 0 q F) (hf : Gang b 4 0 F)
    (hX : ClockD b t r X) (hx : Gang b h t X) : Coal b h t (q+r-2) (bridgeForce F X) := by
  rw [bridgeForce_eq]; obtain ⟨k,H,h0,h1⟩ := feed hf hx
  rw [zero_add] at H
  exact ⟨fun i=> ⟨(H i).fine, capA (clockCap hF) (clockCap hX) (reverse_a G 0) i⟩,h0,h1⟩

end YM.MS.Graphical
