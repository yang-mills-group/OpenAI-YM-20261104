import YangMills.WilsonProof.NativeSupport.PacketCrossPrice
import YangMills.WilsonProof.NativeSupport.CalibratedRead
import YangMills.WilsonProof.NativeSupport.EndpointPrice

/-! Reading complete (possibly disconnected) physical words in the normalized
terminal polynomial agrees with the original positive tagged path integral. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.InletSusceptibility.Packet
open Function Finset MeasureTheory Lattice RG Wilson Marker
open MergeProof MergeProof.Accent Extra.Multi Extra.Trajectories RGComparison.Core16
open WilsonUniformUnmarkedInletConnectedCovariance
open scoped Classical BigOperators

variable {V H : Type} [Fintype V] [Fintype H] [DecidableEq V] [DecidableEq H]
variable {G : Gauge} {n c : Side}

def word (g : V → H) (F : V → Config G n → ℝ) (j : H) (U : Config G n) :=
  ∏ i∈fibre g j,F i U

omit [Fintype H] [DecidableEq V] in
theorem word_cont (g : V → H) (F : V → Config G n → ℝ) (hF : ∀ i, Continuous (F i)) (j : H) :
    Continuous (word g F j) := continuous_finsetProd _ fun i _=>hF i

omit [Fintype H] in
private theorem product_word (g : V → H) (F : V → Config G n → ℝ) (J : Finset H) (U : Config G n) :
    ∏ j∈J,word g F j U = ∏ i∈liftSet g J,F i U := by
  have lift : liftSet g J = J.biUnion (fibre g) := by
    ext i
    simp [liftSet,fibre]
  rw [lift,prod_biUnion]
  · rfl
  intro i _ j _ ne
  exact disjoint_left.mpr fun z a b=>ne ((mem_filter.mp a).2.symm.trans (mem_filter.mp b).2)

private theorem expand_word (g : V → H) (F : V → Config G n → ℝ) (s : ℝ) (U : Config G n) :
    ∏ j, (1+s*word g F j U) =
      ∑ J ∈ (univ : Finset H).powerset, s^J.card * ∏ i∈liftSet g J,F i U := by
  simp_rw [add_comm (1 : ℝ),prod_add]
  apply sum_congr rfl
  intro J _
  simp [prod_mul_distrib,product_word]

private theorem mass_combination {ι : Type*} (I : Finset ι) (d : Descent n c)
    (ok : d.OK G) (β : ℕ → ℝ) (Z : Config G c) (a : ι → ℝ)
    (F : ι → Config G n → ℝ) (cont : ∀ i∈I,Continuous (F i)) :
    mass d β (fun U=>∑ i∈I,a i*F i U) Z = ∑ i∈I,a i*mass d β (F i) Z := by
  simp only [mass,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro t _
  simp_rw [←integral_const_mul]
  rw [←integral_finsetSum I (fun i hi=>(d.path_integrable ok β t (F i) (cont i hi) Z).const_mul _)]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [Descent.integrand,mul_sum]
  apply sum_congr rfl
  intro i _
  ring

theorem physical_reader (A : History G) (selected : A.Selected) {N per k : ℕ}
    (T : Slices A.levels per) (hk : k ≤ N) (g : V → H)
    (F : V → Config G (A.S.side N per) → ℝ) (cont : ∀ i,Continuous (F i))
    (sym : ∀ i,GaugeInvariant (F i)) (Z : Config G (A.S.side k per)) (s : ℝ) :
    let d := traversal T hk
    let B := Stock.census V
    let β := RGComparison.Core16.line A per k N
    let X := gust A N per N (birth B (A.rep N per N) (fun i U=>(F i U : ℂ))) k hk Z
    read g s ((X.part B.quiet)⁻¹ • X) =
      ((mass d β (fun U=>∏ j, (1+s*word g F j U)) Z / mass d β 1 Z : ℝ) : ℂ) := by
  intro d B β X
  let I := (univ : Finset H).powerset
  let h (J : Finset H) (U : Config G (A.S.side N per)) := ∏ i∈liftSet g J,F i U
  have ex := mass_combination I d (traversal_ok T hk) β Z (fun J=>s^J.card) h
    (fun J _=>continuous_finsetProd _ (fun i _=>cont i))
  have same : (fun U=>∏ j, (1+s*word g F j U)) = fun U=>∑ J∈I,s^J.card*h J U :=
    funext (expand_word g F s)
  rw [same,ex,sum_div,Complex.ofReal_sum]
  unfold read
  refine sum_congr rfl fun J _=>?_
  rw [calibrated_submoment A selected T hk B F cont sym (tag (liftSet g J)) Z]
  simp only [Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_pow,h]
  ring

end YM.Integration.InletSusceptibility.Packet
