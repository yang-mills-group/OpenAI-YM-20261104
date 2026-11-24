import YangMills.WilsonProof.NativeSupport.PacketPath

/-! Finite-volume endpoint comparison. The terminal freight is the actual
stock tape, and the endpoint may have any layer-homogeneous real offsets.
Every whole word is read under the same normalized path measure. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.InletSusceptibility.Packet
open Function Finset MeasureTheory Lattice RG Wilson Marker
open MergeProof MergeProof.Accent Extra.Multi Extra.Trajectories RGComparison.Core16 RGGapR2
open WilsonUniformUnmarkedInletConnectedCovariance
open scoped Classical BigOperators
variable {G : Gauge} {V H : Type} [Fintype V] [Fintype H] [DecidableEq V] [DecidableEq H]

abbrev stockTape (A : History G) (N per k : ℕ) (hk : k ≤ N)
    (F : V → Config G (A.S.side N per) → ℝ) :=
  gust A N per N (birth (Stock.census V) (A.rep N per N) (fun i U=>(F i U : ℂ))) k hk

theorem separated_endpoint [Nonempty H] (A : History G) (selected : A.Selected) {N per k : ℕ}
    (T : Slices A.levels per) (hk : k ≤ N) (g : V → H)
    (F : V → Config G (A.S.side N per) → ℝ) (cont : ∀ i,Continuous (F i))
    (sym : ∀ i,GaugeInvariant (F i)) (unit : ∀ i U,|F i U| ≤ 1)
    (W : Config G (A.S.side N per) → ℝ) (contW : Continuous W) (symW : GaugeInvariant W)
    (unitW : ∀ U,|W U| ≤ 1) (shift : H → Site (A.S.side k per))
    (copies : ∀ j U,word g F j U = W (pull 1 (liftSite (traversal T hk) (shift j)) U))
    (o : V → Site (A.S.side k per)) (inj : Injective o) (m L : ℕ)
    (fibres : ∀ j,(fibre g j).card ≤ m)
    (apart : ∀ i j,g i≠g j → 2*(A.rep N per k).p.B+4*(2*(A.rep N per k).p.B+1)*L
      < separation (o i) (o j)) (posL : 0 < L)
    {a ρ A₀ D η ε : ℝ} (hA : 0 ≤ A₀) (hD : 0 ≤ D) (radius : Real.exp (-A₀) ≤ ρ)
    (exponent : 1 ≤ a) (space : m*A₀+D ≤ L)
    (tape : Rough.Freight (A.rep N per k) (Stock.census V) (stockTape A N per k hk F)
      o (fun _=>ρ) a 1)
    (v : ℕ → ℝ) (top : v (traversal T hk).depth=0) (hη : 0 ≤ η)
    (offset : ∀ j, 0<j → j<(traversal T hk).depth → |v j| ≤ η)
    (hε : 0 < ε) (small : ε ≤ 1/4)
    (budget : (Fintype.card V : ℝ)*Real.exp (-2*D) +
      2*(((traversal T hk).depth*((A.S.side N per).val^4*4) : ℕ) : ℝ)*
        (η*(A.levels.clock.kernel.penalty*2)) ≤ (Fintype.card H : ℝ)*ε^2) :
    let d := traversal T hk
    let β := RGComparison.Core16.line A per k N
    let Y := WilsonUniformUnmarkedInletSignedResponse.line β v 1
    |mean d Y W 1 - mean d β W 1| ≤ 3*ε := by
  intro d β Y
  let X := stockTape A N per k hk F
  let B := Stock.census V
  let P := ((X 1).part B.quiet)⁻¹ • X 1
  let C : ℝ := (d.depth*((A.S.side N per).val^4*4) : ℕ)
  let n : ℝ := Fintype.card (Site (A.S.side k per))
  let K : ℝ := Fintype.card H
  let fee : ℝ := Fintype.card V * Real.exp (-2*D)
  let w := mean d β W 1
  let y := mean d Y W 1
  let f (U : Config G (A.S.side N per)) := ∑ j,word g F j U
  have ok := traversal_ok T hk
  have hn : 0<n := by dsimp [n]; positivity
  have hK : 0<K := by dsimp [K]; positivity
  have hw := mean_unit d ok β 1 contW unitW
  have wordC (j : H) := word_cont g F cont j
  have fC : Continuous f := continuous_finsetSum _ fun j _=>wordC j
  have ub (J : Finset V) (U : Config G (A.S.side N per)) : |∏ i∈J,F i U| ≤ 1 := by
    rw [abs_prod]
    exact prod_le_one (fun _ _=>abs_nonneg _) (fun i _=>unit i U)
  have eqWord (β' : ℕ→ℝ) (j : H) : mean d β' (word g F j) 1 = mean d β' W 1 := by
    have symj : GaugeInvariant (word g F j) :=
      fun h U => prod_congr rfl fun i _=>sym i h U
    rw [show word g F j=fun U=>W (pull 1 (liftSite d (shift j)) U) from funext (copies j)] at symj ⊢
    exact translate_mean T hk (shift j) W contW β' symW symj
  have means (β' : ℕ→ℝ) : mean d β' f 1 = K*mean d β' W 1 := by
    change mean d β' (fun U=>∑ j,word g F j U) 1=_
    rw [mean_sum d ok β' 1 (word g F) wordC]
    simp [eqWord,K]
  have coeff (J : Finset V) : P.part (tag J)=
      ((mean d β (fun U=>∏ i∈J,F i U) 1 : ℝ) : ℂ) :=
    calibrated_submoment A selected T hk B F cont sym (tag J) 1
  have mom (J : Finset V) : ‖P.part (tag J)‖ ≤ 1 := by
    rw [coeff,Complex.norm_real,Real.norm_eq_abs]
    exact mean_unit d ok β 1 (continuous_finsetProd _ fun i _=>cont i) (ub J)
  have full (j : H) : P.part (tag (fibre g j))=(w : ℂ) :=
    (coeff _).trans (congrArg Complex.ofReal (eqWord β j))
  have mgf (s : ℝ) (hs : |s| ≤ 1/4) :
      Real.log (mass d β (fun U=>Real.exp (s*f U)) 1) - Real.log (mass (G:=G) d β 1 1)
        ≤ fee+K*(2*s^2+s*w) := by
    have term := terminal_word (A.rep N per k) X g o inj m L fibres apart posL hA hD
      radius exponent space (selected.represents N per k hk).good.labels tape P rfl mom full hw hs
    rw [physical_reader A selected T hk g F cont sym 1 s,Complex.norm_real,Real.norm_eq_abs] at term
    exact log_mgf d ok β 1 (word g F) wordC (fun j U=>ub (fibre g j) U) hw hs ((le_abs_self _).trans term)
  have one (s : ℝ) (hs : |s| ≤ 1/4) :
      K*(s*(y-w)) ≤ fee+K*(2*s^2)+2*C*(η*(A.levels.clock.kernel.penalty*2)) := by
    have e := intensive_response T hk β v top hη offset 1 fC s
    change s*(mean d Y f 1-mean d β f 1)/n ≤
      (Real.log (mass d β (fun U=>Real.exp (s*f U)) 1)-Real.log (mass (G:=G) d β 1 1)-s*mean d β f 1)/n+
      2*(C/n)*(η*(A.levels.clock.kernel.penalty*2)) at e
    rw [means Y,means β] at e
    let a := Real.log (mass d β (fun U=>Real.exp (s*f U)) 1)-Real.log (mass (G:=G) d β 1 1)
    change s*(K*y-K*w)/n ≤ (a-s*(K*w))/n+2*(C/n)*(η*(A.levels.clock.kernel.penalty*2)) at e
    have paid : a ≤ fee+K*(2*s^2+s*w) := mgf s hs
    have cross := mul_le_mul_of_nonneg_right e hn.le
    field_simp [hn.ne'] at cross
    linarith
  have bill : fee+2*C*(η*(A.levels.clock.kernel.penalty*2)) ≤ K*ε^2 := budget
  have pos := one ε (by simpa only [abs_of_pos hε] using small)
  have neg := one (-ε) (by simpa only [abs_neg,abs_of_pos hε] using small)
  have scale : 0<K*ε := mul_pos hK hε
  apply abs_le.mpr
  constructor
  · apply (mul_le_mul_iff_of_pos_left scale).mp
    change K*ε*(-(3*ε)) ≤ K*ε*(y-w)
    linarith
  apply (mul_le_mul_iff_of_pos_left scale).mp
  change K*ε*(y-w) ≤ K*ε*(3*ε)
  linarith

end YM.Integration.InletSusceptibility.Packet
