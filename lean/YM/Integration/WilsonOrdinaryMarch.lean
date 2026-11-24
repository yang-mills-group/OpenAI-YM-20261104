import YM.Integration.WilsonOrdinaryMarchStep

/-! The fixed observed physical exterior prices follow from a local relative defect of
the actual engineering-grade diagonal on the original consecutively sampled frames. -/

noncomputable section
namespace YM.Integration.WilsonOrdinaryMarch
open Filter Set Spec Climb OPE RG12 RG12.Frames RG17 SharpGram Trace.Pilot
open WilsonOrdinaryGradedShear WilsonOrdinaryMarchAnchor WilsonOrdinaryMarchStep
open scoped Topology BigOperators Classical
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
variable (F : Final C f S) (J : ℝ → PhysMS.tower S) (d : ℕ)
set_option quotPrecheck false
local notation "D" => (Bel C.book).Field d
local notation "V" => Desk.Sector F.sector.derivatives d
local notation "X" => Col V

/-- One numerical charge per adjacent *physical* grade diagonal, before all tested
vectors. It compares two concrete norms from the originally appointed position tower. -/
def DiagonalCost (T : X ≃ₗ[ℂ] D) : Prop :=
  ∃ c : ℝ, 0 ≤ c ∧ ∀ᶠ n : ℕ in atTop, ∀ x : X,
    |‖T (diagonalMap V (step F J d T n).toLinearMap x)‖ - ‖T x‖| ≤
      c/Sample.age n * ‖T x‖

private lemma scalar {a b c s : ℝ} {p : ℕ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hs : 0 < s) (hhalf : 2*c ≤ s) (hp : 2*c ≤ (p:ℝ))
    (h : |b-a| ≤ c/s*a) :
    b ≤ (1+s⁻¹)^p*a ∧ a ≤ (1+s⁻¹)^p*b := by
  let t := c/s
  have ht : 0 ≤ t := div_nonneg hc hs.le
  have half : 2*t ≤ 1 := by
    change 2*(c/s) ≤ 1
    rw [← mul_div_assoc]; exact (div_le_one hs).mpr hhalf
  obtain ⟨lo,hi⟩ := abs_le.mp h
  have up : b ≤ (1+t)*a := by dsimp [t]; linarith only [hi]
  have down : (1-t)*a ≤ b := by dsimp [t]; linarith only [lo]
  have widen : 1 ≤ (1+2*t)*(1-t) := by nlinarith only [mul_nonneg ht (sub_nonneg.mpr half)]
  have budget : 1+2*t ≤ (1+s⁻¹)^p := calc
    1+2*t = 1+(2*c)*s⁻¹ := by dsimp [t]; ring
    _ ≤ 1+(p:ℝ)*s⁻¹ := by gcongr
    _ ≤ _ := one_add_mul_le_pow (by linarith only [inv_pos.mpr hs] : (-2:ℝ) ≤ s⁻¹) p
  refine ⟨up.trans (mul_le_mul_of_nonneg_right ((by linarith only [ht] : 1+t ≤ 1+2*t).trans budget) ha),?_⟩
  calc
    a ≤ ((1+2*t)*(1-t))*a := le_mul_of_one_le_left ha widen
    _ = (1+2*t)*((1-t)*a) := mul_assoc _ _ _
    _ ≤ (1+2*t)*b := mul_le_mul_of_nonneg_left down (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_right budget hb

private lemma age_ratio (i : ℕ) :
    Sample.age (i+1) / Sample.age i = 1+(Sample.age i)⁻¹ := by
  have pos : 0 < Sample.age i := by unfold Sample.age; positivity
  have plus : Sample.age (i+1) = Sample.age i+1 := by unfold Sample.age; push_cast; ring
  rw [plus]; field_simp

/-- All actual original RG12 frame and reading conditions, using the explicit physical
adjustment and the single simultaneous lift on the issued original regulator chart. -/
theorem frames (T : X ≃ₗ[ℂ] D) (P : Pier.Lair.Present F J)
    (O : Prescription F.sector.derivatives) (coh : O.Coherent)
    (align : ∀ᶠ r in trail, triangular V ((Desk.official O coh d).symm.toLinearMap.comp (T.trans (J r d)).toLinearMap))
    (cost : DiagonalCost F J d T) {u : Filter (ℕ×ℕ)} (Q : Lenses.Mantle F u)
    (L : Layout F) (hL : Pegs Q L) (E : Services C f S) :
    FramesInput F.sector.derivatives O coh L.charts d := by
  obtain ⟨K,stable⟩ := WilsonOrdinaryMarchAnchor.stable F J d T
  obtain ⟨c,hc,localCost⟩ := cost
  obtain ⟨p,hp⟩ := exists_nat_ge (2*c)
  obtain ⟨i₀,clock⟩ := Sample.samples_clock (K:=K)
  obtain ⟨i₁,late⟩ := Sample.samples_clock (K:=2*c)
  have usable := WilsonOrdinaryMarchStep.permitted F J d T P O coh align
  have flagged := WilsonOrdinaryDyadicAge.approaching.eventually align
  obtain ⟨n₀,good⟩ := eventually_atTop.mp (usable.and (flagged.and (localCost.and
    ((eventually_ge_atTop i₀).and (eventually_ge_atTop i₁)))))
  let Y := fun i : ℕ => (atSample F J d T i).toLinearMap
  let R := fun (i : ℕ) (y : S.Field d) => ‖(J (Sample.length i) d).symm y‖
  let A := adjustment F J d T
  refine ⟨Y,R,A,K,p,1,n₀,?_,?_⟩
  · refine ⟨fun i _ => Sample.samples_spacing i,fun i hi => clock i (good i hi).2.2.2.1,
      fun i hi => (good i hi).2.1,fun i _ => stable i,fun i hi => (good i hi).1.1,
      fun i hi x => ?_,fun i hi x => ?_⟩
    · simpa only [pow_one] using (good i hi).1.2.1 x
    · have identity := (good i hi).1.2.2 x
      have norm_here : R i (Y (i+1) (dilate (Sample.ratio i) (A i x))) =
          ‖T (diagonalMap V (step F J d T i).toLinearMap x)‖ := by
        rw [←identity]
        simp [R,Y,A,step,atSample,engineeringCoord,Sample.ratio]
      have norm_next : R (i+1) (Y (i+1) x) = ‖T x‖ := by simp [R,Y,atSample]
      dsimp only
      rw [norm_here,norm_next,age_ratio]
      exact scalar (norm_nonneg _) (norm_nonneg _) hc
        (by unfold Sample.age; positivity) (late i (good i hi).2.2.2.2).1 hp ((good i hi).2.2.1 x)
  · obtain ⟨e,Z,hZ⟩ := WilsonOrdinarySampleReader.original F J P Q L hL E V T
    refine ⟨Z,e,?_⟩
    have grows := Next.Rank.Station.hat_rate C.path.levels E.simpleGate
    filter_upwards [hZ,grows.eventually_ge_atTop 1] with k hk hb
    obtain ⟨hread⟩ := hk.2
    have bump : C.path.levels.clock.hatBeta k^e ≤ C.path.levels.clock.hatBeta k^(e+2) :=
      pow_le_pow_right₀ hb (by omega)
    exact ⟨⟨fun x => (hread.look x).trans (mul_le_mul_of_nonneg_right bump (mass_nonneg _ _ _)),
      fun x => (hread.norm x).trans (mul_le_mul_of_nonneg_right bump (norm_nonneg _)),
      fun x => (hread.price x).trans (mul_le_mul_of_nonneg_right bump (norm_nonneg _))⟩⟩

/-- Both literal inequalities on the issued fixed original chart and the appointed
physical quotient, from a local grade defect, using the original logarithmic march. -/
theorem prices (T : X ≃ₗ[ℂ] D) (P : Pier.Lair.Present F J)
    (O : Prescription F.sector.derivatives) (coh : O.Coherent)
    (align : ∀ᶠ r in trail, triangular V ((Desk.official O coh d).symm.toLinearMap.comp (T.trans (J r d)).toLinearMap))
    (cost : DiagonalCost F J d T) {u : Filter (ℕ×ℕ)} (Q : Lenses.Mantle F u)
    (L : Layout F) (hL : Pegs Q L) (E : Services C f S) :
    RightPrice C S L.charts d ∧ ∀ w, RowPrice C S F.sector.derivatives L.charts d w := by
  obtain ⟨Y,R,A,K,p,b,n,hV,Z,e,hZ⟩ := frames F J d T P O coh align cost Q L hL E
  have stops := Sample.enough_stops C E.simpleGate e n
  exact ⟨march_right hV (Sample.atMesh C) stops Z hZ E.simpleGate,fun w =>
    march_row hV (Sample.atMesh C) stops Z hZ E.simpleGate w (fun j _ x => Desk.fits O coh d j x)⟩

end YM.Integration.WilsonOrdinaryMarch
