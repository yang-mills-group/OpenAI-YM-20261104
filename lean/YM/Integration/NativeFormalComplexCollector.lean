import YM.Integration.NativeFormalRegulatorCollector

/-! The complex coefficient read from the two native finite-regulator
tests at the same paid stamp converges to the selected Wilson panel. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.NativeFormalComplexCollector

open Function Filter Lattice Labels Precision RG PhysicalNext.Repeat.Legato
open RegulatorIR RegulatorIR.FVAAlt2 RegulatorIR.FVAAlt2.Moving
open MS MS.Local.Physical MS.Menus MS.Land FVA2 FVA2.Verne FVA2.ColorCode FVA2.ArchTurn
open FormalOPE.RG10.Position NativeFormalSharedCoupling NativeFormalPrescriptionAgreement
open WilsonLimitConstruction.FundedFormalEconomy NativePhysicalFieldMatrix NativeFormalRegulatorCollector
open RG11.Jets PowerSeries
open scoped Classical Topology

variable {G : Gauge} {R : Run G} {hG : G.Simple}

abbrev rotate {I : Type*} (v : YM.FVAAlt2.Home.Datum I) :=
  NativeFormalComplexReadout.scale (-Complex.I) v

def panel (W : Bank R hG) (μ : ℝ) {k : ℝ} (J : PositionX.Bend.Booth k (warehouse R).F)
    (X : Pic.pass (warehouse R) hG W.data J) (d : ℕ) (v : Datum R.family.labels d) :=
  (toComplex (NativeFormalFieldTransition.relative W μ (Forge.transfer (warehouse R) W.data J μ X) d)).act
    (series (Forge.Check (warehouse R) W.data J μ X) d) v

private theorem original_phase (W : Bank R hG) (μ : ℝ) (d : ℕ) (v : Datum R.family.labels d) :
    part imag (series (Pic.marked (warehouse R) W.data μ) d v) =
      part real (series (Pic.marked (warehouse R) W.data μ) d (rotate v)) := by
  apply PowerSeries.ext
  intro n
  rw [component, component, series, coeff_mk, series, coeff_mk, Pic.payMark]
  change (Spring.ms (warehouse R) W.data μ d n v.1.n v.1.test
      (FormalOPE.RG10.Position.deck R.family.labels d ∘ v.2)).im =
    (Spring.ms (warehouse R) W.data μ d n v.1.n (-Complex.I • v.1.test)
      (FormalOPE.RG10.Position.deck R.family.labels d ∘ v.2)).re
  rw [NativeFormalComplexReadout.invoice]
  simp

private theorem rotate_act {I : Type*} [Fintype I] (c : Change ℝ I)
    (a : YM.FVAAlt2.Home.Datum I → PowerSeries ℝ) (v : YM.FVAAlt2.Home.Datum I) :
    c.act (fun w => a (rotate w)) v = c.act a (rotate v) := by
  unfold Change.act PertExtension.Position.insert
  rfl

theorem phase (W : Bank R hG) (μ : ℝ) {k : ℝ} (J : PositionX.Bend.Booth k (warehouse R).F)
    (X : Pic.pass (warehouse R) hG W.data J) (d : ℕ) (v : Datum R.family.labels d) :
    part imag (panel W μ J X d v) = readout W μ J X d (rotate v) := by
  rw [panel, readout, NativeFormalFieldTransition.selected W μ J X d v,
    NativeFormalFieldTransition.selected W μ J X d (rotate v),
    ← part_transform imag _ _ (NativeFormalFieldTransition.moving_good W μ d).ruler.base,
    ← part_transform real _ _ (NativeFormalFieldTransition.moving_good W μ d).ruler.base]
  simp_rw [original_phase W μ d]
  exact rotate_act (NativeFormalFieldTransition.moving W μ d)
    (fun w => part real (series (Pic.marked (warehouse R) W.data μ) d w)) v

theorem quadratures (W : Bank R hG) (μ : ℝ) {k : ℝ} (J : PositionX.Bend.Booth k (warehouse R).F)
    (X : Pic.pass (warehouse R) hG W.data J) (d n : ℕ) (v : Datum R.family.labels d) :
    coeff n (panel W μ J X d v) =
      ⟨coeff n (readout W μ J X d v), coeff n (readout W μ J X d (rotate v))⟩ := by
  apply Complex.ext
  · exact (component real _ n).symm
  · exact (component imag _ n).symm.trans (congrArg (coeff n) (phase W μ J X d v))

theorem limits (W : Bank R hG) (μ : ℝ) {k : ℝ} (J : PositionX.Bend.Booth k (warehouse R).F)
    (X : Pic.pass (warehouse R) hG W.data J) {d p : ℕ}
    (E : ℕ → Datum R.family.labels d → PowerSeries ℝ)
    (h : ∀ v, YM.FVAAlt2.Moving.Budget.Nice p atTop (fun j => E j v) (readout W μ J X d v))
    (n : ℕ) (hn : n ≤ p) (v : Datum R.family.labels d) :
    Tendsto (fun j => Complex.mk (coeff n (E j v)) (coeff n (E j (rotate v))))
      atTop (𝓝 (coeff n (panel W μ J X d v))) := by
  rw [quadratures W μ J X d n v]
  exact Complex.equivRealProdCLM.symm.continuousAt.tendsto.comp
    ((h v n hn).prodMk_nhds (h (rotate v) n hn))

/-- Multilinear extension on the original complex physical field space. -/
def fields {F : Frames G} {d n : ℕ} (v : Fin n → Pert.Position.E F d)
    (a : (Fin n → FormalOPE.RG10.Position.Deck F d) → ℂ) : ℂ :=
  ∑ w, a w * ∏ i, (FormalOPE.RG10.Position.deck F d).repr (v i) (w i)

theorem fields_exact {F : Frames G} {d a : ℕ} (P : Panel F) (φ : Test a) (n : ℕ)
    (v : Fin a → Pert.Position.E F d) :
    fields v (fun w => coeff n (series P d ⟨⟨a, φ⟩, w⟩)) = P.lives d n a φ v := by
  let L := P.lives d n a φ
  let b := FormalOPE.RG10.Position.deck F d
  symm
  calc
    _ = L (fun i => ∑ j, b.repr (v i) j • b j) :=
      congrArg L (funext fun i => (b.sum_repr (v i)).symm)
    _ = ∑ w : Fin a → FormalOPE.RG10.Position.Deck F d,
        L (b ∘ w) * ∏ i, b.repr (v i) (w i) := by
      rw [MultilinearMap.map_sum]
      exact Finset.sum_congr rfl fun w _ => (MultilinearMap.map_smul_univ ..).trans (mul_comm ..)
    _ = _ := by simp only [fields, series, coeff_mk, L, b]

theorem limits_fields (W : Bank R hG) (μ : ℝ) {k : ℝ} (J : PositionX.Bend.Booth k (warehouse R).F)
    (X : Pic.pass (warehouse R) hG W.data J) {d p : ℕ}
    (E : ℕ → Datum R.family.labels d → PowerSeries ℝ)
    (h : ∀ v, YM.FVAAlt2.Moving.Budget.Nice p atTop (fun j => E j v) (readout W μ J X d v))
    (n : ℕ) (hn : n ≤ p) (τ : PertExtension.Physical.Profile) (u : Fin τ.n → Pert.Position.E R.family.labels d) :
    Tendsto (fun j => fields u (fun w => Complex.mk (coeff n (E j ⟨τ,w⟩)) (coeff n (E j (rotate ⟨τ,w⟩)))))
      atTop (𝓝 (fields u (fun w => coeff n (panel W μ J X d ⟨τ,w⟩)))) := by
  apply tendsto_finsetSum
  intro w _
  exact (limits W μ J X E h n hn ⟨τ,w⟩).mul_const _

def Converges (W : Bank R hG) (μ : ℝ) {k : ℝ} (J : PositionX.Bend.Booth k (warehouse R).F)
    (X : Pic.pass (warehouse R) hG W.data J) (P : Prescription (nativeDeck R))
    (Z : branches R) (C : Lodge.Contract R (program R) Z) (A : table R) (p : ℕ) (g : G.ColorIndex) : Prop :=
  let t := schedule Z C p
  let ht := above Z C p
  ∃ (F : Calibration.Tent ((C.profile (program R) Z R t ht).entire))
    (x : ℕ → Lattice.Cover) (Λ : ℕ → ℕ),
    Supplier.Funding (program R) Z R C t ht atTop P A p g W.native.2 μ F ∧
    Supplier.Walk (program R) Z R C t ht μ P p atTop x F Λ ∧
    ∀ (I : Type) [Fintype I] [DecidableEq I] (i : I) (S : Marker.Census I),
      Nonempty (ProgramT.Stamp (program R) Z R C t ht F p x S i) ∧
      ∀ (B : ProgramT.Stamp (program R) Z R C t ht F p x S i) (d n : ℕ) (_ : n ≤ p),
        let E := fun j u => ProgramT.Matter (program R) Z R C t ht F p Λ x S i B A j d u
        (∀ v : Datum R.family.labels d,
          Tendsto (fun j => Complex.mk (coeff n (E j v)) (coeff n (E j (rotate v)))) atTop
            (𝓝 (coeff n (panel W μ J X d v)))) ∧
        ∀ (τ : PertExtension.Physical.Profile) (u : Fin τ.n → Pert.Position.E R.family.labels d),
          Tendsto (fun j => fields u (fun w => Complex.mk (coeff n (E j ⟨τ,w⟩)) (coeff n (E j (rotate ⟨τ,w⟩)))))
            atTop (𝓝 (fields u (fun w => coeff n (panel W μ J X d ⟨τ,w⟩))))

theorem of_real (W : Bank R hG) (μ : ℝ) {k : ℝ} (J : PositionX.Bend.Booth k (warehouse R).F)
    (X : Pic.pass (warehouse R) hG W.data J) (P : Prescription (nativeDeck R))
    (Z : branches R) (C : Lodge.Contract R (program R) Z) (A : table R) (p : ℕ) (g : G.ColorIndex)
    (h : NativeFormalRegulatorCollector.Converges W μ J X P Z C A p g) :
    Converges W μ J X P Z C A p g := by
  obtain ⟨F, x, Λ, hF, hW, hB⟩ := h
  refine ⟨F, x, Λ, hF, hW, ?_⟩
  intro I _ _ i S
  obtain ⟨hn, h⟩ := hB I i S
  refine ⟨hn, ?_⟩
  intro B d n hp
  exact ⟨limits W μ J X _ (h B d) n hp, limits_fields W μ J X _ (h B d) n hp⟩

def Supported (W : Bank R hG) (μ : ℝ) : Prop :=
  let V := warehouse R
  ∃ (P : Prescription (wings G)) (S : Blaze.ExactSpin V P) (U : Frost.Trusted P)
    (k : ℝ) (J : PositionX.Bend.Booth k V.F) (X : Pic.pass V hG W.data J)
    (Z : branches R) (C : Lodge.Contract R (program R) Z) (D : Drivers)
    (L : Patience (Study.Plan R) D) (A : table R),
    Atoll.Main.Economy hG V W.book W.data P S U J ∧
    MovingOn R (NativeFormalDeckAgreement.moving_deck R) (angular W.book V) W.data P ∧
    YM.FVAAlt2.Mass.Framed (Study.Plan R) L A ∧
    ∀ p : ℕ, 0 < p → ∀ g : G.ColorIndex,
      Converges W μ J X (castPrescription (NativeFormalDeckAgreement.moving_deck R) P) Z C A p g

theorem purchased (W : Bank R hG) (μ : ℝ) : Supported W μ := by
  obtain ⟨P, S, U, k, J, X, Z, C, D, L, A, E, h, hf, pay⟩ := NativeFormalRegulatorCollector.purchased W μ
  exact ⟨P, S, U, k, J, X, Z, C, D, L, A, E, h, hf,
    fun p hp g => of_real W μ J X _ Z C A p g (pay p hp g)⟩

theorem at_penalty (hG : G.Simple) {ε : ℝ} (hε : 0 < ε) :
    ∃ (R : Run G) (W : Bank R hG), R.family.path.levels.clock.kernel.penalty = ε ∧ Run.Ties R ∧
      (∀ a : Extraction.Order, ∃ (b : Extraction.Order) (T : Table R.family.book),
        Nonempty (Spec.Final R.family (a.refine b) T)) ∧ ∀ μ : ℝ, Supported W μ := by
  obtain ⟨R, W, he, ht, hf, _⟩ := NativeFormalRegulatorCollector.at_penalty hG hε
  exact ⟨R, W, he, ht, hf, purchased W⟩

end YM.Integration.NativeFormalComplexCollector
end
