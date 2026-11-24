import YM.Integration.WilsonMaxwellThermometerWardCredit

/-! The earned equation, including its actual incoming numerical multiplier,
has a zero vacuum charge and a zero first pole within the cleared inversion
measurement. Preserve every separated spectator in the real normalized law. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerWardOccupant
open Function Filter Set MeasureTheory Lattice Wilson RG Labels Source Push
open Next.Extract MergeProof PhysicalNext.Repeat.Legato PertExtension PertExtension.Orb
open WilsonOffsetEquationLaw WilsonMaxwellThermometerWardConditional WilsonMaxwellThermometerWardReflection
open WilsonMaxwellThermometerWardOrbitStation WilsonMaxwellThermometerWardPupil
open scoped Classical Topology BigOperators
variable {G:Gauge}

def currency (R:Run G) {d:ℕ} (W:Mark.Weave G) (N:ℕ) (v:Label G d)
    : (R.family.labels.level d).Coeff :=
  ((R.family.S.a N:ℂ)^d)⁻¹ • (R.family.labels.level d).coords (W d v)

theorem placed (R:Run G) {d:ℕ} (C:SectionData (R.family.labels.level d))
    (W:Mark.Weave G) (N:ℕ) (v:Label G d) {n:Side} (o:Site n):
    C.places (currency R W N v) o = field R C W N v ∘ expandAt o :=by
  funext U
  unfold SectionData.places field currency
  simp [SectionData.evaluate,map_smul]

theorem original (R:Run G) (V:∀d,SectionData (R.family.labels.level d)) (W:Mark.Weave G)
    (P:∀d,(ℕ×ℕ)→(R.family.label d≃ₗ[ℂ] R.family.label d)) (b:Presentation R.family)
    (portfolio:∀d,Mark.Portfolio R.family.params (V d) (W d))
    (issued:Hearthside R.family V W P b (Bandage.fly R.alloy.B.a)) (simple:G.Simple) :
    ∀d,∃r M:ℕ,∀N p (x:R.family.label d),∃v∈Maxwell.equationIdeal G d,
      (∀o:Site (R.family.side N p),
        incoming R.family (V d) N p (P d (N,p)) (x-b.step d (N,p) x) o =
          (V d).places (currency R W N v) o) ∧
      ∀ {n:Side}, Even n.val → M≤n.val → ∀o:Site n, 2*r+4<separation o (-o) →
        (∀ e:Edge (Site n), e.1∈(V d).footprint o → e.1+step e.2∈(V d).footprint o →
          far r o (reflect e)) → ∀L:ℂ→L[ℝ]ℝ,
        let c:=currency R W N v
        L (c 0)=0 ∧
        diagonalWith (tray G) (restrictedO (selected (V d) c L o (next (F:=R.family.labels.level d)))) 2=0 ∧
        ∀{T:Set (Site n)} {K:Config G n→ℝ}, Continuous K → LocalOn T K →
          (∀e:Edge (Site n),e.1∈T→e.1+step e.2∈T→far r o e ∧ far r o (reflect e)) →
          ∀s:ℝ,s≠0→preExpectation
            (fun U=>selected (V d) c L o (active (F:=R.family.labels.level d)) U * K U) s=0 :=by
  intro d
  obtain ⟨r,M,election⟩:=WilsonMaxwellThermometerWardOrbitStation.original R V W P b portfolio issued d
  refine ⟨r,M,?_⟩
  intro N p x
  obtain ⟨v,hv,literal,hearing⟩:=election N p x
  refine ⟨v,hv,fun o=>(literal o).trans (placed R (V d) W N v o).symm,?_⟩
  intro n even cut o span clear L
  let c:=currency R W N v
  have hear {T:Set (Site n)} {K:Config G n→ℝ} (hk:Continuous K) (ks:LocalOn T K)
      (hr:∀e:Edge (Site n),e.1∈T→e.1+step e.2∈T→far r o e ∧ far r o (reflect e)) (s:ℝ) (hs:s≠0):
      preExpectation (fun U=>L ((V d).places c o U)*K U) s=0 :=by
    apply WilsonMaxwellThermometerWardCredit.normalize ((V d).continuous_places _ o) hk L
    rw [show (V d).places c o = _ from placed R (V d) W N v o]
    apply hearing even cut o span clear (Complex.continuous_ofReal.comp hk) _ hr s hs
    intro U X law
    exact congrArg ((↑):ℝ→ℂ) (ks U X law)
  have paid (s:ℝ) (hs:s≠0):preExpectation (fun U=>L ((V d).places c o U)) s=0:=by
    simpa using hear (T:=∅) (K:=fun _=>1) continuous_const (fun _ _ _=>rfl)
      (by simp) s hs
  obtain ⟨credit,ground⟩:=WilsonMaxwellThermometerWardCredit.ground (V d) c L o
    (portfolio d).valid (portfolio d).pays even simple paid
  refine ⟨credit,ground,?_⟩
  intro T K hk ks hr s hs
  have equality (U:Config G n) : selected (V d) c L o (active (F:=R.family.labels.level d)) U =
      L ((V d).places c o U):=by
    rw [WilsonMaxwellThermometerWardPupil.literal (V d) c L o (portfolio d).valid,credit,zero_add]
  change preExpectation (fun U=>selected (V d) c L o (active (F:=R.family.labels.level d)) U * K U) s=0
  simp_rw [equality]
  exact hear hk ks hr s hs

end YM.Integration.WilsonMaxwellThermometerWardOccupant
