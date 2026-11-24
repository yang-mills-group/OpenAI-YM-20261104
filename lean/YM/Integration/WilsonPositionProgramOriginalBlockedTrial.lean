import YM.Integration.WilsonOriginalNullPlacedFullMatrix
import YM.Extra.SOURCE_HISTORIES.Unit

/-! Guarded canonical trial columns and their complete intrinsic measured matrix
on one blocked physical vacuum. The original cutoff can lie strictly above
the trial's birthday. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 400000
noncomputable section
namespace YM.Integration.WilsonPositionProgramOriginalBlockedTrial
open Function Filter Lattice RG Wilson Extra.Histories Source Labels
open Extra.Histories.Relay Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph MeasureTheory
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato RG05Readout RG05Readout.Address
open WilsonOriginalNullCorridor WilsonOriginalNullPlacedGermMap
open scoped Classical BigOperators Topology
variable {G:Gauge} (R:Run G) (d:ℕ)
local notation "C₀" => R.family
local notation "F₀" => (C₀).labels.level d
local notation "S₀" => (C₀).localSection d

def numerator (N p K:ℕ) (o:Site ((C₀).side K p)) (v:(C₀).label d) : Config G ((C₀).side K p) → ℂ :=
  (primary o v).density o S₀ ((C₀).path.rep N p K)

theorem original_field (N p K:ℕ) (o:Site ((C₀).side K p)) (v:(C₀).label d) (U:Config G ((C₀).side K p)) :
    numerator R d N p K o v U = (((C₀).path.rep N p K).eval U : ℂ)*part S₀ o ((C₀).path.rep N p K) U v :=
  primary_density _ _ _ _

theorem unit (N p K:ℕ) (o:Site ((C₀).side K p)) :
    numerator R d N p K o (F₀).e0 = fun U => ((((C₀).path.rep N p K).eval U):ℂ) :=
  unit_density _ _ _

theorem tested {N p K:ℕ} (live:K ≤ N) (o:Site ((C₀).side K p)) (v:(C₀).label d) :
    Integrable (numerator R d N p K o v) (prior G _) :=
  ((primary o v).envelope S₀ (R.makes.wilson.represents N p K live).good
    (primary_rem (v:=safety C₀ K) v (Real.sqrt_pos.mpr (Real.exp_pos _))) (primary_format (H:=(C₀).params) v)).integrableC _

def carried {N p b n:ℕ} (live:b+n ≤ N) (o:Site ((C₀).side (b+n) p)) :
    (C₀).label d →ₗ[ℂ] (Config G ((C₀).side b p) → ℂ) where
  toFun v:=flow C₀ d N p b n (numerator R d N p (b+n) o v)
  map_add' x y:=by
    have same:numerator R d N p (b+n) o (x+y)=numerator R d N p (b+n) o x+numerator R d N p (b+n) o y:=by
      funext U;simp only [original_field,map_add,Pi.add_apply,mul_add]
    rw [same];exact flow_add C₀ d N p b n _ _ (tested R d live o x) (tested R d live o y)
  map_smul' a x:=by
    have same:numerator R d N p (b+n) o (a • x)=a • numerator R d N p (b+n) o x:=by
      funext U;simp only [original_field,map_smul,Pi.smul_apply,smul_eq_mul];ring
    rw [same];exact WilsonOriginalNullPlacedFlowPanel.scalar C₀ d N p b n a _ (tested R d live o x)

theorem original (simple:G.Simple) (shop:RG05Preconstruction.ReadoutPurchase R.b) {η:ℝ} (η0:0<η):
    ∃ onset:ℕ,∀ b≥onset,∀ N p n,∀ live:b+n ≤ N,∀ y:∀ j,Site ((C₀).side j p),
      (∀ j<n,((C₀).path.levels.clock.op (b+j) p).ratio.parent (y (b+j+1))=y (b+j)) →
      let P:=(C₀).path.rep N p b
      let out:=carried R d live (y (b+n))
      ∃ A:(C₀).label d →ₗ[ℂ] (C₀).label d,
        (∀ v z, Printed C₀ d N p b (y b) z (out v) → A v=projection F₀ (C₀).params P.p.threshold (y b) z) ∧
        ∀ v,let price:=WilsonOriginalNullPlacedCollar.cost R d η b (b+n)*(F₀).coeffSize v
        ∃ z:Coefficient F₀ ((C₀).side b p), z.Format (y b) (C₀).params P ∧
          z.remBound (y b) P (safety C₀ b) price ∧ (F₀).coeffSize z.x ≤ price ∧ z.density (y b) S₀ P=out v:=by
  obtain ⟨s,move⟩:=WilsonOriginalNullPlacedCollar.original R d simple shop η0
  obtain ⟨s₀,openAt⟩:=eventually_atTop.mp (open_late C₀ simple d)
  refine ⟨max s s₀,?_⟩;intro b late N p n live y path P out
  have reads (v:(C₀).label d):=move b ((le_max_left ..).trans late) N p y n live path (primary (y (b+n)) v)
    ((F₀).coeffSize v) (primary_format v)
    (rem_mono (primary_rem _ (Real.sqrt_pos.mpr (Real.exp_pos _))) (Work.G08.size_nonneg ..)) le_rfl
  have words (v:(C₀).label d):∃ z,Printed C₀ d N p b (y b) z (out v):=by
    obtain ⟨z,zf,zp,_,field⟩:=reads v;exact ⟨z,zf,⟨_,zp⟩,field.symm⟩
  obtain ⟨A,measured⟩:=WilsonOriginalNullPlacedGermMap.linear C₀ d N p b (y b) R.makes
    (openAt b ((le_max_right ..).trans late) p) (by omega) out words
  refine ⟨A,measured,?_⟩
  intro v
  obtain ⟨z,zf,zp,head,field⟩:=reads v;exact ⟨z,zf,zp,head,field.symm⟩
end YM.Integration.WilsonPositionProgramOriginalBlockedTrial
end
