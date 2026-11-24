import YM.Integration.HealthyJetTransfer
import YM.RGLocalTaylor.Laminate.Coincidence
import YM.RGLocalTaylor.Mayer.Moment

/-! Exact healthy-mask and aperture identities for retained local insertions
in Lemma qlocal. Every ordered spatial direction, the empty word, all marked
partners and the original two reference tag sums stay attached to the same
Cash and Captain. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ManuscriptQLocalHealthyMoments
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory
open Push Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure
open PhysicalNext PhysicalNext.Repeat Lotus Daisy Greenbelt RGLocalTaylor RGLocalTaylor.Insert
open Blaze.March ConnectedActivityE6.Matter ConnectedActivityE6.Pond
open scoped Topology BigOperators Classical

section masks
variable {G : Gauge} {n : Side} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- An explicit companion on the original flag predicate, with no restriction
on fields outside the selected hull. -/
theorem companion {G : Gauge} {n : Side} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (t : ℝ) {P Q : Support n} (hPQ : P ⊆ Q) (f : Config G n → E) (U : Config G n) :
    masked t P f U = masked t Q f U +
      (if Healthy t P U ∧ ¬Healthy t Q U then f U else 0) := by
  by_cases hQ : Healthy t Q U
  · have hP : Healthy t P U := Finset.disjoint_of_subset_left hPQ hQ
    simp [hP,hQ]
  · by_cases hP : Healthy t P U <;> simp [hP,hQ]

theorem words {a b : ℝ} (hab : a<b) {P : Support n} {F H : Config G n → E}
    (eqn : ∀ U, Healthy b P U → F U=H U) {U : Config G n} (hU : Healthy a P U)
    (l : List (Directions G n)) : leftDerivs F l U=leftDerivs H l U := by
  have chart : Tendsto (increment U) (𝓝 0) (𝓝 U) := by
    have hc : Continuous (increment U) := continuous_pi fun e => by unfold increment; fun_prop
    have atZero := hc.continuousAt (x := 0)
    change Tendsto (increment U) (𝓝 0) (𝓝 (increment U 0)) at atZero
    simpa only [Work.G07.at_zero_increment] using atZero
  have localEq : F =ᶠ[𝓝 U] H := (HealthyJetTransfer.margin hab P hU).mono eqn
  exact Push.Local.left_congr l U (localEq.comp_tendsto chart)

end masks

variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {P : Teller G}
  {j n : ℕ} {R : Rep G f} {η q Y W d C' A b s μ C v B : ℝ}
  {Q : ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi}
  {H : Cash W s μ L Q o C T R} {p : Molecule S}
  (N : Captain H j C' d v Y A b q B η n χ)

private abbrev sectorPrism (_ : Cash W s μ L Q o C T R) (χ : Chi)
    (V : Config G c) (F : Forest S.ratio) := Greenbelt.prism T s χ o.K V F

def measured (I : Insert T) (H : Cash W s μ L Q o C T R) (χ : Chi)
    (p : Molecule S) (V : Config G c) : ℝ :=
  likely fun j:Greenbelt.Reserve S =>
    let X := sectorPrism H χ V (Greenbelt.allot j)
    likely fun k:S.Choices =>
      let A := (planted X p).taggedL k
      ∫ z, I.joint A z ∂Insert.moment A

variable {I : Insert T} (fit : Fits H I (H.unionP p) j) (permit : authorized H p)
  (unflagged : (roster p).flags=∅)

include N fit permit unflagged

theorem accepted (V : Config G c) (hV : Healthy (Pressure.temp s) (H.unionP p) V) :
    I.onLog H χ p V = measured I H χ p V := by
  unfold measured sectorPrism
  refine (fit.exact_meaning (N:=N) V permit unflagged hV).trans ?_
  congr 1
  exact Subsingleton.elim _ _

/-- The two functions coincide even at the discontinuous predicate's
boundary, as full original masked fields. -/
theorem mask : masked (Pressure.temp s) (H.unionP p) (I.onLog H χ p) =
    masked (Pressure.temp s) (H.unionP p) (measured I H χ p) := by
  funext V
  by_cases h : Healthy (Pressure.temp s) (H.unionP p) V
  · simpa only [masked_eq _ _ _ _ h] using accepted N fit permit unflagged V h
  · simp only [masked_ne _ _ _ _ h]

/-- Every Taylor direction at the actual healthy field before averaging,
including the empty list for the original field-independent insertion. -/
theorem retained {a : ℝ} (ha : a<Pressure.temp s) {U : Config G c}
    (hU : Healthy a (H.unionP p) U) (l : List (Directions G c)) :
    leftDerivs (I.onLog H χ p) l U=leftDerivs (measured I H χ p) l U :=
  words ha (accepted N fit permit unflagged) hU l

theorem flat (hs : 0<s) (l : List (Directions G c)) :
    leftDerivs (I.onLog H χ p) l 1=leftDerivs (measured I H χ p) l 1 :=
  retained N fit permit unflagged (Work.E09.temp_pos hs) (Next.Foundations.one_healthy _ _ le_rfl) l

omit fit in
/-- The selected native Team already contains the exact joint signed
insertions and their forced spectral partners under this same mask. -/
theorem team (M : Team R) (he : M.signs S ⊆ p) (U : Config G c) :
    M.lotus T s χ o.K W o.a Q.table Q.halo U p =
      masked (Pressure.temp s) (H.unionP p)
        (measured (Mayer.original H p (p\M.signs S) (Laminate.partner M H)) H χ p) U := by
  rw [Laminate.teamLecturer (M:=M) (H:=H) he U N unflagged,
    mask N (Laminate.fit_original (M:=M) (H:=H) (j:=j) p) permit unflagged]

end YM.Integration.ManuscriptQLocalHealthyMoments
end

