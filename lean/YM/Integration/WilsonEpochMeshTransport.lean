import YM.Integration.WilsonEpochPhysicalStation

/-! Compare the genuinely independently chosen finite meshes using precisely
the same historical position scheme on each side. This also identifies the
exact numerical residual when the regulator sequences cannot coincide. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonEpochMeshTransport
open Function Lattice XSpace XSpace.Normalize XSpace.Cirrus XSpace.Structure1
open FVA2 FVA2.Register FVA2.Arrival MS MS.Land
open WilsonEpochPositionCoefficients
open scoped Classical BigOperators

variable {G : Gauge} (R : PhysicalNext.Repeat.Legato.Run G)

def mesh (c per : ℕ) : Mesh :=
  ⟨⟨R.family.side c per,(ActualOriginalFiniteCoefficients.side_admissible R c per).2,
       (ActualOriginalFiniteCoefficients.side_admissible R c per).1⟩,
    R.family.S.a c,R.family.S.a_pos c⟩

section Arrays
variable (Y : Initialize G) (m : Mesh) {n : ℕ} {d : Fin n → ℕ}
variable (t : (j : Fin n) → Dframe.Toon G (d j)) (x : Fin n → Cover)
private abbrev Source (G : Gauge) := List (Folio G) → PowerSeries ℝ
def position (b : Source G) : PowerSeries ℂ :=
  Dframe.Csum m (fun j => (t j).size) •
    PowerSeries.map Complex.ofRealHom (Birth.scan (Handoff.wordSymbols n t x) b)

def sweep (a : Test n) (b : Source G) : PowerSeries ℂ :=
  (m.spacing : ℂ)^(4*n) • ∑ x : Fin n → m.Sites,
    m.smear (lift ∘ x) a • position m t (lift ∘ x) b

private theorem filed :
    position m t x (Folio.coefficients Y m.p.side) = Y.atTuple m (fun j => (t j).size)
      (wrap m.p.side ∘ x) (fun j => Birth.theory (t j)) := by
  let T := Y.tree m.p
  let A (j : Fin n) := XSpace.On.stencil Y.hol (Y.surveys (t j).size) m.p T
    ((wrap m.p.side ∘ x) j) (Arrival.Birth.theory (t j))
  have he : XSpace.Bare.normalized T G (∏ j : Fin n, A j) =
      PowerSeries.map Complex.ofRealHom
        (Birth.words Y m.p.side (Handoff.wordSymbols n t x)) :=
    Birth.compact_labels Y T Finset.univ x d t
  unfold position
  change _ • PowerSeries.map Complex.ofRealHom (Birth.words Y _ _) = _
  rw [←he,←map_smul,Initialize.atTuple_eq]
  apply congr_arg
  suffices ∀ e : Finset (Fin n), (∏ j∈e,Dframe.Ufee m (t j).size) •
      (∏ j∈e,A j) = ∏ j∈e,Y.atSite m (t j).size ((wrap m.p.side ∘ x) j)
      (Birth.theory (t j)) from this Finset.univ
  intro e
  induction e using Finset.induction_on with
  | empty => simp
  | insert j e hj ih =>
    symm
    rw [Finset.prod_insert hj,Finset.prod_insert hj,Finset.prod_insert hj,←ih]
    rw [Initialize.atSite,LinearMap.smul_apply,←inv_pow,mul_smul,smul_mul_assoc,mul_smul_comm]

private theorem filed_sweep (a : Test n) : sweep m t a (Folio.coefficients Y m.p.side) =
    Y.report m (fun j => (t j).size) a (fun j => Birth.theory (t j)) := by
  unfold sweep
  rw [Initialize.report_formula]
  simp_rw [filed]
  apply congr_arg ((m.spacing:ℂ)^(4*n) • ·)
  refine Finset.sum_congr rfl (fun z _ => ?_)
  rw [show (wrap m.p.side ∘ (lift ∘ z)) = z from funext (fun q => wrap_lift _)]

private theorem separate :
    position m t x (actual R Y m.p.side) =
      position m t x (Folio.coefficients Y m.p.side) +
      position m t x (residual R Y m.p.side) := by
  unfold position
  rw [assembled R Y m.p.side (even_iff_two_dvd.mpr m.p.even),map_add,smul_add]
  rfl

private theorem separate_sweep (a : Test n) : sweep m t a (actual R Y m.p.side) =
    sweep m t a (Folio.coefficients Y m.p.side) + sweep m t a (residual R Y m.p.side) := by
  unfold sweep
  simp_rw [separate,smul_add,Finset.sum_add_distrib]
  exact smul_add _ _ _
end Arrays

variable (Y : Initialize G) (m : Mesh) (n d k : ℕ)
variable (x : Fin n → Cover) (a : Test n) (p : Tags G d n)

def readPoint (b : Source G) : ℂ :=
  ∑ t : Fin n → Dframe.Toon G d, Dframe.each t p * PowerSeries.coeff k (position m t x b)
def readBatch (b : Source G) : ℂ :=
  ∑ t : Fin n → Dframe.Toon G d, Dframe.each t p * PowerSeries.coeff k (sweep m t a b)

/-- The prescribed arrays on an arbitrary native mesh. -/
theorem comparison :
    readPoint m n d k x p (actual R Y m.p.side) =
      litP Y d m (wrap m.p.side ∘ x) k p +
      readPoint m n d k x p (residual R Y m.p.side) ∧
    readBatch m n d k a p (actual R Y m.p.side) =
      XSpace.Normalize.batch Y m d k n a p +
      readBatch m n d k a p (residual R Y m.p.side) := by
  constructor
  · let v : Sample n := ⟨m,x,0⟩
    have he (t : Fin n → Dframe.Toon G d) : live Y d v k (Dframe.fill t) =
        PowerSeries.coeff k (position m t x (Folio.coefficients Y m.p.side)) := by
      rw [filed Y]
      exact lives Y d v (j:=fun j => (t j).size) (fun j => Birth.theory (t j))
        (fun j => Dframe.size_le (t j)) k
    change readPoint m n d k x p _ = live Y d v k p + _
    rw [Dframe.stencil_he (live Y d v k) p]
    simp only [readPoint,separate,map_add,mul_add,Finset.sum_add_distrib,he]
  · have he (t : Fin n → Dframe.Toon G d) :
        XSpace.Normalize.batch Y m d k n a (Dframe.fill t) =
        PowerSeries.coeff k (sweep m t a (Folio.coefficients Y m.p.side)) := by
      rw [filed_sweep Y]
      exact indicated Y m (L:=fun j => ⟨(t j).size,Nat.lt_add_one_iff.mpr (Dframe.size_le (t j))⟩)
        (fun j=>Birth.theory (t j)) a k
    rw [Dframe.stencil_he (XSpace.Normalize.batch Y m d k n a) p]
    simp only [readBatch,separate_sweep,map_add,mul_add,Finset.sum_add_distrib,he]

/-- No common period or common mesh hypothesis. All original complex
multi-tests and both complete, distinct smearing sums appear in the
remaining regulator difference. -/
theorem booked {hG : G.Simple} (Z : WilsonPrescription G)
    {T : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}
    {S : Prescription (Press.portDeck G)} {dial : Bool} (M : Main.Match Z hG T S dial)
    (c per i B n d k : ℕ) (P : Handoff.Directory Z i B)
    (h : Handoff.Directory.budget G n d + k ≤ B)
    (x : Fin n → Cover) (a : Test n) (p : Tags G d n) (ν : ℝ) :
    let m := mesh R c per
    let z := Z.run.step i
    (readPoint m n d k x p (actual R Z.scheme m.p.side) -
      (∑ t : Fin n → Dframe.Toon G d, Dframe.each t p * PowerSeries.coeff k (P.point_fk n d t x)) =
      readPoint m n d k x p (residual R Z.scheme m.p.side) +
        (litP Z.scheme d m (wrap m.p.side ∘ x) k p - litP Z.scheme d z (wrap z.p.side ∘ x) k p)) ∧
    (readBatch m n d k a p (actual R Z.scheme m.p.side) -
      (∑ t : Fin n → Dframe.Toon G d, Dframe.each t p * PowerSeries.coeff k (P.sweep_fk n d a t)) =
      readBatch m n d k a p (residual R Z.scheme m.p.side) +
        (XSpace.Normalize.batch Z.scheme m d k n a p - XSpace.Normalize.batch Z.scheme z d k n a p)) ∧
    O.Canon.Supplied Z T ν := by
  intro m z
  obtain ⟨pointed,smeared⟩ := comparison R Z.scheme m n d k x a p
  obtain ⟨oldPoint,oldBatch⟩ := M.batchFromEpochFk i B P d k n x a p h
  refine ⟨?_,?_,M.separatedOPE ν⟩
  · rw [pointed,←oldPoint]
    abel
  · rw [smeared,←oldBatch]
    abel

end YM.Integration.WilsonEpochMeshTransport
end
