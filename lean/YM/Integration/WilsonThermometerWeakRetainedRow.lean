import YM.Integration.WilsonThermometerWeakGroupFiling
import YM.Next.RANK.Post

/-! The actual short deposited row, its unmasked reading and its paid long occurrences on
the full original group field. These are the operands of the two-shelf weak comparison. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakRetainedRow
open Function Filter Set MeasureTheory Lattice Wilson RG Source Labels RG12 Extra.Histories
open Next.Rank.Spindle Next.Rank Next.Rank.Edition Configuration Normal Rise Source.Drops
open Function RG Thirst Relation Value Glyph Marker Vac.Numbers Alarm Cells Baler EntryWord
open Value Thirst Atlas Beamer Common LiftMark Perch Glimmer Station Asymptotics MvPolynomial Ribbon Corona
open WilsonThermometerWeakTaylor WilsonThermometerWeakPrimary WilsonThermometerWeakGroupAperture
open scoped Classical Topology BigOperators ContDiff
variable {G:Gauge} {n:Side} {D b:ℕ} {S:Rules G} {P:BudgetPoint}

private theorem masked_sum {ι:Type*} [Countable ι] {X:ι→Support n} {A:ι → Config G n→ℂ} {f:ι→ℂ}
    {r c:ℝ} {L:poly (links G (0:Site n) b)} (h:Summary S P b D X A f r c L)
    {Z:Support n} (inside:∀ i,X i⊆Z) :
    Reliable P.threshold G n (halo 8 Z) (fun U=>∑' i,f i*masked P.threshold (X i) (A i) U) ∧
    Reliable P.threshold G n Z (fun U=>∑' i,f i*A i U) ∧
    ∀ U,Healthy P.threshold Z U→(∑' i,f i*masked P.threshold (X i) (A i) U)=∑' i,f i*A i U := by
  obtain ⟨_,_,T⟩:=h
  refine ⟨⟨?_,?_,?_⟩,⟨?_,?_,?_⟩,?_⟩
  · intro g U;apply tsum_congr;intro i;rw [sails _ _ _ (T.smooth i).symmetry g U]
  · apply Measurable.tsum;intro i;exact measurable_const.mul (masked_measurable _ _ _ (T.smooth i).borel)
  · intro U V hh;apply tsum_congr;intro i;apply congrArg (f i*·)
    exact sail _ _ _ (T.smooth i).sites U V (agrees_mono hh (halo_mono le_rfl (inside i)))
  · intro g U;apply tsum_congr;intro i;rw [(T.smooth i).symmetry g U]
  · apply Measurable.tsum;intro i;exact measurable_const.mul (T.smooth i).borel
  · intro U V hh;apply tsum_congr;intro i;exact congrArg (f i*·) ((T.smooth i).sites _ _ (agrees_mono hh (inside i)))
  intro U hh;apply tsum_congr;intro i;rw [masked_eq _ _ _ _ (hh.mono_left (inside i))]

variable {C:Family G} {d k N p m:ℕ}
local notation "𝔽" => C.labels.level d
local notation "ℙ" => C.path.rep N p k

def unitSlip (x:C.label d) (t:ℝ) (U:Config G n):ℂ:=
  x 0-x 0*masked t {0} (fun _=>1) U

private theorem basis (x:C.label d) (U:Config G (C.side k p)) :
    (∑' j:LA C d,weights C (ℙ).p.threshold x j*
      masked (ℙ).p.threshold (verseX C d k p j) (verseA C d k p j) U)+
        unitSlip (C:=C) x (ℙ).p.threshold U=
      x 0+masked (ℙ).p.threshold ((C.localSection d).footprint 0)
        ((C.localSection d).places ((𝔽).scaled (ℙ).p.threshold⁻¹ ((𝔽).core x)) 0) U := by
  let z:=(𝔽).scaled (ℙ).p.threshold⁻¹ ((𝔽).core x)
  have hz:z=∑ i,z i • Pi.single i 1 := by ext1 i;simp [Pi.single_apply]
  have he:(∑ i,z i*((C.localSection d).places (Pi.single i 1) 0 U))=
      (C.localSection d).places z 0 U := by
    conv_rhs => rw [hz]
    unfold SectionData.places SectionData.evaluate
    rw [map_sum,map_sum];simp_rw [map_smul];rfl
  rw [tsum_fintype,Fintype.sum_sum_type,Fintype.sum_unique]
  change x 0*masked (ℙ).p.threshold {0} (fun _=>1) U+
    (∑ i,z i*masked (ℙ).p.threshold ((C.localSection d).footprint 0)
       ((C.localSection d).places (Pi.single i 1) 0) U)+
    (x 0-x 0*masked (ℙ).p.threshold {0} (fun _=>1) U)=_
  by_cases ok:Healthy (ℙ).p.threshold ((C.localSection d).footprint 0) U
  · simp only [masked_eq _ _ _ _ ok];rw [he];abel
  · simp only [masked_ne _ _ _ _ ok,mul_zero,Finset.sum_const_zero,add_zero];abel

def short (X:Coefficient 𝔽 (C.side k p)) (N m:ℕ) (U:Config G (C.side k p)):ℂ:=
  (∑' j:LA C d,weights C ((C.path.rep N p k)).p.threshold X.x j*
    masked ((C.path.rep N p k)).p.threshold (verseX C d k p j) (verseA C d k p j) U)+
    unitSlip (C:=C) X.x ((C.path.rep N p k)).p.threshold U+(∑' j:Near (P:=(C.path.rep N p k)) X m,X.maskedTerm (C.path.rep N p k) j U)

def unmasked (X:Coefficient 𝔽 (C.side k p)) (N m:ℕ) (U:Config G (C.side k p)):ℂ:=
  (∑' j:LA C d,weights C ((C.path.rep N p k)).p.threshold X.x j*verseA C d k p j U)+
    (∑' j:Near (P:=(C.path.rep N p k)) X m,X.regular j U)

def distant (X:Coefficient 𝔽 (C.side k p)) (N m:ℕ) (U:Config G (C.side k p)):ℂ:=
  ∑' j:Far (P:=(C.path.rep N p k)) X m,X.maskedTerm (C.path.rep N p k) j U

theorem original (K:Provision C d k N p m b) (X:Coefficient 𝔽 (C.side k p))
    (form:X.Format 0 C.params ℙ) {q u v:poly (Up C k p b)} {a e cap cash:ℝ}
    (hq:Summary S (ℙ).p b D (verseX C d k p) (verseA C d k p)
      (weights C (ℙ).p.threshold X.x) a cap q)
    (hu:Summary S (ℙ).p b D (fun j:Near (P:=ℙ) X m=>X.support j) (fun j=>X.regular j)
      (fun _=>1) e cash u)
    (hv:Summary S (ℙ).p b D (fun j:Far (P:=ℙ) X m=>X.support j) (fun j=>X.regular j)
      (fun _=>1) e (expCut (ℙ).p m*cash) v) :
    let t:=(ℙ).p.threshold;let Z:=Spindle.patch b (0:Site (C.side k p))
    Reliable t G _ (halo 8 Z) (short X N m) ∧ Reliable t G _ Z (unmasked X N m) ∧
    (∀ U,Healthy t Z U→short X N m U=unmasked X N m U) ∧
    (∀ U,‖short X N m U‖≤cap+‖X.x 0‖+cash) ∧
    (∀ U,‖distant X N m U‖≤expCut (ℙ).p m*cash) ∧
    ∀ U,X.exponentialEntry 0 (C.localSection d) ℙ U=short X N m U+distant X N m U := by
  intro t Z
  have zi:({0}:Support (C.side k p))⊆Z:=by
    intro j hj;change j∈Spindle.patch b 0;rw [show j=0 from Finset.mem_singleton.mp hj,doors,separation_self];exact Nat.zero_le _
  have si (i:LA C d):verseX C d k p i⊆Z:=by
    cases i with
    | inl _ => exact zi
    | inr _ => change _⊆Spindle.patch b 0;rw [patch_eq];exact Finset.image_subset_image K.footprint
  have inside (j:Near (P:=ℙ) X m):X.support j⊆Z:=by
    intro i hi;change i∈Spindle.patch b 0;rw [doors]
    exact (Corona.extent _ (ℙ).p.B (form.origin _) hi).trans
      ((Nat.add_le_add_right (Nat.mul_le_mul_right _ j.property) _).trans K.cuts)
  obtain ⟨ph,pr,eqp⟩:=masked_sum hq si
  obtain ⟨rh,rr,eqr⟩:=masked_sum hu inside
  simp only [one_mul] at rh rr eqr
  have U0:Reliable t G _ (halo 8 Z) (unitSlip (C:=C) X.x t) := by
    constructor
    · intro g U;unfold unitSlip;rw [sails t {0} (fun _=>1) (fun _ _=>rfl) g U]
    · exact measurable_const.sub (measurable_const.mul (masked_measurable _ _ _ measurable_const))
    · intro U V h;unfold unitSlip;rw [sail t {0} (fun _=>1) (fun _ _ _=>rfl) U V (agrees_mono h (halo_mono le_rfl zi))]
  refine ⟨⟨?_,?_,?_⟩,⟨?_,?_,?_⟩,?_,?_,?_,?_⟩
  · intro g U;exact congrArg₂ (·+·) (congrArg₂ (·+·) (ph.inv g U) (U0.inv g U)) (rh.inv g U)
  · exact (ph.meas.add U0.meas).add rh.meas
  · intro U V h;exact congrArg₂ (·+·) (congrArg₂ (·+·) (ph.locally _ _ h) (U0.locally _ _ h)) (rh.locally _ _ h)
  · intro g U;exact congrArg₂ (·+·) (pr.inv g U) (rr.inv g U)
  · exact pr.meas.add rr.meas
  · intro U V h;exact congrArg₂ (·+·) (pr.locally _ _ h) (rr.locally _ _ h)
  · intro U h;unfold short unmasked unitSlip Coefficient.maskedTerm
    rw [eqp U h,eqr U h,masked_eq t {0} (fun _=>1) U (h.mono_left zi)];simp
  · intro U
    have slip:‖unitSlip (C:=C) X.x t U‖≤‖X.x 0‖:=by
      unfold unitSlip;by_cases h:Healthy t {0} U
      · rw [masked_eq _ _ _ _ h];simp
      · rw [masked_ne _ _ _ _ h];simp
    have near:= (deposit hu U).2;simp only [one_mul] at near
    exact (norm_add_le ..).trans ((add_le_add ((norm_add_le ..).trans (add_le_add (deposit hq U).2 slip)) near))
  · intro U;simpa only [distant,Coefficient.maskedTerm,one_mul] using (deposit hv U).2
  intro U
  let M:Set ℕ:=setOf fun i=>coverNumber (ℙ).p.B (X.support i) ≤ m
  let Z' j:=X.maskedTerm ℙ j U
  have nS:Summable (fun j:Near (P:=ℙ) X m=>Z' j):=by
    simpa only [Z',Coefficient.maskedTerm,one_mul] using (deposit hu U).1.of_norm
  have fS:Summable (fun j:Far (P:=ℙ) X m=>Z' j):=by
    simpa only [Z',Coefficient.maskedTerm,one_mul] using (deposit hv U).1.of_norm
  have exhaust:((∑' j:Near (P:=ℙ) X m,Z' j)+∑' j:Far (P:=ℙ) X m,Z' j)=∑' j,Z' j:=
    Summable.tsum_add_tsum_compl (s:=M) (f:=Z') nS fS
  unfold short distant;rw [basis]
  change _ = _+(∑' j:Near (P:=ℙ) X m,Z' j)+(∑' j:Far (P:=ℙ) X m,Z' j)
  rw [add_assoc,exhaust];rfl

end YM.Integration.WilsonThermometerWeakRetainedRow
end
