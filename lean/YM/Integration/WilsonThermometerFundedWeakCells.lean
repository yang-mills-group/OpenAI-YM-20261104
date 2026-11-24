import YM.Integration.WilsonThermometerWeakEquationCost

/-! All seven displaced thermometer faces compared to candidates in their original Wilson equation classes. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonThermometerFundedWeakCells
open Function Filter Set Table Spec Extraction OPE OPE.Orbits Climb Trace Trace.Pilot Next.UVStress
open Lattice Wilson RG PhysicalNext.Repeat.Legato RG17 PhysMS PhysMS.Frame Maxwell XSpace XSpace.Normalize
open Labels Source Bid Cells Push FullVolume MergeProof Next.Extract Extra.Histories XSpace.Rose
open WilsonPositionThermometerCapStation WilsonPositionCapTransport WilsonPositionThermometerGradedReading
open WilsonPositionThermometerGradedSource WilsonPositionCorrectedCap
open PhysicalNext.Repeat Legato Bandage
open scoped Topology Classical BigOperators
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {T : Table R.family.book}
variable (F : Final R.family f T) (J : ℝ → tower T) (V : Store G)
    {H : (Bel R.family.book).Hierarchy} {l : Ultrafilter (ℕ × ℕ)} (A : ℝ → Group R.family 6)
open WilsonThermometerMarchProduct (field)

open WilsonThermometerMarchTerminalWatch (upper)
open RG05Readout.Address WilsonThermometerOffsetTrajectory
open scoped BigOperators
def degree (i : Fin 3) : ℕ := (grade i).val

def candidate {k N p : ℕ} (Z : Group R.family 6) (h : k≤N) (s : Badge)
    (Q : (i : Fin 3) → Emblems R.family (degree i))
    (y : (i : Fin 3) → Palette R.family (degree i)) (i : Fin 3) :=
  if i∈s then WilsonThermometerWeakEquationCost.column R (p:=p) (Q i) h (y i)
  else field Z N p s i

theorem occupied (Z : Group R.family 6) (N p : ℕ) (s : Badge) (i : Fin 3) (hi : i∈s) :
    field Z N p s i=field Z N p Finset.univ i := by
  simp only [field,vector,WilsonPositionThermometerGradedSource.source,hi,Finset.mem_univ,if_true]

def extra (y : (i : Fin 3) → Palette R.family (degree i)) := 2*∑ i,size (y i)

theorem original (simple : G.Simple) (paid : Book (f:=f) (l:=l) (H:=H) A J) (lead : Leading F J)
    (E : ∀ d, SectionData (R.family.labels.level d)) (W : Mark.Weave G)
    (P : ∀ d, (ℕ × ℕ) → R.family.label d ≃ₗ[ℂ] R.family.label d) (b : Presentation R.family)
    (portfolio : ∀ d, Mark.Portfolio R.family.params (E d) (W d))
    (house : Hearthside R.family E W P b (Bandage.fly R.alloy.B.a)) :
    ∃ (radius : ℕ → ℕ) (start : ℕ), ∀ᶠ r in trail, let Z:=adjusted F J V A r
      ∀ k₀≥start,
      ∀ᶠ k : ℕ in atTop, ∃ M : Badge → ℝ, (∀ s,0≤M s) ∧ ∀ᶠ z : ℕ × ℕ in f.fuse, ∃ h : k≤z.1, ∃ h₀ : k₀≤z.1,
      ∀ (s : Badge) (m : ℕ) (early : m≤k)
        (v : Fin 3→Site (R.family.side m z.2)) (o : Fin 3→Site (R.family.side z.1 z.2)),
        let S:=center R.family.S z.2 (early.trans h) 0
        WilsonOffsetReportingProducts.Avoids (C:=R.family) E radius (fun i=>(grade i).val) o →
        (∀ i,o i∈S.margin (v i) (3*span R.family.S h z.2)) →
        ∀ (born : Fin 3→Site (R.family.side z.1 z.2)) (B : ℕ→ℕ→ℝ) (X₀ : (i:Fin 3)→Sight R.family (degree i) z.2)
          (Q : (i:Fin 3)→Emblems R.family (degree i)),
        (∀ i, Enrolled R.makes R.doors B k₀ z.1 z.2 (degree i)
          (WilsonThermometerOffsetResidue.digits R z.1 z.2 (born i)) (X₀ i) (Q i)) →
        ∀ y : (i : Fin 3) → Palette R.family (degree i),
        (∀ i∈s, b.step (degree i) z (field Z z.1 z.2 Finset.univ i) =
          b.step (degree i) z (WilsonThermometerWeakEquationCost.column R (p:=z.2) (Q i) h₀ (y i))) →
        ∀ (I : Type) [Fintype I] (sites : I → S.Cell) (watch : I → Config G (R.family.side z.1 z.2)→ℂ),
        Function.Injective (Sum.elim v sites) → (∀ j, Interior (S.chamber 0) (watch j)) →
        let X:=WilsonThermometerReflectedWatch.exterior S sites watch
        (∀ i,LocalOn (Mark.Outer (radius (grade i)) (o i)) X) → Envelope X →
        ‖moment (R.family.beta z.1 z.2) (fun U=>(∏ i,
            R.family.O z.1 z.2 (candidate (p:=z.2) Z h₀ s Q y i) (o i) U)*X U) -
          moment (R.family.beta z.1 z.2) (fun U=>(∏ i,R.family.O z.1 z.2 (field Z z.1 z.2 s i) (o i) U)*X U)‖ ≤
          7*(Real.exp (-(1/64:ℝ)*R.family.S.scale z.1)*(M s+extra y)^3)*
            ∏ j,S.rootTest (R.family.beta z.1 z.2) (watch j) := by
  obtain ⟨radius,erase⟩:=WilsonThermometerRelativeWard.original R E W P b portfolio house
  choose k₁ cash cash0 bank using fun i : Fin 3=>
    WilsonThermometerExtractedColumns.original R.makes F.room.copies (grade i).val
  obtain ⟨start,bankWeak⟩:=eventually_atTop.mp (eventually_all.mpr (fun i:Fin 3=>
    WilsonThermometerWeakEquationCost.original R P house (grade i) (1/64) (by norm_num)))
  refine ⟨radius,start,?_⟩
  filter_upwards [WilsonThermometerMarchReference.original F J V A simple paid lead 1 zero_lt_one] with r reference
  dsimp only
  intro k₀ funded
  have weak:=bankWeak k₀ funded
  filter_upwards [eventually_all.mpr (fun i : Fin 3=>eventually_ge_atTop (k₁ i)),
    eventually_all.mpr (fun i : Fin 3=>WilsonThermometerRelativeWard.paid R E W P b portfolio house simple (grade i))]
    with k available returned
  let Z := adjusted F J V A r
  let tag (s:Badge) (i:Fin 3) := WilsonThermometerMarchReference.fee R.family s i
  let g (i:Fin 3) := cash i*R.family.S.a k^(-((grade i).val:ℝ)-1)+1
  let bill (s:Badge) (i:Fin 3) := g i * (1+Real.exp (1*(-Real.log r))*tag s i)
  let rate (s:Badge) (i:Fin 3) := 2*(Fintype.card (R.family.labels.level (grade i)).Index:ℝ)*(Real.exp (1*(-Real.log r))*tag s i)
  let M (s:Badge) := (1+∑ i, |rate s i|)+∑ i,|bill s i|
  have positive (s) : 0≤M s := by dsimp only [M]; positivity
  have p₀ (s i) : rate s i ≤ M s := by
    have one:=Finset.single_le_sum (s:=Finset.univ) (f:=fun a=>|rate s a|) (fun _ _=>abs_nonneg _) (Finset.mem_univ i)
    dsimp only [M]
    linarith [le_abs_self (rate s i),Finset.sum_nonneg (s:=Finset.univ) (f:=fun a=>|bill s a|) (fun _ _=>abs_nonneg _)]
  have p₁ (s i) : bill s i ≤ M s := by
    have one:=Finset.single_le_sum (s:=Finset.univ) (f:=fun a=>|bill s a|) (fun _ _=>abs_nonneg _) (Finset.mem_univ i)
    dsimp only [M]
    linarith [le_abs_self (bill s i),Finset.sum_nonneg (s:=Finset.univ) (f:=fun a=>|rate s a|) (fun _ _=>abs_nonneg _)]
  refine ⟨M,positive,?_⟩
  filter_upwards [(upper f).eventually (eventually_all.mpr returned),
      (upper f).eventually (erase (Fin 3) (fun i=>(grade i).val)),
      (upper f).eventually (R.family.S.divergent.eventually_ge_atTop 0),
      eventually_all.mpr (fun i=>bank i k (available i)),(upper f).eventually_gt_atTop Z.station.k, (upper f).eventually_ge_atTop k, (upper f).eventually_ge_atTop k₀,
      (upper f).eventually (eventually_all.mpr weak)]
    with z receipt all clock prices later h h₀ costs
  refine ⟨h,h₀,?_⟩
  intro s m early v o avoids margin born B X₀ Q record y matching I inst sites watch inject hW away envelope
  let S:=center R.family.S z.2 (early.trans h) 0
  have get (i:Fin 3) := (prices i).choose_spec m early (v i) (o i) (field Z z.1 z.2 s i) (margin i)
  choose X loc base registered using get
  let input (i:Fin 3) : R.family.label (degree i) := field Z z.1 z.2 s i
  let replacement (i:Fin 3) : R.family.label (degree i) := candidate (p:=z.2) Z h₀ s Q y i
  choose D ld error exactD using fun i : Fin 3=>(receipt i).choose_spec z.2 (input i) (replacement i) early (v i) (o i) (margin i)
  have actual (i:Fin 3) : ‖field Z z.1 z.2 s i‖ ≤ Real.exp (1*(-Real.log r))*tag s i := by
    let x:=field Z z.1 z.2 s i
    have size : ‖x‖ ≤ (R.family.labels.level (grade i)).coeffSize x :=
      (pi_norm_le_iff_of_nonneg (Work.G08.size_nonneg _ _)).mpr fun j=>
        Finset.single_le_sum (fun _ _=>norm_nonneg _) (Finset.mem_univ j)
    exact size.trans (reference z.1 z.2 later s i)
  have regular (i:Fin 3) : S.rootTest (R.family.beta z.1 z.2) (X i) ≤ M s := by
    have good : 0≤ g i := by
      exact add_nonneg (mul_nonneg (cash0 i) (Real.rpow_nonneg (R.family.S.a_pos k).le _)) zero_le_one
    exact (base i).trans ((mul_le_mul_of_nonneg_left (add_le_add (le_refl (1:ℝ)) (actual i)) good).trans (p₁ s i))
  have pair (i:Fin 3) : b.step (degree i) z (input i)=b.step (degree i) z (replacement i) := by
    by_cases hi:i∈s
    · simp only [input,replacement,candidate,hi,if_true,occupied Z z.1 z.2 s i hi]
      exact matching i hi
    · simp only [input,replacement,candidate,hi,if_false]
  have exp0 := Real.exp_pos ((1/64:ℝ)*R.family.S.scale z.1)
  have error0 := Real.exp_pos (-(1/64:ℝ)*R.family.S.scale z.1)
  have extras : 0≤extra y := mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _=>size_ge _)
  have reserve (i:Fin 3) : 2*size (y i) ≤ extra y :=
    mul_le_mul_of_nonneg_left (Finset.single_le_sum (fun j _=>size_ge (y j)) (Finset.mem_univ i)) (by norm_num)
  have defect (i:Fin 3) : S.rootTest (R.family.beta z.1 z.2) (D i) ≤
      Real.exp (-(1/64:ℝ)*R.family.S.scale z.1)*(M s+extra y) := by
    apply (error i).trans
    by_cases hi : i∈s
    · have q:=(costs i) z.2 h₀ _ B (X₀ i) (Q i) (record i) (input i) (y i)
      have rate0 : 2*(Fintype.card (R.family.labels.level (degree i)).Index * ‖input i‖+size (y i)) ≤
          M s+extra y := by
        dsimp only [rate] at p₀
        have cost := (mul_le_mul_of_nonneg_left (actual i)
          (by positivity : 0 ≤ (2:ℝ)*Fintype.card (R.family.labels.level (degree i)).Index)).trans (p₀ s i)
        rw [mul_add,←mul_assoc]
        exact add_le_add cost (reserve i)
      simp only [replacement,candidate,hi,if_true]
      apply (mul_le_mul_of_nonneg_right q (Real.exp_pos _).le).trans
      rw [mul_assoc,←Real.exp_add]
      rw [show (1/64:ℝ)*R.family.S.scale z.1+ -(1/32:ℝ)*R.family.S.scale z.1 =
        -(1/64:ℝ)*R.family.S.scale z.1 by ring]
      rw [mul_comm (Real.exp _)]
      exact mul_le_mul_of_nonneg_right rate0 error0.le
    · simp only [replacement,candidate,hi,if_false,WilsonThermometerRelativeWard.gap,input,sub_self,map_zero]
      simp [Labels.Frame.coeffSize]
      exact mul_nonneg (Real.exp_pos _).le (add_nonneg (positive s) extras)
  have bound := WilsonThermometerReflectedWatch.original S v sites X D watch (R.family.beta z.1 z.2)
    (seamless R.makes z.1 z.2) inject loc ld hW (add_nonneg (positive s) extras)
    (Real.exp_le_one_iff.mpr (by nlinarith : -(1/64:ℝ)*R.family.S.scale z.1 ≤ 0))
    (fun i=>(regular i).trans (le_add_of_nonneg_right extras)) defect
  have first (i : Fin 3) : S.copy (v i) (X i) =
      R.family.O z.1 z.2 (d:=(grade i).val) (field Z z.1 z.2 s i) (o i) := registered i
  have last (i : Fin 3) : S.copy (v i) (D i) = WilsonOffsetReportingProducts.residual R.family
      (E (grade i)) z.1 z.2 (P (grade i) z) (input i-replacement i) (o i) := exactD i
  have original := all z.2 input replacement o (WilsonThermometerReflectedWatch.exterior S sites watch)
    pair avoids away envelope
  let ref := Wilson.moment (R.family.beta z.1 z.2) (fun U=>(∏ i,R.family.O z.1 z.2 (input i) (o i) U)*
    WilsonThermometerReflectedWatch.exterior S sites watch U)
  exact (congrArg (fun a : ℂ=>‖a-ref‖) original).le.trans (by
    simpa only [first,last,input,ref] using! bound)


end YM.Integration.WilsonThermometerFundedWeakCells
