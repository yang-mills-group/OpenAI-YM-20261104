import YM.Integration.WilsonThermometerMarchProduct
import YM.Integration.WilsonThermometerReflectedWatch
import YM.Integration.WilsonThermometerExtractedColumns

/-! Hear the signed equation error on the original physical extraction
with every cleared reflected exterior cell. The source-field bill at fixed
physical radius is independent of both regulators. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonThermometerMarchTerminalWatch
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

theorem upper (f : Extraction.Order) : Tendsto Prod.fst f.fuse atTop :=
  tendsto_atTop.mpr fun n=> (f.fused _).2 (Eventually.of_forall fun _=>f.mesh.cofinal.eventually_ge_atTop n)

theorem original (simple : G.Simple) (paid : Book (f:=f) (l:=l) (H:=H) A J) (lead : Leading F J)
    (E : ∀ d, SectionData (R.family.labels.level d)) (W : Mark.Weave G)
    (P : ∀ d, (ℕ × ℕ) → R.family.label d ≃ₗ[ℂ] R.family.label d) (b : Presentation R.family)
    (portfolio : ∀ d, Mark.Portfolio R.family.params (E d) (W d))
    (house : Hearthside R.family E W P b (Bandage.fly R.alloy.B.a)) :
    ∃ radius : ℕ → ℕ, ∀ᶠ r in trail, let Z:=adjusted F J V A r
      ∀ᶠ k : ℕ in atTop, ∃ M : Badge → ℝ, (∀ s,0≤M s) ∧ ∀ᶠ z : ℕ × ℕ in f.fuse, ∃ h : k≤z.1,
      ∀ (s : Badge) (m : ℕ) (early : m≤k)
        (v : Fin 3→Site (R.family.side m z.2)) (o : Fin 3→Site (R.family.side z.1 z.2)),
        let S:=center R.family.S z.2 (early.trans h) 0
        WilsonOffsetReportingProducts.Avoids (C:=R.family) E radius (fun i=>(grade i).val) o →
        (∀ i,o i∈S.margin (v i) (3*span R.family.S h z.2)) →
        ∀ (I : Type) [Fintype I] (sites : I → S.Cell) (watch : I → Config G (R.family.side z.1 z.2)→ℂ),
        Function.Injective (Sum.elim v sites) → (∀ j, Interior (S.chamber 0) (watch j)) →
        let X:=WilsonThermometerReflectedWatch.exterior S sites watch
        (∀ i,LocalOn (Mark.Outer (radius (grade i)) (o i)) X) → Envelope X →
        ‖moment (R.family.beta z.1 z.2) (fun U=>(∏ i,
            R.family.O z.1 z.2 (b.step (grade i) z (field Z z.1 z.2 s i)) (o i) U)*X U) -
          moment (R.family.beta z.1 z.2) (fun U=>(∏ i,R.family.O z.1 z.2 (field Z z.1 z.2 s i) (o i) U)*X U)‖ ≤
          7*(Real.exp (-(1/64:ℝ)*R.family.S.scale z.1)*(M s)^3)*
            ∏ j,S.rootTest (R.family.beta z.1 z.2) (watch j) := by
  obtain ⟨radius,erase⟩:=WilsonThermometerReverseWard.projected R E W P b portfolio house
  choose k₀ cash cash0 bank using fun i : Fin 3=>
    WilsonThermometerExtractedColumns.original R.makes F.room.copies (grade i).val
  refine ⟨radius,?_⟩
  filter_upwards [WilsonThermometerMarchReference.original F J V A simple paid lead 1 zero_lt_one] with r reference
  dsimp only
  filter_upwards [eventually_all.mpr (fun i : Fin 3=>eventually_ge_atTop (k₀ i)),
    eventually_all.mpr (fun i : Fin 3=>WilsonAddressedMatchedEquation.original R (d:=(grade i).val) simple portfolio house)]
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
      eventually_all.mpr (fun i=>bank i k (available i)),(upper f).eventually_gt_atTop Z.station.k, (upper f).eventually_ge_atTop k]
    with z receipt all clock prices later h
  refine ⟨h,?_⟩
  intro s m early v o avoids margin I inst sites watch inject hW away envelope
  let S:=center R.family.S z.2 (early.trans h) 0
  have get (i:Fin 3) := (prices i).choose_spec m early (v i) (o i) (field Z z.1 z.2 s i) (margin i)
  choose X loc base registered using get
  choose D ld error exactD using fun i : Fin 3=>(receipt i).choose_spec z.2 (field Z z.1 z.2 s i) early (v i) (o i) (margin i)
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
  have defect (i:Fin 3) : S.rootTest (R.family.beta z.1 z.2) (D i) ≤
      Real.exp (-(1/64:ℝ)*R.family.S.scale z.1)*M s := by
    apply (error i).trans
    rw [mul_comm (Real.exp _)]
    exact mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_left (actual i) (by positivity)).trans (p₀ s i)) (Real.exp_pos _).le
  have bound := WilsonThermometerReflectedWatch.original S v sites X D watch (R.family.beta z.1 z.2)
    (seamless R.makes z.1 z.2) inject loc ld hW (positive s)
    (Real.exp_le_one_iff.mpr (by nlinarith : -(1/64:ℝ)*R.family.S.scale z.1 ≤ 0)) regular defect
  have first (i : Fin 3) : S.copy (v i) (X i) =
      R.family.O z.1 z.2 (d:=(grade i).val) (field Z z.1 z.2 s i) (o i) := registered i
  have last (i : Fin 3) : S.copy (v i) (D i) = WilsonOffsetReportingProducts.residual R.family
      (E (grade i)) z.1 z.2 (P (grade i) z) (field Z z.1 z.2 s i-b.step (grade i) z (field Z z.1 z.2 s i)) (o i) := exactD i
  have original := all z.2 (field Z z.1 z.2 s) o (WilsonThermometerReflectedWatch.exterior S sites watch)
    avoids away envelope
  rw [original]
  simpa only [first,last] using! bound

end YM.Integration.WilsonThermometerMarchTerminalWatch
