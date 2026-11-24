import YM.Integration.WilsonTrueProjectedLocatedLeg

/-! Before the cutoffs, the true original partial transfer buys a full
numerical account at the reporting site for every incoming primary. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonTrueProjectedLocatedExpense
open Filter MeasureTheory Lattice RG Wilson Extra.Histories Source Labels
open Extra.Histories.Relay Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open QuadraticLocal QuadraticLocal.Advent AllOrder AllOrder.Floe AllOrder.Transit WheelP WilsonOriginalNullCorridor
open scoped Classical Topology BigOperators

open FormalBulk08 City Pose RemainderComparison ConnectedActivityE6
open WilsonTrueProjectedPointProgram WilsonTrueProjectedPointInverse
open WilsonTrueProjectedLocatedBasis WilsonTrueProjectedLocatedHistory
open WilsonPinnedWidthTransport WilsonTrueProjectedNaturalFee WilsonTrueProjectedCourse
open scoped Classical BigOperators
variable {G : Gauge} (R : Run G)
local notation "C₀" => R.family


open WilsonTrueProjectedLocatedFunded WilsonTrueProjectedLocatedMerge
def roof (d N p b n : ℕ) (η : ℝ) : ℝ :=
  (2+|tPrice ((C₀).labels.level d) (C₀).params ((C₀).path.rep N p b)|)*
    WilsonOriginalNullPlacedCollar.cost R d η b (b+n)*(2*∑ j ∈ Finset.range (n+1),stock C₀ (b+j))

theorem original (d : ℕ) (simple : G.Simple) (shop : RG05Preconstruction.ReadoutPurchase R.b) {η : ℝ}
    (ep : 0<η) : ∃ base,∀ b≥base,∀ N p n,b+n≤N → ∀ o : ∀ j,Site ((C₀).side j p),
    (∀ j<n,((C₀).path.levels.clock.op (b+j) p).ratio.parent (o (b+j+1))=o (b+j)) →
    ∀ i≤n,∀ x : (C₀).label d,
      let P := (C₀).path.rep N p b
      ∃ h : store C₀ d p b, Paid R P (o b) h (roof R d N p b n η*mCost C₀ d N p (b+i) x) ∧
        flow C₀ d N p b i (placed R d N p b o i x)=h.density (o b) ((C₀).localSection d) P := by
  obtain ⟨base,maps⟩:=WilsonOriginalNullPlacedFullMatrix.original R d simple shop ep
  refine ⟨base,?_⟩
  intro b late N p n live o route i hi x P
  obtain ⟨room,A,gate⟩:=maps b late N p i (by omega) o (fun j hj=>route j (by omega))
  obtain ⟨z,⟨fz,bz,hz⟩,field⟩:=WilsonTrueProjectedLocatedLeg.original R gate x
  have stks (j:ℕ):0 ≤ stock R.family (b+j):=zero_le_one.trans (R.family.path.levels.params _).columns_ge
  have stk : stock R.family (b+i) ≤ ∑ j ∈ Finset.range (n+1),stock R.family (b+j) :=
    Finset.single_le_sum (fun j _=>stks j) (Finset.mem_range.mpr (by omega))
  have growth : WilsonOriginalNullPlacedCollar.cost R d η b (b+i) ≤ WilsonOriginalNullPlacedCollar.cost R d η b (b+n) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (sub_le_sub_right
      ((OPE.scale_mono R.family.S).monotone (by omega)) _) (add_nonneg (Nat.cast_nonneg _) ep.le))
  let v:=mCost R.family d N p (b+i) x
  have v0:0 ≤ v:=Finset.sum_nonneg (fun _ _=>norm_nonneg _)
  let t:=tPrice (R.family.labels.level d) R.family.params P
  have t0:0 ≤ 2+|t|:=by positivity
  have pay:(2+|t|)*(WilsonOriginalNullPlacedCollar.cost R d η b (b+i)*(2*stock R.family (b+i)*v))
      ≤ roof R d N p b n η*v:=by
    dsimp only [roof]
    change _ ≤ (2+|t|)*WilsonOriginalNullPlacedCollar.cost R d η b (b+n)*
      (2*∑ j ∈ Finset.range (n+1),stock R.family (b+j))*v
    rw [show (2+|t|)*(WilsonOriginalNullPlacedCollar.cost R d η b (b+i)*(2*stock R.family (b+i)*v))=
      (2+|t|)*WilsonOriginalNullPlacedCollar.cost R d η b (b+i)*(2*stock R.family (b+i))*v by ring]
    exact mul_le_mul_of_nonneg_right (mul_le_mul (mul_le_mul_of_nonneg_left growth t0)
      (mul_le_mul_of_nonneg_left stk (by norm_num)) (mul_nonneg (by norm_num) (stks i))
      (mul_nonneg t0 (Real.exp_pos _).le)) v0
  exact ⟨z,⟨fz,rem_mono bz pay,hz.trans pay⟩,field⟩

theorem collected {d p b : ℕ} {W : Rep G ((C₀).side b p)} (o : Site ((C₀).side b p))
    {σ C Λ δ w : ℝ} (law : W.Lawful σ C Λ δ w) {A : Type*} (s : Finset A) (fee : A → ℝ)
    (F : A → Config G ((C₀).side b p) → ℂ)
    (each : ∀ j∈s, ∃ z : store C₀ d p b, Paid R W o z (fee j) ∧
      F j=z.density o ((C₀).localSection d) W) :
    ∃ z : store C₀ d p b, Paid R W o z (∑ j∈s,fee j) ∧
      (∑ j∈s,F j)=z.density o ((C₀).localSection d) W := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty,Finset.sum_empty]
    refine ⟨Extra.Histories.primary o 0,⟨primary_format _,primary_rem _ (Real.sqrt_pos.mpr (Real.exp_pos _)),?_⟩,?_⟩
    · change (R.family.labels.level d).coeffSize 0 ≤ 0
      simp [Frame.coeffSize]
    · funext U;simp only [primary_density,map_zero,mul_zero,Pi.zero_apply]
  | @insert i s outside ih =>
    obtain ⟨q,⟨fq,bq,pq⟩,eq⟩:=each i (Finset.mem_insert_self ..)
    obtain ⟨z,⟨fz,bz,pz⟩,ez⟩:=ih (fun j hj=>each j (Finset.mem_insert_of_mem hj))
    rw [Finset.sum_insert outside,Finset.sum_insert outside]
    refine ⟨beside q z,⟨(presentation fq bq fz bz).1,(presentation fq bq fz bz).2,?_⟩,?_⟩
    · rw [reckon];exact (Size.add _ _ _).trans (add_le_add pq pz)
    · rw [eq,ez,plus law bq bz]

end YM.Integration.WilsonTrueProjectedLocatedExpense
