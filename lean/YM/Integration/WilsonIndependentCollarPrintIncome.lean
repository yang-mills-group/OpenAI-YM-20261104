import YM.Integration.WilsonIndependentCollarFirstJoinIncome

/-! Elect the inverse strip and the linear group-word printer for every
active pair of orders. Their moving price is on the original Wilson clock
before the cutoff, period or amplitude of a planted bank is specified. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonIndependentCollarPrintIncome
open Filter Function Finset Lattice Laurent Bloch Metric Precision RG Wilson Work.F08 FormalBulk08
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Winding WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Soil WilsonCoeffUV.Embroider
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open scoped Classical BigOperators
variable {G : Gauge}

structure Print (G : Gauge) (s : ℝ) (e k : ℕ) where
  strip : ℝ
  fee : ℝ
  openStrip : 0 < strip
  narrow : strip ≤ s
  funded : 1 ≤ fee
  stencil (h : ℕ) (horizon : h≤e) (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [CompleteSpace V] (P : Bookend V G) (A : ℝ) (auth : Nimbus k e P) (stock : Rain P e s A) :
    Rains (automa P k h) h strip (fee*A) ∧ ∀ j<h,(baton (automa P k h) h).2 j=P j

def printer (s : ℝ) (positive : 0<s) (e k : ℕ) : Print G s e k :=
  let f := autoK G s e k positive
  ⟨f.choose,f.choose_spec.choose,f.choose_spec.choose_spec.1,f.choose_spec.choose_spec.2.1,
   f.choose_spec.choose_spec.2.2.1,f.choose_spec.choose_spec.2.2.2⟩

structure Widths (G : Gauge) where
  requested : ℕ → ℕ → Gear G → ℝ
  admitted (e k : ℕ) (I : Gear G) : 0 < requested e k I

variable (σ : Widths G)
abbrev strip (e k : ℕ) (I : Gear G) := arborθ (σ.requested e k I) I e
def issue (e k : ℕ) (I : Gear G) : Print G (strip σ e k I) e k :=
  printer _ (arbor_pos (σ.admitted e k I) I e) e k
def fee (e k : ℕ) (I : Gear G) : ℝ :=
  max (issue σ e k I).fee (issue σ e k I).strip⁻¹
def prices (J : ℕ) (I : Gear G) : ℝ :=
  max (nimbus I) (∑ e ∈ range (J+1),∑ k ∈ range (J+1), fee σ e k I)

private theorem per {J e k : ℕ} (he : e≤J) (hk : k≤J) (I : Gear G) :
    fee σ e k I ≤ prices σ J I := by
  have h (i j : ℕ) : 0 ≤ fee σ i j I :=
    zero_le_one.trans ((issue σ i j I).funded.trans (le_max_left ..))
  exact ((single_le_sum (f:=fun t=>fee σ e t I) (fun t _=>h e t)
    (mem_range.mpr (Nat.lt_succ_of_le hk))).trans (single_le_sum
      (f:=fun t=>∑ v ∈ range (J+1),fee σ t v I)
      (fun t _=>sum_nonneg (fun v _=>h t v)) (mem_range.mpr (Nat.lt_succ_of_le he)))).trans (le_max_right ..)

/-- The actual compact compiler and its nonempty scalar come from the folded
independent Bookend. Both the amplification and the inverse output width are
at most the same log-log clock price at each late date. -/
theorem original (R : Run G) (simple : G.Simple)
    (fund : FundedMarkedCoverRows.prices (prices σ) R.kit) (e : ℕ) :
    ∀ᶠ b : ℕ in atTop, ∃ Q : Realm G (e+1) Credit.leanC,
      Q.draws=R.family.path.levels ∧ Q.paid=R.metals.O ∧ Q.anchor=b ∧
      ∀ j : ℕ, ∀ h : Q.anchor ≤ j,
        let J := R.family.path.levels.clock.J (j+1)
        let z := Borough.ageZ (R.family.path.levels.clock.hatBeta j)
        let I := (Q.mint j h).gear
        nimbus I ≤ z ∧ ∀ k : ℕ, e≤J → k≤J →
          let out := issue σ e k I
          out.fee ≤ z ∧ out.strip⁻¹ ≤ z ∧ out.strip ≤ (holt Q j h (σ.requested e k I)
            (σ.admitted e k I)).s := by
  filter_upwards [FundedMarkedCoverRows.realm R simple (prices σ) fund 0 (fun _=>0) (fun _=>1)
    (fun _=>Nat.zero_lt_succ _) e 0 0] with b enrolled
  obtain ⟨Q,levels,coins,calendar,anchor,_,_,_,stages⟩ := enrolled
  refine ⟨Q,levels,coins,anchor,?_⟩
  intro j h J z I
  obtain ⟨_,_,p⟩ := stages j (anchor ▸ h) h
  have cost : prices σ J I ≤ z := by
    simpa only [J,z,I,Realm.cash,Credit.lean_cost,calendar,Ticket.zz,Borough.ageZ] using p
  refine ⟨(le_max_left ..).trans cost,?_⟩
  intro k he hk out
  have paid := (per σ he hk I).trans cost
  exact ⟨(le_max_left ..).trans paid,(le_max_right ..).trans paid,out.narrow⟩

end YM.Integration.WilsonIndependentCollarPrintIncome
