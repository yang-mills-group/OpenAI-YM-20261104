import YM.Integration.WilsonOriginalCollarMint
import YM.Integration.WilsonIndependentCollarPrintIncome
import YM.Integration.WilsonIndependentCollarNeutralIncome

/-! Pre-length teacher widths for the actual neighboring marked compiler. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonOriginalCollarTeacher
open Filter Finset Lattice RG RG.Supply Precision Wilson Next.Foundations
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Winding WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar
open scoped Classical BigOperators
variable {G : Gauge}

abbrev Request (G : Gauge) := WilsonOriginalCompoundStrip.Request G

/-- Each live neutral height at the current or adjacent stage funds this inlet. -/
def common (Q : Request G) (K : KernelChoices) (x : ℕ) : ℝ :=
  univ.inf' univ_nonempty (fun z : Fin (x+2) × Fin (x+2) =>
    WilsonThermometerUnitFilingWeakStrip.trial Q K z.1 z.2)

theorem positive (Q : Request G) (K : KernelChoices) (x : ℕ) : 0 < common Q K x :=
  (lt_inf'_iff _).2 (fun z _ => WilsonThermometerUnitFilingWeakStrip.trial_pos Q K z.1 z.2)

theorem paid_neutral (Q : Request G) (K : KernelChoices) {x i H : ℕ}
    (site : i ≤ x+1) (height : H ≤ x+1) :
    common Q K x ≤ WilsonThermometerUnitFilingWeakStrip.trial Q K i H := by
  let entry : Fin (x+2) × Fin (x+2) := (⟨i,by omega⟩,⟨H,by omega⟩)
  exact inf'_le (f:=fun z : Fin (x+2) × Fin (x+2) =>
    WilsonThermometerUnitFilingWeakStrip.trial Q K z.1 z.2)
    (mem_univ entry)

def widths (Q : Request G) (x : ℕ) : WilsonIndependentCollarPrintIncome.Widths G :=
  ⟨fun _ _ I => common Q I.kernel x, fun _ _ I => positive Q I.kernel x⟩

def prices (Q : Request G) (x : ℕ) (I : Gear G) : ℝ :=
  WilsonIndependentCollarPrintIncome.prices (widths Q x) x I


/-- A post-length charged stage pays every live compiler on this particular gear. -/
theorem charged (Q : Request G) (x e k : ℕ) (I : Gear G) (he : e ≤ x) (hk : k ≤ x)
    {z : ℝ} (cash : prices Q x I ≤ z) :
    nimbus I ≤ z ∧
    (WilsonIndependentCollarPrintIncome.issue (widths Q x) e k I).fee ≤ z ∧
    (WilsonIndependentCollarPrintIncome.issue (widths Q x) e k I).strip⁻¹ ≤ z := by
  let s := widths Q x
  have h (i j : ℕ) : 0 ≤ WilsonIndependentCollarPrintIncome.fee s i j I :=
    zero_le_one.trans ((WilsonIndependentCollarPrintIncome.issue s i j I).funded.trans (le_max_left ..))
  have c : WilsonIndependentCollarPrintIncome.fee s e k I ≤ z :=
    ((single_le_sum (f:=fun t=> WilsonIndependentCollarPrintIncome.fee s e t I) (fun t _=>h e t)
      (mem_range.mpr (Nat.lt_succ_of_le hk))).trans (single_le_sum
        (f:=fun t=>∑ v ∈ range (x+1),WilsonIndependentCollarPrintIncome.fee s t v I)
        (fun t _=>sum_nonneg (fun v _=>h t v)) (mem_range.mpr (Nat.lt_succ_of_le he)))).trans
        ((le_max_right ..).trans cash)
  exact ⟨(le_max_left ..).trans cash,(le_max_left ..).trans c,(le_max_right ..).trans c⟩

/-- Compute both tokenizer outlets before the block length or any print is specified. -/
def stageInlet (Q : Request G) (K : KernelChoices) (i j l e : ℕ)
    (hi : 4 ≤ i) (hj : 5 ≤ j) (hl : 5 ≤ l) : ℝ :=
  min (common Q K j /32) (min ((raySmall G K i j hi hj).s/16)
    (admission (splash G K j l (by omega) hl) e))

theorem stage_pos (Q : Request G) (K : KernelChoices) (i j l e : ℕ)
    (hi : 4 ≤ i) (hj : 5 ≤ j) (hl : 5 ≤ l) : 0 < stageInlet Q K i j l e hi hj hl :=
  lt_min (div_pos (positive ..) (by norm_num)) (lt_min
    (div_pos (raySmall G K i j hi hj).sigma (by norm_num))
    ((lt_inf'_iff _).2 (fun a _ => perch_pos
      (div_pos (safron_nn G K j l (by omega) hl) (by norm_num)) _)))

def atStages (Q : Request G) (K : KernelChoices) (i j l e k : ℕ) : ℝ :=
  if ok : 4 ≤ i ∧ 5 ≤ j ∧ 5 ≤ l then
    (WilsonIndependentCollarPrintIncome.printer (G:=G) (stageInlet Q K i j l e ok.1 ok.2.1 ok.2.2)
      (stage_pos ..) e k).strip
  else 1

theorem atStages_pos (Q : Request G) (K : KernelChoices) (i j l e k : ℕ) :
    0 < atStages Q K i j l e k := by
  unfold atStages
  split
  · exact WilsonIndependentCollarPrintIncome.Print.openStrip _
  · exact zero_lt_one

abbrev Entries (x : ℕ) := Fin (x+3) × Fin (x+3) × Fin (x+3) × Fin (x+2) × Fin (x+2)

def teacherWidth (Q : Request G) (K : KernelChoices) (x : ℕ) : ℝ :=
  univ.inf' univ_nonempty (fun a : Entries x =>
    atStages Q K a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2)

def menu (Q : Request G) : WilsonOlderFreshGraphSchool.Menu where
  width A p K k x := min ((WilsonOlderFreshGraphAllStages.menu G).width A p K k x) (teacherWidth Q K x)
  positive A p K k x := lt_min ((WilsonOlderFreshGraphAllStages.menu G).positive A p K k x)
    ((lt_inf'_iff _).2 (fun a _ => atStages_pos Q K a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2))
  shell _ := 1
  cost _ := zero_lt_one

theorem below (Q : Request G) (K : KernelChoices) {x i j l e k : ℕ}
    (hi : i ≤ x+2) (hj : j ≤ x+2) (hl : l ≤ x+2) (he : e ≤ x+1) (hk : k ≤ x+1) :
    teacherWidth Q K x ≤ atStages Q K i j l e k := by
  let entry : Entries x := (⟨i,by omega⟩,⟨j,by omega⟩,⟨l,by omega⟩,⟨e,by omega⟩,⟨k,by omega⟩)
  exact inf'_le (f:=fun a : Entries x => atStages Q K a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2)
    (mem_univ entry)

private theorem width_eq (G : Gauge) {s t : ℝ} (pos : 0 < s) (other : 0 < t)
    (e k : ℕ) (same : s = t) :
    (WilsonIndependentCollarPrintIncome.printer (G:=G) s pos e k).strip =
    (WilsonIndependentCollarPrintIncome.printer (G:=G) t other e k).strip := by
  subst t
  rfl

/-- On a mint with its two original tokenizer equalities, the filed stage
width fits the actual compiler object. -/
theorem at_mint (Q : Request G) (A : Levels G) (m : ℕ) (e k x : ℕ)
    {I : Gear G} (kernel : I.kernel = A.clock.kernel)
    (hz : 5 ≤ A.clock.J (m+1)) (hs : I.s = (raySmall G A.clock.kernel _ _ (A.clock.adm m) hz).s)
    (past : I.past = crestM A (m+1) (upstairs A (m+1) hz))
    (hi : A.clock.J m ≤ x+2) (hj : A.clock.J (m+1) ≤ x+2) (hl : A.clock.J (m+2) ≤ x+2)
    (he : e ≤ x+1) (hk : k ≤ x+1) :
    teacherWidth Q A.clock.kernel x ≤
      (WilsonIndependentCollarPrintIncome.issue (widths Q (A.clock.J (m+1))) e k I).strip := by
  apply le_trans (below Q A.clock.kernel hi hj hl he hk)
  have ok : 4 ≤ A.clock.J m ∧ 5 ≤ A.clock.J (m+1) ∧ 5 ≤ A.clock.J (m+2) :=
    ⟨A.clock.adm m,hz,upstairs A (m+1) hz⟩
  have same : WilsonIndependentCollarPrintIncome.strip (widths Q (A.clock.J (m+1))) e k I =
      stageInlet Q A.clock.kernel (A.clock.J m) (A.clock.J (m+1)) (A.clock.J (m+2)) e ok.1 ok.2.1 ok.2.2 := by
    change min (common Q I.kernel _ /32) (min (I.s/16) (admission I.past e)) = _
    rw [kernel, hs, past]; rfl
  simp only [atStages, dif_pos ok, WilsonIndependentCollarPrintIncome.issue]
  exact (width_eq G _ _ e k same).symm.le

end YM.Integration.WilsonOriginalCollarTeacher
end
