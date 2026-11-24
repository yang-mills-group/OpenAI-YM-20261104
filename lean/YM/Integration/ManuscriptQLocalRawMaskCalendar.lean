import YM.Integration.ManuscriptQLocalFiniteDisplacement
import YM.Integration.ActualNormalizedPush
import YM.RG02.Marker.Euler
import YM.Integration.WilsonCurvatureEndpoints
import YM.Integration.ActualWilsonPacketGerms
import YM.Integration.LocalComparisonReadout
import YM.Vac.Caps
import YM.Integration.PhysicalWilsonHotAllowance
import YM.Integration.ActualWilsonAbsoluteTransport
import YM.Integration.WilsonForwardMeasurable
import YM.Corona.Fill
import YM.Lattice.Foliation
import YM.Integration.WilsonThermalPacketSum

/-! Positive normalized conditional moments of the regular marked source. All original scalar spectator activities remain in the conditional density. -/

noncomputable section
namespace YM.Integration.ManuscriptQLocalRegularConditional
open Lattice Wilson RG RG.Shoot Marker MeasureTheory Comparison.RG02
open Extra.Trajectories ManuscriptQLocalShiftLedger
open scoped Classical BigOperators

variable {V : Type} [DecidableEq V] [Fintype V] {Γ : Census V}

/-- The two finite norm polynomials for the actual mark algebra. -/
def expBill (n : ℕ) (b : ℝ) := ∑i∈Finset.range (n+1), ‖((i.factorial:ℂ)⁻¹)‖*b^i
def logBill (n : ℕ) (b : ℝ) := ∑i∈Finset.range n, ‖((-1:ℂ)^i)/(i+1:ℂ)‖*(b+1)^(i+1)

theorem exp_price {w : V→ℝ} (hw : ∀i,0< w i) {x : Poly Γ} {b : ℝ} (h : Poly.price w x≤ b) :
    Poly.price w (Poly.pass x) ≤ expBill (Fintype.card V) b := by
  refine (Poly.batch hw _ _).trans <| Finset.sum_le_sum fun i _=>?_
  rw [Poly.adapted]
  exact mul_le_mul_of_nonneg_left ((Poly.powers hw x i).trans
    (pow_le_pow_left₀ (Poly.nonnegative hw x) h i)) (norm_nonneg _)

theorem log_price {w : V→ℝ} (hw : ∀i,0< w i) {x : Poly Γ} {b : ℝ}
    (hq : x.part Γ.quiet=1) (h : Poly.price w x≤ b) :
    Poly.price w (Extra.Trajectories.connected x) ≤ logBill (Fintype.card V) b := by
  have hn : Poly.price w (-(1:Poly Γ))=1 := by
    rw [←neg_one_smul ℂ (1:Poly Γ),Poly.adapted]
    simp
  have hd : Poly.price w (x-1)≤ b+1 := by
    simpa only [sub_eq_add_neg,hn] using (Poly.addition hw x (-(1:Poly Γ))).trans (add_le_add h hn.le)
  rw [RG02.Marks.connected_eq_logTable hq,RG02.Marks.logTable]
  refine (Poly.batch hw _ _).trans <| Finset.sum_le_sum fun i _=>?_
  rw [Poly.adapted]
  exact mul_le_mul_of_nonneg_left ((Poly.powers hw (x-1) (i+1)).trans
    (pow_le_pow_left₀ (Poly.nonnegative hw _) hd _)) (norm_nonneg _)

variable {G : Gauge} (C : Family G) {N n p : ℕ}
local notation "Fine" => Config G (C.side (n+1) p)
local notation "Coarse" => Config G (C.side n p)

/-- The true incoming density times the registered coarse transition divided
by the true outgoing density. The field and all test variables are fixed. -/
def charged (U : Coarse) (X : ℂ→ Fine→ Poly Γ) (z : ℂ) (v : Fine) : Poly Γ :=
  ((actualConditionalDensity C N p n U v : ℝ):ℂ) • Poly.pass (X z v)

def moment (U : Coarse) (X : ℂ→ Fine→ Poly Γ) (z : ℂ) : Poly Γ :=
  Actual.charge (prior G (C.side (n+1) p)) (charged C (N:=N) U X z)

theorem moment_part (U : Coarse) (X : ℂ→ Fine→ Poly Γ) (z : ℂ) (s : Γ.Mode) :
    (moment C (N:=N) U X z).part s = actualAverage C (N:=N) (fun v=>(Poly.pass (X z v)).part s) U := by
  simp only [moment,Actual.components,actualAverage]
  apply integral_congr_ae
  filter_upwards with v
  change ((((actualConditionalDensity C N p n U v : ℝ):ℂ) • Poly.pass (X z v)).part s) = _
  rw [Poly.part_smul,Complex.real_smul]

theorem moment_quiet (hC : C.Makes) (hn : n< N) (U : Coarse) (X : ℂ→ Fine→ Poly Γ)
    (z : ℂ) (quiet : ∀v,(X z v).part Γ.quiet=0) :
    (moment C (N:=N) U X z).part Γ.quiet=1 := by
  rw [moment_part]
  have eqn : (fun v=>(Poly.pass (X z v)).part Γ.quiet)=fun _ : Fine=>(1:ℂ) :=
    funext fun v=>Poly.pass_part _ (quiet v)
  rw [eqn,actualAverage_const C hC hn]

/-- Every rooted coefficient of the entire conditional integral is paid on
the correctly normalized original leaf. The intermediate finite coefficient
count is independent of all lattice periods and the selected fine roster. -/
theorem moment_price (hC : C.Makes) (hn : n< N) (U : Coarse) (X : ℂ→ Fine→ Poly Γ)
    {w : V→ℝ} (hw : ∀i,0< w i) (z : ℂ) {b : ℝ} (hx : ∀v,Poly.price w (X z v)≤ b) :
    Poly.price w (moment C (N:=N) U X z) ≤ Fintype.card Γ.Mode*expBill (Fintype.card V) b := by
  let a := expBill (Fintype.card V) b
  have each (s : Γ.Mode) : Poly.toll w s*‖(moment C (N:=N) U X z).part s‖≤ a := by
    let d := Poly.toll w s
    have hd : 0< d := Poly.worth hw _
    have h (v : Fine) : ‖(Poly.pass (X z v)).part s‖≤ a/d :=
      (le_div_iff₀ hd).2 (by simpa only [mul_comm] using (Poly.member hw s _).trans (exp_price hw (hx v)))
    rw [moment_part]
    exact (mul_comm ..).le.trans ((le_div_iff₀ hd).1 (actualAverage_norm_le C hC hn h U))
  exact (Finset.sum_le_sum fun s _=>each s).trans_eq (by simp [a])

def connectedBill (Γ : Census V) (b : ℝ) : ℝ :=
  logBill (Fintype.card V) (Fintype.card Γ.Mode*expBill (Fintype.card V) b)

theorem conditional_price (hC : C.Makes) (hn : n< N) (U : Coarse) (X : ℂ→ Fine→ Poly Γ)
    {w : V→ℝ} (hw : ∀i,0< w i) (z : ℂ) {b : ℝ} (hx : ∀v,Poly.price w (X z v)≤ b)
    (quiet : ∀v,(X z v).part Γ.quiet=0) :
    Poly.price w (Extra.Trajectories.connected (moment C (N:=N) U X z)) ≤ connectedBill Γ b :=
  log_price hw (moment_quiet C hC hn U X z quiet) (moment_price C hC hn U X hw z hx)

/-- Each actual mixed coefficient remains polynomial in its auxiliary source
charge through the normalized Wilson integral and genuine finite logarithm. -/
theorem conditional_degree (hC : C.Makes) (hn : n< N) (U : Coarse) (X : ℂ→ Fine→ Poly Γ)
    (weight₀ : V→ℕ) (hX : ∀v,Ledger weight₀ (fun z=>X z v))
    {w : V→ℝ} (hw : ∀i,0< w i) (b : ℂ→ℝ) (paid : ∀z v,Poly.price w (X z v)≤ b z)
    (hm : ∀z s,AEStronglyMeasurable (fun v=>(Poly.pass (X z v)).part s) (prior G _)) :
    Ledger weight₀ (fun z=>Extra.Trajectories.connected (moment C (N:=N) U X z)) := by
  apply ManuscriptQLocalShiftLedger.Ledger.connected
  apply ManuscriptQLocalShiftIntegral.charge
  · exact fun v=>Ledger.smul ((actualConditionalDensity C N p n U v:ℝ):ℂ) (hX v).pass
  · intro z s
    let a := expBill (Fintype.card V) (b z)
    have h (v : Fine) : ‖(Poly.pass (X z v)).part s‖≤ a/Poly.toll w s :=
      (le_div_iff₀ (Poly.worth hw _)).2 (by
        rw [mul_comm]
        exact (Poly.member hw s (Poly.pass (X z v))).trans (exp_price hw (paid z v)))
    change Integrable (fun v=>(charged C (N:=N) U X z v).part s) (prior G _)
    simpa only [charged,Poly.part_smul,Complex.real_smul,smul_eq_mul] using
      actualAverage_integrable C hC hn (hm z s) h U

end YM.Integration.ManuscriptQLocalRegularConditional
end

/-! The artificial analytic disk for the complete conditional regular source and its finite high-grade remainder. -/

noncomputable section
namespace YM.Integration.ManuscriptQLocalConditionalGradeTail
open Lattice Wilson RG RG.Shoot Marker MeasureTheory Comparison.RG02
open Extra.Trajectories ManuscriptQLocalShiftLedger ManuscriptQLocalSourceFourier
open ManuscriptQLocalRegularConditional
open scoped Classical BigOperators

theorem scaled {D : ℕ} (p : Polynomial ℂ) (hp : p.natDegree≤ D) (r : ℂ) (k : ZMod (D+1)) :
    project (fun j=>p.eval (r*phase j)) k = r^k.val*p.coeff k.val := by
  apply Eq.trans _ (recover (fun i : ZMod (D+1)=>r^i.val*p.coeff i.val) k)
  apply congrArg (fun u:ZMod (D+1)→ℂ=>ManuscriptQLocalSourceFourier.project u k)
  funext j
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hp)]
  change _=∑i : Fin (D+1),phase j^i.val • (r^i.val*p.coeff i.val)
  rw [←Fin.sum_univ_eq_sum_range (fun i:ℕ=>p.coeff i*(r*phase j)^i) (D+1)]
  exact Finset.sum_congr rfl fun i _=>by rw [mul_pow,smul_eq_mul];ring

def low (p : Polynomial ℂ) (D k : ℕ) := ∑i : Fin (D+1),if i.val≤ k then p.coeff i.val else 0

def high (p : Polynomial ℂ) (D k : ℕ) := ∑i : Fin (D+1),if k< i.val then p.coeff i.val else 0

theorem split {D : ℕ} (p : Polynomial ℂ) (hp : p.natDegree≤ D) (k : ℕ) :
    p.eval 1=low p D k+high p D k := by
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hp),
    ←Fin.sum_univ_eq_sum_range (fun i:ℕ=>p.coeff i*(1:ℂ)^i) (D+1), low,high,←Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _=>?_
  by_cases h : i.val≤ k
  · simp [h,not_lt.mpr h]
  · simp [h,lt_of_not_ge h]

theorem purchased {D : ℕ} (p : Polynomial ℂ) (hp : p.natDegree≤ D) (k : ℕ)
    {g d B : ℝ} (hg : 0< g) (hw : g≤1) (hd : 0< d)
    (paid : ∀j : ZMod (D+1),d*‖p.eval (((g⁻¹:ℝ):ℂ)*phase j)‖≤ B) :
    d*‖p.eval 1-low p D k‖ ≤ (D+1:ℕ)*(g^(k+1)*B) := by
  have hB : 0≤ B := (mul_nonneg hd.le (norm_nonneg _)).trans (paid 0)
  let u := fun j : ZMod (D+1)=>p.eval (((g⁻¹:ℝ):ℂ)*phase j)
  have h (i : ZMod (D+1)) : ‖project u i‖≤ B/d := by
    have proj := estimate u (fun _=>0) (ε:=B/d) (fun j=>by
      rw [sub_zero]
      exact (le_div_iff₀ hd).2 ((mul_comm ..).le.trans (paid j))) i
    simpa only [projection,smul_zero,Finset.sum_const_zero,sub_zero] using proj
  have hgrad (i : ZMod (D+1)) : d*‖p.coeff i.val‖≤ g^i.val*B := by
    have hi := h i
    rw [show u=(fun j : ZMod (D+1)=>p.eval (((g⁻¹:ℝ):ℂ)*phase j)) from rfl,scaled p hp,
      norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg (inv_pos.mpr hg).le,inv_pow] at hi
    have hp' : g^i.val≠0 := pow_ne_zero _ hg.ne'
    calc _ = g^i.val*(((g^i.val)⁻¹*‖p.coeff i.val‖)*d) := by field_simp
         _ ≤ _ := mul_le_mul_of_nonneg_left ((le_div_iff₀ hd).1 hi) (pow_nonneg hg.le _)
  rw [split p hp k,add_sub_cancel_left,high]
  calc _ ≤ d*(∑i : Fin (D+1),‖if k< i.val then p.coeff i.val else 0‖) :=
         mul_le_mul_of_nonneg_left (norm_sum_le ..) hd.le
       _ = ∑i : Fin (D+1),d*‖if k< i.val then p.coeff i.val else 0‖ := Finset.mul_sum _ _ _
       _ ≤ ∑_i : Fin (D+1),g^(k+1)*B := by
         refine Finset.sum_le_sum fun i _=>?_
         by_cases hi : k< i.val
         · rw [if_pos hi]
           exact (hgrad i).trans (mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hg.le hw hi) hB)
         · simp [hi,mul_nonneg (pow_nonneg hg.le _) hB]
       _ = _ := by simp

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] {Γ : Census V}
    (C : Family G) {N n period : ℕ}
local notation "Fine" => Config G (C.side (n+1) period)
local notation "Coarse" => Config G (C.side n period)

/-- An exact finite Taylor truncation in the source engineering grade. The
physical coupling and coarse data have their original real values throughout. -/
theorem conditional (hC : C.Makes) (hn : n< N) (U : Coarse) (X : ℂ→ Fine→ Poly Γ)
    (ℓ : V→ℕ) (degrees : ∀v,Ledger ℓ (fun z=>X z v)) {w : V→ℝ} (hw : ∀i,0< w i)
    (b : ℂ→ℝ) (all : ∀z v,Poly.price w (X z v)≤ b z)
    (hm : ∀z s,AEStronglyMeasurable (fun v=>(Poly.pass (X z v)).part s) (prior G _))
    (quiet : ∀z v,(X z v).part Γ.quiet=0) {g B : ℝ} (hg : 0< g) (hweak : g≤1)
    (cap : ∀z : ℂ,‖z‖=g⁻¹→∀v,Poly.price w (X z v)≤ B) (s : Γ.Mode) (k : ℕ) :
    ∃p : Polynomial ℂ,p.natDegree≤ ManuscriptQLocalShiftLedger.weight ℓ s ∧
      (∀z,p.eval z=(Extra.Trajectories.connected (moment C (N:=N) U X z)).part s) ∧
      Poly.toll w s*‖(Extra.Trajectories.connected (moment C (N:=N) U X 1)).part s-
        low p (ManuscriptQLocalShiftLedger.weight ℓ s) k‖ ≤
        (ManuscriptQLocalShiftLedger.weight ℓ s+1:ℕ)*(g^(k+1)*connectedBill Γ B) := by
  obtain ⟨p,hp,he⟩ := conditional_degree C hC hn U X ℓ degrees hw b all hm s
  refine ⟨p,hp,he,?_⟩
  rw [←he]
  apply purchased p hp k hg hweak (Poly.worth hw s)
  intro j
  rw [he]
  have hnorm : ‖((g⁻¹:ℝ):ℂ)*phase j‖=g⁻¹ := by
    rw [norm_mul,ManuscriptQLocalSourceFourier.unit,mul_one,Complex.norm_real,Real.norm_of_nonneg (inv_pos.mpr hg).le]
  exact (Poly.member hw s _).trans (conditional_price C hC hn U X hw _ (cap _ hnorm) (quiet _))

end YM.Integration.ManuscriptQLocalConditionalGradeTail
end

/-! Summable incoming marked rows on the original field. Their finite degree columns carry the physical conditional estimate through the whole countable source. -/

noncomputable section
namespace YM.Integration.ManuscriptQLocalCountableConditional
open Filter Finset Lattice Wilson RG RG.Shoot Marker MeasureTheory Comparison.RG02
open ManuscriptQLocalShiftLedger ManuscriptQLocalRegularConditional
open Push.AbsoluteSums
open scoped Classical BigOperators

variable {V ι Ω : Type} [DecidableEq V] [Fintype V] {Γ : Census V}
    {M : ℕ} (s : ι→ Γ.Mode) (slot : ι→ Fin (M+1)) (f : ι→ Ω→ℂ)

def row (u : Ω) (i : ι) : Poly Γ := Poly.send (s i) (f i u)
def bank (z : ℂ) (u : Ω) : Poly Γ := ∑'i,z^(slot i).val • row s f u i

def charge (w : V→ℝ) (a : ι→ℝ) (r : ℝ) (i : ι) := r^(slot i).val*Poly.toll w (s i)*a i

variable {w : V→ℝ} (hw : ∀i,0< w i) {a : ι→ℝ} (ha : ∀i,0≤ a i) (hf : ∀i u,‖f i u‖≤ a i)
    {r D : ℝ} (hr : 1≤ r) (pay : SumBudget (charge s slot w a r) D)

omit [Fintype V] in
include hw ha hf hr in
private theorem each (u : Ω) (i : ι) : Poly.price w (row s f u i)≤ charge s slot w a r i := by
  rw [row,Poly.solo,charge,mul_assoc]
  exact (mul_le_mul_of_nonneg_left (hf i u) (Poly.worth hw _).le).trans
    (le_mul_of_one_le_left (mul_nonneg (Poly.worth hw _).le (ha i)) (one_le_pow₀ hr))

omit [Fintype V] in
include hw ha hf hr pay in
theorem whole (z : ℂ) (u : Ω) : Summable (fun i=>z^(slot i).val • row s f u i) ∧
    Poly.price w (bank s slot f z u) ≤ (max 1 ‖z‖)^M*D := by
  let c := (max 1 ‖z‖)^M
  have hc : 0≤ c := pow_nonneg (le_trans zero_le_one (le_max_left ..)) _
  have hb := Poly.budgeted (f:=fun i=>z^(slot i).val • row s f u i) hw (pay.2.1.mul_left c) (fun i=>by
    rw [Poly.adapted,norm_pow]
    have hz : ‖z‖^(slot i).val≤ c := (pow_le_pow_left₀ (norm_nonneg _) (le_max_right ..) _).trans
      (pow_le_pow_right₀ (le_max_left ..) (Nat.le_of_lt_succ (slot i).isLt))
    exact mul_le_mul hz (each s slot f hw ha hf hr u i) (Poly.nonnegative hw _) hc)
  exact ⟨hb.1,hb.2.trans (by rw [pay.2.1.tsum_mul_left];exact mul_le_mul_of_nonneg_left pay.2.2 hc)⟩

omit [Fintype V] in
include hw hf hr pay in
theorem capped (z : ℂ) (hz : ‖z‖=r) (u : Ω) : Poly.price w (bank s slot f z u)≤ D := by
  refine (Poly.budgeted (f:=fun i=>z^(slot i).val • row s f u i) hw pay.2.1 (fun i=>?_)).2.trans pay.2.2
  rw [Poly.adapted,row,Poly.solo,norm_pow,hz,charge,mul_assoc]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hf i u) (Poly.worth hw _).le)
    (pow_nonneg (zero_le_one.trans hr) _)

omit [Fintype V] in
include hw ha hf hr pay in
theorem quiet (shy : ∀i,s i≠Γ.quiet) (z : ℂ) (u : Ω) : (bank s slot f z u).part Γ.quiet=0 := by
  rw [bank,Poly.share (whole s slot f hw ha hf hr pay z u).1]
  simp [row,Poly.part_smul,Poly.part_send,fun i=>(shy i).symm]

omit [Fintype V] in
theorem measured [Countable ι] [MeasurableSpace Ω] (hm : ∀i,Measurable (f i)) (z : ℂ) :
    Measurable (bank s slot f z) := by
  apply Measurable.tsum
  intro i
  have he : (fun u=>row s f u i)=(fun u=>f i u • Poly.send (s i) 1) := by
    funext u
    ext t
    by_cases h : t=s i <;> simp [row,Poly.part_send,Poly.part_smul,h]
  have hr : Measurable (fun u=>row s f u i) := by rw [he];exact (hm i).smul measurable_const
  exact (measurable_const (a:=z^(slot i).val)).smul hr

omit [Fintype V] in
include hw ha hf hr pay in
theorem degree (shy : ∀i,s i≠Γ.quiet) (u : Ω) :
    Ledger (fun _ : V=>M) (fun z=>bank s slot f z u) := by
  let held := row s f u
  have base : Summable held := by simpa [held] using (whole s slot f hw ha hf hr pay 1 u).1
  let col (k : Fin (M+1)) (i : ι) := if slot i=k then held i else 0
  have hc (k : Fin (M+1)) : Summable (col k) := by
    have eqn : col k = ({i : ι | slot i=k}).indicator held := by
      funext i; by_cases eq : slot i=k <;> simp [col,Set.indicator,eq]
    rw [eqn]; exact base.indicator _
  have grouped (z : ℂ) : bank s slot f z u=∑ k : Fin (M+1),z^k.val • ∑'i,col k i := by
    have h (i : ι) : z^(slot i).val • held i=∑k : Fin (M+1), z^k.val • col k i := by
      simp [col,smul_ite,eq_comm (a:=slot i)]
    unfold bank
    rw [tsum_congr h,Summable.tsum_finsetSum (fun k _=>(hc k).const_smul (z^k.val))]
    exact Finset.sum_congr rfl fun k _=>((hc k).hasSum.const_smul (z^k.val)).tsum_eq
  intro t
  by_cases hq : t=Γ.quiet
  · subst t
    exact ⟨0,by simp,fun z=>by rw [Polynomial.eval_zero,quiet s slot f hw ha hf hr pay shy z u]⟩
  · let coeff (k : Fin (M+1)) := (∑'i,col k i).part t
    refine ⟨∑k : Fin (M+1),Polynomial.C (coeff k)*Polynomial.X^k.val,?_,?_⟩
    · have hne : t.val.Nonempty := Finset.nonempty_iff_ne_empty.mpr (fun h=>hq (Subtype.ext h))
      have ht : M≤ weight (fun _:V=>M) t := by
        simpa [ManuscriptQLocalShiftLedger.weight] using Nat.mul_le_mul_right M (Finset.card_pos.mpr hne)
      exact (degree_sum _ _ _ (fun k _=>(Polynomial.natDegree_mul_le ..).trans
        (by simpa using Nat.le_of_lt_succ k.isLt))).trans ht
    · intro z
      change Polynomial.eval z _ = (bank s slot f z u).part t
      rw [grouped,Poly.part_sum,ManuscriptQLocalShiftLedger.eval_sum]
      refine Finset.sum_congr rfl fun k _=>?_
      simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,Poly.part_smul]
      exact mul_comm _ _

end YM.Integration.ManuscriptQLocalCountableConditional
end

/-! The original engineering-degree tail of all masked regular Wilson packets, with the complete scalar spectator gas in the positive coarse conditional. -/

noncomputable section
namespace YM.Integration.ManuscriptQLocalOriginalConditionalTail
open Function Filter Finset Lattice RG RG.Shoot Wilson Marker MeasureTheory
open Progress.DirectedRecipe LocalComparison Comparison.Density.RenderM Comparison.Density.RenderM.Token
open Push.Local Push.AbsoluteSums FullQLocal FullQLocal.RenderedStep.Numeric Comparison.RG02
open ManuscriptQLocalShiftLedger ManuscriptQLocalRegularConditional Pert.Asymptotics
open scoped Classical BigOperators

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] {Γ : Census V} {n : Side}
    {D : V→ ComparisonDensity.Address.Orbit} (P : MarkedPackets D G n Γ)

abbrev Live := {i : ℕ // (P.packet i).isSome}

def token (i : Live P) := (P.packet i).get i.property

omit [Fintype V] in
theorem chosen (i : Live P) : P.packet i=some (token P i) := (Option.some_get i.property).symm

omit [Fintype V] in
theorem hot (i : Live P) : P.mode i≠Γ.quiet := P.marked i (token P i) (chosen P i)

def engineering (i : ℕ) : ℕ := (P.power i+P.rank i).toNat

omit [Fintype V] in
theorem capacity (i : Live P) : engineering P i≤ P.powerCap+P.rankCap := by
  have hp := P.power_bounded i (token P i) (chosen P i)
  have hq := P.rank_bounded i (token P i) (chosen P i)
  have h0 := P.nonnegative_grade i (token P i) (chosen P i)
  have hnat : P.power i≤((P.power i).natAbs:ℤ) := Int.le_natAbs
  unfold engineering
  omega

def slot (i : Live P) : Fin (P.powerCap+P.rankCap+1) :=
  ⟨engineering P i,Nat.lt_succ_of_le (capacity P i)⟩

def field (p : BudgetPoint) (g : ℝ) (x : IndependentTests D) (i : Live P) :=
  masked p.threshold (token P i).plot (fun u=>P.term (testInclusion D x) g u i)

def source (p : BudgetPoint) (g : ℝ) (x : IndependentTests D) :=
  ManuscriptQLocalCountableConditional.bank (fun i : Live P=>P.mode i) (slot P) (field P p g x)

omit [Fintype V] in
theorem physical (p : BudgetPoint) (g : ℝ) (x : IndependentTests D) (u : Config G n) :
    source P p g x 1 u=∑'i : Live P,Poly.send (P.mode i) (field P p g x i u) := by
  simp [source,ManuscriptQLocalCountableConditional.bank,ManuscriptQLocalCountableConditional.row]

theorem healthy (p : BudgetPoint) (g : ℝ) (x : IndependentTests D) (u : Config G n)
    (hu : ∀i : Live P,Healthy p.threshold (token P i).plot u) :
    source P p g x 1 u=P.read (testInclusion D x) g u := by
  rw [physical]
  have hh (i : Live P) : field P p g x i u=P.term (testInclusion D x) g u i :=
    masked_eq _ _ _ _ (hu i)
  simp_rw [hh]
  unfold MarkedPackets.read
  apply tsum_subtype_eq_of_support_subset (s:={i:ℕ | (P.packet i).isSome})
    (f:=fun i:ℕ=>Poly.send (P.mode i) (P.term (testInclusion D x) g u i))
  intro i hi
  cases h : P.packet i with
  | none=>exact (hi (by simp [MarkedPackets.term,h])).elim
  | some T=>change (P.packet i).isSome;simp [h]

variable {q : BudgetPoint} {L : V→ Support n}
    {region : Comparison.Density.Testing.Region (fun v=>(D v).Mood) n}
    {w : V→ℝ} {width budget : ℝ} {off slope : ℕ} (H : P.Paid q L region w 1 width budget off slope)
    (o : V→ Site n) (ho : ∀v,o v∈L v)

omit [Fintype V] in
include H in
theorem measured (p : BudgetPoint) (g : ℝ) (x : IndependentTests D) (i : Live P) :
    Measurable (field P p g x i) := by
  have he : (fun u=>P.term (testInclusion D x) g u i)=
      ((g:ℂ)^P.power i) • (token P i).read (testInclusion D x) := by
    funext u
    simp [MarkedPackets.term,chosen P i]
  apply masked_measurable
  rw [he]
  exact (measurable_const (a:=(g:ℂ)^P.power i)).smul (ActualWilsonPacketGerms.regular_at H (chosen P i) p (testInclusion D x)).borel

end YM.Integration.ManuscriptQLocalOriginalConditionalTail
end


/-! Absolute signed perturbations of the complete finite marked exponential and connected logarithm. -/

noncomputable section
namespace YM.Integration.ManuscriptQLocalMeasuredMarkDifference
open Filter Finset Lattice RG RG.Shoot Wilson Marker MeasureTheory Comparison.RG02
open ManuscriptQLocalRegularConditional ManuscriptQLocalOriginalConditionalTail
open scoped BigOperators Classical
variable {V : Type} [DecidableEq V] [Fintype V] {Γ : Census V} {w : V→ℝ} (hw : ∀i,0< w i)

omit [Fintype V] in
include hw in
theorem power (x y : Poly Γ) {B : ℝ} (hx : Poly.price w x≤ B) (hy : Poly.price w y≤ B) (j : ℕ) :
    Poly.price w (x^j-y^j)≤ j*(1+B)^j*Poly.price w (x-y) := by
  let d := Poly.price w (x-y)
  have hd : 0≤ d := Poly.nonnegative hw _
  have hb : 0≤ B := (Poly.nonnegative hw x).trans hx
  have ha : 1≤1+B := by linarith
  induction j with
  | zero=>simp
  | succ j ih=>
    have id : x^(j+1)-y^(j+1)=(x^j-y^j)*x+y^j*(x-y) := by ring
    rw [id]
    have e := (Poly.addition hw ((x^j-y^j)*x) (y^j*(x-y))).trans
      (add_le_add (Poly.multiplication hw (x^j-y^j) x) (Poly.multiplication hw (y^j) (x-y)))
    have yb : Poly.price w (y^j)≤(1+B)^j := (Poly.powers hw y j).trans
      (pow_le_pow_left₀ (Poly.nonnegative hw y) (hy.trans (by linarith)) _)
    have l : Poly.price w (x^j-y^j)*Poly.price w x≤(j:ℝ)*(1+B)^j*d*(1+B) :=
      mul_le_mul ih (hx.trans (by linarith)) (Poly.nonnegative hw _) (by positivity)
    have r : Poly.price w (y^j)*d≤(1+B)^(j+1)*d :=
      mul_le_mul_of_nonneg_right (yb.trans (pow_le_pow_right₀ ha (Nat.le_succ j))) hd
    apply e.trans ((add_le_add l r).trans_eq ?_)
    simp only [Nat.cast_succ,pow_succ,d];ring

def modulus {ι : Type} (I : Finset ι) (a : ι→ℂ) (j : ι→ℕ) (b : ℝ) : ℝ :=
  ∑i∈I,‖a i‖*(j i:ℝ)*(1+b)^j i

omit [Fintype V] in
include hw in
theorem polynomial {ι : Type} (I : Finset ι) (a : ι→ℂ) (j : ι→ℕ) (x y : Poly Γ) {B : ℝ}
    (hx : Poly.price w x≤ B) (hy : Poly.price w y≤ B) :
    Poly.price w ((∑i∈I,a i • x^(j i))-(∑i∈I,a i • y^(j i)))≤ modulus I a j B*Poly.price w (x-y) := by
  rw [←Finset.sum_sub_distrib]
  unfold modulus
  rw [Finset.sum_mul]
  apply (Poly.batch hw _ _).trans
  refine Finset.sum_le_sum fun i _=>?_
  rw [←smul_sub,Poly.adapted]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (power hw x y hx hy (j i)) (norm_nonneg (a i))

def expMod (n : ℕ) (B : ℝ) := modulus (Finset.range (n+1)) (fun i=>(i.factorial:ℂ)⁻¹) id B
def logMod (n : ℕ) (B : ℝ) := modulus (Finset.range n) (fun i=>(-1:ℂ)^i/(i+1:ℂ)) (fun i=>i+1) (B+1)

include hw in
theorem passing {B : ℝ} {x y : Poly Γ} (hx : Poly.price w x≤ B) (hy : Poly.price w y≤ B) :
    Poly.price w (Poly.pass x-Poly.pass y)≤ expMod (Fintype.card V) B*Poly.price w (x-y) :=
  polynomial hw _ _ _ _ _ hx hy

omit [Fintype V] in
include hw in
private theorem centered (x : Poly Γ) {B : ℝ} (hx : Poly.price w x≤ B) : Poly.price w (x-1)≤ B+1 := by
  have hn : Poly.price w (-(1:Poly Γ))=1 := by
    rw [←neg_one_smul ℂ (1:Poly Γ),Poly.adapted]
    simp
  simpa only [sub_eq_add_neg,hn] using (Poly.addition hw x (-(1:Poly Γ))).trans (add_le_add hx hn.le)

include hw in
theorem connected {B : ℝ} {x y : Poly Γ} (cx : x.part Γ.quiet=1) (cy : y.part Γ.quiet=1)
    (hx : Poly.price w x≤ B) (hy : Poly.price w y≤ B) :
    Poly.price w (Extra.Trajectories.connected x-Extra.Trajectories.connected y)≤
      logMod (Fintype.card V) B*Poly.price w (x-y) := by
  rw [RG02.Marks.connected_eq_logTable cx,RG02.Marks.connected_eq_logTable cy,RG02.Marks.logTable,RG02.Marks.logTable]
  simpa only [logMod,sub_sub_sub_cancel_right] using
    polynomial hw (Finset.range (Fintype.card V)) (fun i=>(-1:ℂ)^i/(i+1:ℂ)) (fun i=>i+1) (x-1) (y-1)
      (centered hw x hx) (centered hw y hy)

theorem nonnegative {ι : Type} (I : Finset ι) (a : ι→ℂ) (j : ι→ℕ) {b : ℝ} (hb : 0≤ b) :
    0≤ modulus I a j b := Finset.sum_nonneg fun i _=>by positivity

end YM.Integration.ManuscriptQLocalMeasuredMarkDifference
end

/-! The true incident oriented faces of a declared original source support. -/

noncomputable section
namespace YM.Integration.ManuscriptQLocalIncidentMasks
open Function Filter Set Finset MeasureTheory Lattice Wilson RG RG.Supply Next.Rank Push.GridApprox WardBin.Wheels
open MergeProof PhysicalNext.Repeat.Legato PhysicalNext.Repeat Next.Scheduling Next.Scheduling.Clock
open Push.PriceCompiler Next.Foundations OPE.Therm
open RG.Shoot
open scoped BigOperators Classical Topology
variable {G : Gauge} {n : Side}

def bases (x : Site n) (a : PlaqAxes) : Support n :=
  {x,x-step a.val.1,x-step a.val.1-step a.val.2,x-step a.val.2}

def faces (P : Support n) : Finset (Face (Per n)) :=
    P.biUnion fun x=>Finset.univ.biUnion fun a : PlaqAxes=>(bases x a).image (fun y=>(y,a))

theorem cap (x : Site n) (a : PlaqAxes) : (bases x a).card≤4 := by
  unfold bases
  calc _ ≤ (insert (x-step a.val.1) ({x-step a.val.1-step a.val.2,x-step a.val.2}:Support n)).card+1 := Finset.card_insert_le _ _
       _ ≤ ({x-step a.val.1-step a.val.2,x-step a.val.2}:Support n).card+1+1 := Nat.add_le_add_right (Finset.card_insert_le _ _) 1
       _ ≤ ({x-step a.val.2}:Support n).card+1+1+1 := Nat.add_le_add_right (Nat.add_le_add_right (Finset.card_insert_le _ _) 1) 1
       _ = 4 := by simp

theorem rooted (P : Support n) (f : Face (Per n)) {x : Site n} (hx : x∈P) (ht : x∈touched f) : f∈faces P := by
  rcases f with ⟨y,a⟩
  refine Finset.mem_biUnion.mpr ⟨x,hx,Finset.mem_biUnion.mpr ⟨a,Finset.mem_univ _,Finset.mem_image.mpr ⟨y,?_,rfl⟩⟩⟩
  have v : x=y ∨ x=y+step a.val.1 ∨ x=y+step a.val.1+step a.val.2 ∨ x=y+step a.val.2 := by
    simpa [touched,square_corners,or_assoc,or_left_comm,or_comm] using ht
  simp only [bases,Finset.mem_insert,Finset.mem_singleton]
  rcases v with rfl|rfl|rfl|rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl (by abel))
  · exact Or.inr (Or.inr (Or.inl (by abel)))
  · exact Or.inr (Or.inr (Or.inr (by abel)))

theorem count (P : Support n) : (faces P).card≤ P.card*(Fintype.card PlaqAxes*4) := by
  calc _ ≤ ∑x∈P,(Finset.univ.biUnion fun a:PlaqAxes=>(bases x a).image fun y=>(y,a)).card := Finset.card_biUnion_le
       _ ≤ ∑_x∈P,Fintype.card PlaqAxes*4 := by
         refine Finset.sum_le_sum fun x _=>?_
         calc _ ≤ ∑a:PlaqAxes,((bases x a).image fun y=>(y,a)).card := Finset.card_biUnion_le
              _ ≤ ∑_a:PlaqAxes,4 := Finset.sum_le_sum fun a _=>Finset.card_image_le.trans (cap x a)
              _ = _ := by simp
       _ = _ := by simp

def failed (P : Support n) (t : ℝ) : Set (Config G n) := {U | ¬Disjoint P (flags t U)}

theorem forced (P : Support n) (t : ℝ) : failed (G:=G) P t⊆(House.chilly (faces P) t)ᶜ := by
  intro U h hquiet
  change ¬Disjoint P (flags t U) at h
  obtain ⟨x,hp,hf⟩ := Finset.not_disjoint_iff.mp h
  obtain ⟨f,ht,hbad⟩ := (flags_spec t U x).1 hf
  exact (not_le_of_gt hbad) (hquiet f (rooted P f hp ht))

theorem measured (P : Support n) (t : ℝ) : MeasurableSet (failed (G:=G) P t) := by
  have eqn : failed (G:=G) P t = ⋃x:P,{U:Config G n | x.val∈flags t U} := by
    ext U
    change (¬Disjoint P (flags t U)) ↔ _
    simp only [Finset.not_disjoint_iff,Set.mem_iUnion,Set.mem_setOf_eq]
    exact ⟨fun ⟨x,hp,hf⟩=>⟨⟨x,hp⟩,hf⟩,fun ⟨x,hf⟩=>⟨x.val,x.property,hf⟩⟩
  rw [eqn]
  exact MeasurableSet.iUnion fun x=>(flags_open x.val t).measurableSet

theorem hot {H : History G} (W : Poetry H.levels) (hG : G.Simple) (Z : H.Selected) (d : ℕ) :
    ∀ᶠ k:ℕ in atTop,∀N,k≤ N→∀per (P:Support (H.S.side k per)),
      (scene H N per k).real (failed P (H.rep N per k).p.threshold) ≤
        (faces P).card*H.levels.clock.forcedAllowance k^d := by
  filter_upwards [PhysicalWilsonHotAllowance.faces W hG Z (ρ:=1) zero_lt_one d] with k paid N hk per P
  letI : IsProbabilityMeasure (scene H N per k) := probability (H:=H) (p:=per) Z hk
  have first := measureReal_mono (μ:=scene H N per k) (forced P (H.rep N per k).p.threshold) (measure_ne_top _ _)
  exact first.trans (by simpa only [one_mul] using paid N hk per (faces P))

/-- Fixed schedule coefficient for the entire inspected plaquette support. -/
theorem cover {B : ℕ} {σ w ℓ A : ℝ} {off slope : ℕ} (P : Support n)
    (hb : 0< B) (hσ : 0<σ) (hw : 0≤ w) (hℓ : 0≤ℓ) (hA : Real.exp (σ*off)≤ A)
    (h : B*(coverNumber B P : ℝ)≤ off*B+slope*ℓ) (reserve : σ*slope/B≤ w/4) :
    (faces P).card ≤ ((Fintype.card PlaqAxes*4:ℕ):ℝ)*(2*B+1)^4*(A/σ)*Real.exp (w*ℓ) := by
  have b : 0<(B:ℝ) := by exact_mod_cast hb
  have hm : σ*(coverNumber B P : ℝ)≤σ*off+(w/4)*ℓ := by
    have hh : (coverNumber B P:ℝ)≤(off:ℝ)+(slope:ℝ)*ℓ/B := by
      have hh := (le_div_iff₀ b).2 (show (coverNumber B P:ℝ)*B≤ off*B+slope*ℓ by linarith only [h])
      calc _ ≤ ((off:ℝ)*(B:ℝ)+slope*ℓ)/B := hh
           _ = _ := by field_simp [b.ne']
    have h1 := mul_le_mul_of_nonneg_left hh hσ.le
    have h2 := mul_le_mul_of_nonneg_right reserve hℓ
    linarith [show σ*((slope:ℝ)*ℓ/B)=(σ*slope/B)*ℓ by ring]
  have hterm : σ*(coverNumber B P:ℝ)≤ A*Real.exp (w*ℓ) := by
    calc _ ≤ σ*off+w*ℓ := hm.trans (by nlinarith [mul_nonneg hw hℓ])
         _ ≤ Real.exp (σ*off+w*ℓ) := (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _)
         _ = _ := Real.exp_add _ _
         _ ≤ _ := mul_le_mul_of_nonneg_right hA (Real.exp_pos _).le
  have face : ((faces P).card:ℝ)≤(P.card:ℝ)*((Fintype.card PlaqAxes*4:ℕ):ℝ) := by exact_mod_cast count P
  have size : (P.card:ℝ)≤(coverNumber B P:ℝ)*(2*B+1)^4 := by
    exact_mod_cast (by simpa [two_mul] using Corona.pays P B : P.card≤ coverNumber B P*(2*B+1)^4)
  have lim := mul_le_mul_of_nonneg_right size (Nat.cast_nonneg (Fintype.card PlaqAxes*4))
  have cap' : (coverNumber B P:ℝ)≤(A*Real.exp (w*ℓ))/σ := (le_div_iff₀ hσ).2 (by linarith only [hterm])
  calc _ ≤ (coverNumber B P:ℝ)*(2*(B:ℝ)+1)^4*((Fintype.card PlaqAxes*4:ℕ):ℝ) := face.trans lim
       _ ≤ ((A*Real.exp (w*ℓ))/σ)*(2*(B:ℝ)+1)^4*((Fintype.card PlaqAxes*4:ℕ):ℝ) :=
         mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right cap' (by positivity)) (Nat.cast_nonneg _)
       _ = _ := by ring

end YM.Integration.ManuscriptQLocalIncidentMasks
end

/-! One genuine normalized Wilson transition, with the signed source perturbation measured in the physical coarse law. -/

noncomputable section
namespace YM.Integration.ManuscriptQLocalMeasuredMarkTransport
open Function Set Filter Finset MeasureTheory Lattice Wilson RG RG.Shoot Marker OPE.Therm Comparison.RG02
open ManuscriptQLocalRegularConditional ManuscriptQLocalMeasuredMarkDifference
open scoped Classical BigOperators Topology
variable {V : Type} [DecidableEq V] [Fintype V] {Γ : Census V} {w : V→ℝ} (hw : ∀i,0< w i)
variable {G : Gauge} (C : Family G) (hC : C.Makes) {N m p : ℕ} (hm : m< N)
local notation "F" => Config G (C.side (m+1) p)
local notation "D" => Config G (C.side m p)
local notation "μf" => scene C.path N p (m+1)
local notation "μc" => scene C.path N p m

def row (X : F→ Poly Γ) (s : Γ.Mode) (T : F) : ℂ := (Poly.pass (X T)).part s

def bank (X : F→ Poly Γ) (U : D) : Poly Γ := moment C (N:=N) U (fun _=>X) 1

include hw in
theorem env (X : F→ Poly Γ) (hX : Measurable X) {b : ℝ} (hx : ∀T,Poly.price w (X T)≤ b) (s : Γ.Mode) :
    Envelope (row C X s) := by
  refine ⟨(Poly.get s).continuous.measurable.comp (Poly.pass_cont.measurable.comp hX),
    expBill (Fintype.card V) b/Poly.toll w s,fun T=>?_⟩
  apply (le_div_iff₀ (Poly.worth hw s)).2
  simpa only [row,mul_comm] using (Poly.member hw s (Poly.pass (X T))).trans (exp_price hw (hx T))

private theorem sub {S : Type} [MeasurableSpace S] {f g : S→ℂ} (hf : Envelope f) (hg : Envelope g) :
    Envelope (fun x=>f x-g x) := by
  obtain ⟨a,ha⟩ := hf.cost
  obtain ⟨b,hb⟩ := hg.cost
  exact ⟨hf.meas.sub hg.meas,a+b,fun x=>(norm_sub_le _ _).trans (add_le_add (ha _) (hb _))⟩

private theorem l1 {S : Type} [MeasurableSpace S] (μ : Measure S) [IsFiniteMeasure μ] {f : S→ℂ}
    (hf : Envelope f) : Integrable f μ := by
  obtain ⟨a,ha⟩ := hf.cost
  exact Integrable.of_bound hf.meas.aestronglyMeasurable a (ae_of_all _ ha)

include hC hm in
theorem each (X Y : F→ Poly Γ) (s : Γ.Mode) (hx : Envelope (row C X s)) (hy : Envelope (row C Y s)) (U : D) :
    (bank C (N:=N) X U).part s-(bank C (N:=N) Y U).part s =
    actualAverage C (N:=N) (fun T=>row C X s T-row C Y s T) U := by
  obtain ⟨a,ha⟩ := hx.cost
  obtain ⟨b,hb⟩ := hy.cost
  rw [bank,moment_part,bank,moment_part]
  unfold actualAverage
  simp_rw [smul_sub]
  exact (integral_sub (actualAverage_integrable C hC hm hx.meas.aestronglyMeasurable ha U)
      (actualAverage_integrable C hC hm hy.meas.aestronglyMeasurable hb U)).symm

include hC hm in
theorem marginal {g : F→ℂ} (hg : Envelope g) :
    ∫U,‖actualAverage C (N:=N) g U‖ ∂μc ≤ ∫T,‖g T‖ ∂μf := by
  have normcheck := ActualWilsonAbsoluteTransport.first C hC hm (ActualWilsonAbsoluteTransport.weighted C hC hm hg)
    (Nat.le_succ m)
  rwa [actualTransport_step C hC hm g (Nat.lt_succ_self m),actualTransport_base C hC hm g] at normcheck

include hw hC hm in
/-- The complete finite sum over every mode, using the original kernels,
weights and signed joint averaging, at a genuinely normalized Wilson step. -/
theorem measure (X Y : F→ Poly Γ) (hx : ∀s,Envelope (row C X s)) (hy : ∀s,Envelope (row C Y s)) :
    ∫U,Poly.price w (bank C (N:=N) X U-bank C (N:=N) Y U) ∂μc ≤
      ∫T,Poly.price w (Poly.pass (X T)-Poly.pass (Y T)) ∂μf := by
  letI : IsProbabilityMeasure μf := probability (H:=C.path) (p:=p) hC.wilson hm
  letI : IsProbabilityMeasure μc := probability (H:=C.path) (p:=p) hC.wilson hm.le
  let f := fun (s:Γ.Mode) (T:F)=>row C X s T-row C Y s T
  have hf s : Envelope (f s) := sub (hx s) (hy s)
  have ha s : Envelope (actualAverage C (N:=N) (f s) : D→ℂ) := WilsonForwardMeasurable.average hC hm (hf s)
  have e (s : Γ.Mode) (U : D) : (bank C (N:=N) X U-bank C (N:=N) Y U).part s=actualAverage C (N:=N) (f s) U :=
    each C hC hm X Y s (hx s) (hy s) U
  have z (s : Γ.Mode) (T : F) : (Poly.pass (X T)-Poly.pass (Y T)).part s=f s T := rfl
  simp only [Poly.price,e,z]
  rw [integral_finsetSum _ (fun s _=>(l1 μc (ha s)).norm.const_mul _),
      integral_finsetSum _ (fun s _=>(l1 μf (hf s)).norm.const_mul _)]
  apply Finset.sum_le_sum
  intro s _
  rw [integral_const_mul,integral_const_mul]
  exact mul_le_mul_of_nonneg_left (marginal C hC hm (hf s)) (Poly.worth hw s).le

omit [Fintype V] in
include hw in
private theorem integral_price (μ : Measure F) [IsFiniteMeasure μ] (X Y : F→ Poly Γ)
    (my : Measurable X) (mz : Measurable Y) {B : ℝ} (xy : ∀T,Poly.price w (X T)≤ B)
    (yy : ∀T,Poly.price w (Y T)≤ B) : Integrable (fun T=>Poly.price w (X T-Y T)) μ := by
  unfold Poly.price
  apply integrable_finsetSum
  intro s _
  have o (Z : F→ Poly Γ) (z : Measurable Z) (x : ∀T,Poly.price w (Z T)≤ B) : Envelope (fun T=>(Z T).part s) := by
    refine ⟨(Poly.get s).continuous.measurable.comp z,B/Poly.toll w s,fun T=>?_⟩
    exact (le_div_iff₀ (Poly.worth hw s)).2 (by simpa only [mul_comm] using (Poly.member hw s (Z T)).trans (x T))
  exact (l1 μ (sub (o X my xy) (o Y mz yy))).norm.const_mul _

/-- The full physical conditional connected source before either mask is
removed. It depends only on the actual admitted field function at this step. -/
def logarithm (X : F→ Poly Γ) (U : D) : Poly Γ := Extra.Trajectories.connected (bank C (N:=N) X U)

include hw hC hm in
theorem compared (X Y : F→ Poly Γ) (hX : Measurable X) (hY : Measurable Y) {B : ℝ} (hB : 0≤ B)
    (hx : ∀T,Poly.price w (X T)≤ B) (hy : ∀T,Poly.price w (Y T)≤ B)
    (quietX : ∀T,(X T).part Γ.quiet=0) (quietY : ∀T,(Y T).part Γ.quiet=0) :
    let n := Fintype.card V
    let v := (Fintype.card Γ.Mode:ℝ)*expBill n B
    ∫U,Poly.price w (logarithm C (N:=N) X U-logarithm C (N:=N) Y U) ∂μc ≤
      (logMod n v*expMod n B)*(∫T,Poly.price w (X T-Y T) ∂μf) := by
  letI : IsProbabilityMeasure μf := probability (H:=C.path) (p:=p) hC.wilson hm
  letI : IsProbabilityMeasure μc := probability (H:=C.path) (p:=p) hC.wilson hm.le
  let n := Fintype.card V
  let v := (Fintype.card Γ.Mode:ℝ)*expBill n B
  have vb : 0≤ v := mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun _ _=>mul_nonneg (norm_nonneg _) (pow_nonneg hB _))
  have pe : 0≤ expMod n B := nonnegative _ _ _ hB
  have pl : 0≤ logMod n v := nonnegative _ _ _ (by linarith : 0≤ v+1)
  have ex := env hw C X hX hx
  have ey := env hw C Y hY hy
  have edge s := sub (ex s) (ey s)
  have qc (S : F→ Poly Γ) (hs : ∀T,(S T).part Γ.quiet=0) (U : D) := moment_quiet C hC hm U (fun _=>S) 1 hs
  have bound (S : F→ Poly Γ) (hs : ∀T,Poly.price w (S T)≤ B) (U : D) := moment_price C hC hm U (fun _=>S) hw 1 hs
  have hb : Integrable (fun U=>Poly.price w (bank C (N:=N) X U-bank C (N:=N) Y U)) μc := by
    unfold Poly.price
    apply integrable_finsetSum
    intro s _
    have real := (l1 μc (WilsonForwardMeasurable.average hC hm (edge s))).norm.const_mul (Poly.toll w s)
    apply real.congr (Filter.Eventually.of_forall fun U=>?_)
    change Poly.toll w s*‖actualAverage C (N:=N) (fun T=>row C X s T-row C Y s T) U‖=
      Poly.toll w s*‖(bank C (N:=N) X U).part s-(bank C (N:=N) Y U).part s‖
    rw [each C hC hm X Y s (ex s) (ey s)]
  have hg := integral_price hw C μf X Y hX hY hx hy
  calc _ ≤ ∫U,logMod n v*Poly.price w (bank C (N:=N) X U-bank C (N:=N) Y U) ∂μc := by
         apply integral_mono_of_nonneg (ae_of_all _ fun U=>Poly.nonnegative hw _) (hb.const_mul _)
         exact ae_of_all _ fun U=>connected hw (qc X quietX U) (qc Y quietY U) (bound X hx U) (bound Y hy U)
       _ = _ := integral_const_mul _ _
       _ ≤ logMod n v*(∫T,Poly.price w (Poly.pass (X T)-Poly.pass (Y T)) ∂μf) :=
         mul_le_mul_of_nonneg_left (measure hw C hC hm X Y ex ey) pl
       _ ≤ logMod n v*(∫T,expMod n B*Poly.price w (X T-Y T) ∂μf) := by
         apply mul_le_mul_of_nonneg_left _ pl
         apply integral_mono_of_nonneg (ae_of_all _ fun T=>Poly.nonnegative hw _) (hg.const_mul _)
         exact ae_of_all _ fun T=>passing hw (hx T) (hy T)
       _ = _ := by rw [integral_const_mul];ring

include hC hm in
theorem measured_bank (X : F→ Poly Γ) (hx : ∀s,Envelope (row C X s)) : Measurable (bank C (N:=N) X) := by
  have eqn : bank C (N:=N) X = fun U=>∑s:Γ.Mode,Poly.send s (actualAverage C (N:=N) (row C X s) U) := by
    funext U
    calc
      _ = ∑s:Γ.Mode,Poly.send s ((bank C (N:=N) X U).part s):=(Poly.studs _).symm
      _ = _ := Finset.sum_congr rfl fun s _=>congrArg (Poly.send s) (moment_part C (N:=N) U (fun _=>X) 1 s)
  rw [eqn]
  exact Finset.measurable_sum _ fun s _=>(Overlay.Bands.sends s).measurable.comp (WilsonForwardMeasurable.average hC hm (hx s)).meas

include hC hm in
theorem measured_log (X : F→ Poly Γ) (hx : ∀s,Envelope (row C X s)) (quiet : ∀T,(X T).part Γ.quiet=0) :
    Measurable (logarithm C (N:=N) X) := by
  have eqn : logarithm C (N:=N) X = fun U=>RG02.Marks.logTable (bank C (N:=N) X U) :=
    funext fun U=>RG02.Marks.connected_eq_logTable (moment_quiet C hC hm U (fun _=>X) 1 quiet)
  rw [eqn]
  unfold RG02.Marks.logTable
  exact Finset.measurable_sum _ fun i _=>(measurable_const (a:=(-1:ℂ)^i/(i+1:ℂ))).smul
    (((measured_bank C hC hm X hx).sub (measurable_const (a:=(1:Poly Γ)))).pow_const (i+1))

omit [Fintype V] in
include hw in
private theorem price_sub (x y : Poly Γ) : Poly.price w (x-y)≤ Poly.price w x+Poly.price w y := by
  simpa only [sub_eq_add_neg,←neg_one_smul ℂ y,Poly.adapted,norm_neg,norm_one,one_mul] using (Poly.addition hw x (-y))

include hw hC hm in
theorem finite_moment (X Y : F→ Poly Γ) (hX : Measurable X) (hY : Measurable Y) {B : ℝ}
    (hx : ∀T,Poly.price w (X T)≤ B) (hy : ∀T,Poly.price w (Y T)≤ B)
    (qx : ∀T,(X T).part Γ.quiet=0) (qy : ∀T,(Y T).part Γ.quiet=0) (j : ℕ) :
    Integrable (fun U=>(Poly.price w (logarithm C (N:=N) X U-logarithm C (N:=N) Y U))^j) μc := by
  letI : IsProbabilityMeasure μc := probability (H:=C.path) (p:=p) hC.wilson hm.le
  let n := Fintype.card V
  let v := (Fintype.card Γ.Mode:ℝ)*expBill n B
  let Δ := fun U=>Poly.price w (logarithm C (N:=N) X U-logarithm C (N:=N) Y U)
  have mΔ : Measurable Δ := (Poly.price_cont w).measurable.comp
    ((measured_log C hC hm X (env hw C X hX hx) qx).sub (measured_log C hC hm Y (env hw C Y hY hy) qy))
  have bound (S:F→ Poly Γ) (qs:∀T,(S T).part Γ.quiet=0) (hs:∀T,Poly.price w (S T)≤ B) (U:D) :
      Poly.price w (logarithm C (N:=N) S U)≤logBill n v := by
    exact conditional_price C hC hm U (fun _=>S) hw 1 hs qs
  have hΔ (U:D) : Δ U≤2*logBill n v := (price_sub hw _ _).trans (by
    simpa only [two_mul] using add_le_add (bound X qx hx U) (bound Y qy hy U))
  apply Integrable.of_bound (mΔ.pow_const j).aestronglyMeasurable ((2*logBill n v)^j)
  apply ae_of_all
  intro U
  rw [Real.norm_of_nonneg (pow_nonneg (Poly.nonnegative hw _) _)]
  exact pow_le_pow_left₀ (Poly.nonnegative hw _) (hΔ U) _

include hw hC hm in
theorem powers (X Y : F→ Poly Γ) (hX : Measurable X) (hY : Measurable Y) {B : ℝ} (hB : 0≤ B)
    (hx : ∀T,Poly.price w (X T)≤ B) (hy : ∀T,Poly.price w (Y T)≤ B)
    (qx : ∀T,(X T).part Γ.quiet=0) (qy : ∀T,(Y T).part Γ.quiet=0) (j : ℕ) :
    let n := Fintype.card V
    let v := (Fintype.card Γ.Mode:ℝ)*expBill n B
    ∫U,(Poly.price w (logarithm C (N:=N) X U-logarithm C (N:=N) Y U))^(j+1) ∂μc ≤
      (2*logBill n v)^j*(logMod n v*expMod n B)*(∫T,Poly.price w (X T-Y T) ∂μf) := by
  letI : IsProbabilityMeasure μc := probability (H:=C.path) (p:=p) hC.wilson hm.le
  let n := Fintype.card V
  let v := (Fintype.card Γ.Mode:ℝ)*expBill n B
  let z := fun U=>Poly.price w (logarithm C (N:=N) X U-logarithm C (N:=N) Y U)
  let a := 2*logBill n v
  have h0 U : 0≤ z U := Poly.nonnegative hw _
  have bound (S:F→ Poly Γ) (qs:∀T,(S T).part Γ.quiet=0) (hs:∀T,Poly.price w (S T)≤ B) (U:D) :
      Poly.price w (logarithm C (N:=N) S U)≤logBill n v := by
    exact conditional_price C hC hm U (fun _=>S) hw 1 hs qs
  have high U : z U≤ a := (price_sub hw _ _).trans (by
    simpa only [a,two_mul] using add_le_add (bound X qx hx U) (bound Y qy hy U))
  have hz : Measurable z := (Poly.price_cont w).measurable.comp
    ((measured_log C hC hm X (env hw C X hX hx) qx).sub (measured_log C hC hm Y (env hw C Y hY hy) qy))
  have int : Integrable z μc := Integrable.of_bound hz.aestronglyMeasurable a
    (ae_of_all _ fun U=>by simpa only [Real.norm_eq_abs,abs_of_nonneg (h0 U)] using high U)
  have ha : 0≤ a := (h0 1).trans (high 1)
  calc _ ≤ ∫U,a^j*z U ∂μc := by
         apply integral_mono_of_nonneg (ae_of_all _ fun U=>pow_nonneg (h0 U) _) (int.const_mul _)
         apply ae_of_all
         intro U
         change z U ^ (j+1) ≤ a ^ j * z U
         rw [pow_succ]
         exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (h0 U) (high U) j) (h0 U)
       _ = _ := integral_const_mul _ _
       _ ≤ a^j*((logMod n v*expMod n B)*(∫T,Poly.price w (X T-Y T) ∂μf)) :=
         mul_le_mul_of_nonneg_left (compared hw C hC hm X Y hX hY hB hx hy qx qy) (pow_nonneg ha _)
       _ = _ := by ring

end YM.Integration.ManuscriptQLocalMeasuredMarkTransport
end

/-! The exposed fine source bill on the actual original Laurent and mask supports. -/

noncomputable section
namespace YM.Integration.ManuscriptQLocalRawSourceRoot
open Filter Finset MeasureTheory Lattice RG RG.Shoot Wilson Marker LocalComparison
open Comparison.Density.RenderM Comparison.Density.RenderM.Token ActualRunPacketRetuning
open ManuscriptQLocalOriginalConditionalTail ManuscriptQLocalIncidentMasks
open scoped Classical BigOperators Topology
variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] {Γ : Census V} {n : Side}
  {D : V→ ComparisonDensity.Address.Orbit} (P : MarkedPackets D G n Γ)
  {q : BudgetPoint} {L : V→ Support n} {region : Comparison.Density.Testing.Region (fun v=>(D v).Mood) n}
  {w : V→ℝ} {g width budget : ℝ} {off slope : ℕ} (H : P.Paid q L region w g width budget off slope)

def principal (u : ℝ) (i : Live P) : ℝ := ‖(g:ℂ)^P.power i‖*(token P i).coin*u^P.rank i

def base (i : Live P) : ℝ := Poly.toll w (P.mode i)*principal P (g:=g) 2 i

def fare (i : Live P) : ℝ := base P (g:=g) (w:=w) i*Real.exp (width*(token P i).fall)

omit [Fintype V] in
include H in
theorem row (x : IndependentTests D) (i : Live P) (T : Config G n) :
    ‖P.term (testInclusion D x) g T i‖≤ principal P (g:=g) 2 i := by
  let t := token P i
  let z := testInclusion D x
  have hc := H.coefficient i t (chosen P i)
  have cap := WilsonCurvatureEndpoints.cold t z (hc.2 x) 2 (by norm_num) T (fun j=>G.chord_le_two _)
  simp only [MarkedPackets.term,chosen P i,norm_mul]
  exact (mul_le_mul_of_nonneg_left cap (norm_nonneg _)).trans_eq (by unfold principal;ring)

include H in
include H in
theorem roots : SumBudget (fare P (g:=g) (w:=w) (width:=width))
    ((Fintype.card V:ℝ)*((2:ℝ)^P.rankCap*budget)) := by
  let old := fun (v : V) (i : ℕ)=> if v∈(P.mode i).val then match P.packet i with
    | none=>0
    | some T=>Poly.toll w (P.mode i)*‖(g:ℂ)^P.power i‖*T.coin*Real.exp (width*T.fall) else 0
  let a := fare P (g:=g) (w:=w) (width:=width)
  have hb (i : Live P) : 0≤ a i := by
    have h := (H.coefficient i (token P i) (chosen P i)).1
    have ht := (Poly.worth H.positive (P.mode i)).le
    dsimp [a,fare,base,principal];positivity
  have each (v : V) : SumBudget (fun i:Live P=>if v∈(P.mode i).val then a i else 0)
      ((2:ℝ)^P.rankCap*budget) := by
    refine Push.AbsoluteSums.budget_of_sum (fun i=>by split <;> simp [hb]) (fun e=>?_)
    calc _ ≤ ∑i∈e,(2:ℝ)^P.rankCap*old v i := by
           refine Finset.sum_le_sum fun i _=>?_
           by_cases hv : v∈(P.mode i).val
           · have h₀ := (H.coefficient i (token P i) (chosen P i)).1
             have h₁ := (Poly.worth H.positive (P.mode i)).le
             have h := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (P.rank_bounded i (token P i) (chosen P i))
             let y:=Poly.toll w (P.mode i)*‖(g:ℂ)^P.power i‖*(token P i).coin*Real.exp (width*(token P i).fall)
             have y0:0≤y:=mul_nonneg (mul_nonneg (mul_nonneg h₁ (norm_nonneg _)) h₀) (Real.exp_pos _).le
             have lhs : a i=(2:ℝ)^P.rank i*y:=by dsimp [a,fare,base,principal,y];ring
             have rhs : old v i=y:=by simp only [old,if_pos hv,chosen P i];rfl
             rw [if_pos hv,lhs,rhs];exact mul_le_mul_of_nonneg_right h y0
           · simp [old,hv]
         _ = (2:ℝ)^P.rankCap*(∑i∈e.image Subtype.val,old v i) := by
           rw [Finset.mul_sum,Finset.sum_image (fun i _ j _ h=>Subtype.ext h)]
         _ ≤ _ := mul_le_mul_of_nonneg_left (by
          have q := ((H.roots v).2.1.sum_le_tsum (e.image Subtype.val) (fun i _=>(H.roots v).1 i)).trans (H.roots v).2.2
          apply le_trans _ q
          apply Finset.sum_le_sum;intro i _
          by_cases hv : v∈(P.mode i).val
          · cases hi:P.packet i <;> simp [old,hv,hi]
          · simp [old,hv]) (by positivity)
  have all := rooted_sumBudget hb (fun i:Live P=>Finset.nonempty_iff_ne_empty.mpr
    (fun h=>hot P i (Subtype.ext h))) each
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using all

include H in
omit [Fintype V] in
theorem masked (x : IndependentTests D) (i : Live P) (T : Config G n) (t : ℝ) :
    Poly.toll w (P.mode i)*‖P.term (testInclusion D x) g T i-masked t (token P i).plot
      (fun S=>P.term (testInclusion D x) g S i) T‖≤
        (failed (token P i).plot t).indicator (fun _=>base P (g:=g) (w:=w) i) T := by
  by_cases h : Disjoint (token P i).plot (flags t T)
  · simp [masked_eq _ _ _ _ h,failed,h,Set.indicator_of_notMem]
  · have h' : T∈failed (token P i).plot t := h
    rw [Set.indicator_of_mem h']
    simp only [masked_ne _ _ _ _ h,sub_zero]
    exact mul_le_mul_of_nonneg_left (row P H x i T) (Poly.worth H.positive _).le

def debit (t : ℝ) (i : Live P) (T : Config G n) : ℝ :=
  (failed (token P i).plot t).indicator (fun _=>base P (g:=g) (w:=w) i) T

omit [Fintype V] in
include H in
theorem debit_nonnegative (t : ℝ) (i : Live P) (T : Config G n) : 0≤ debit P (g:=g) (w:=w) t i T := by
  have b := (H.coefficient i (token P i) (chosen P i)).1
  have ht := (Poly.worth H.positive (P.mode i)).le
  unfold debit
  exact Set.indicator_nonneg (fun _ _=>by dsimp [base,ManuscriptQLocalRawSourceRoot.principal];positivity) _

include H in
theorem exposure (μ : Measure (Config G n)) [IsProbabilityMeasure μ]
    (t : ℝ) {d A : ℝ} (hd : 0≤ d) (hA : Real.exp (q.supportExponent*off)≤ A)
    (events : ∀i : Live P, μ.real (failed (token P i).plot t)≤(faces (token P i).plot).card*d) :
    let K := ((Fintype.card PlaqAxes*4:ℕ):ℝ)*(2*q.B+1)^4*(A/q.supportExponent)*d
    SumBudget (fun i : Live P=>∫T,debit P (g:=g) (w:=w) t i T ∂μ)
      (K*((Fintype.card V:ℝ)*((2:ℝ)^P.rankCap*budget))) := by
  let K := ((Fintype.card PlaqAxes*4:ℕ):ℝ)*(2*q.B+1)^4*(A/q.supportExponent)*d
  have ha := (Real.exp_pos _).le.trans hA
  have hK : 0≤ K := by dsimp [K];positivity [q.exponent_pos]
  have non (i:Live P):0≤∫T,debit P (g:=g) (w:=w) t i T ∂μ := integral_nonneg (fun T=>debit_nonnegative P H t i T)
  have hrow (i:Live P) : (∫T,debit P (g:=g) (w:=w) t i T ∂μ)≤ K*fare P (g:=g) (w:=w) (width:=width) i := by
    have hp := ManuscriptQLocalIncidentMasks.cover (token P i).plot q.B_pos q.exponent_pos H.width_pos.le
      (Nat.cast_nonneg _) hA (H.cover i (token P i) (chosen P i)) H.width_reserved
    have hprice : 0≤ base P (g:=g) (w:=w) i := by
      have b := (H.coefficient i (token P i) (chosen P i)).1
      have ht := (Poly.worth H.positive (P.mode i)).le
      dsimp [base,ManuscriptQLocalRawSourceRoot.principal];positivity
    have hval := mul_le_mul_of_nonneg_right ((events i).trans (mul_le_mul_of_nonneg_right hp hd)) hprice
    simpa only [debit,integral_indicator_const _ (measured (token P i).plot t),smul_eq_mul,K,fare,
      mul_comm,mul_left_comm,mul_assoc] using hval
  exact ⟨non,(Summable.of_nonneg_of_le non hrow ((roots P H).2.1.mul_left K)),
    (Summable.tsum_le_tsum hrow (Summable.of_nonneg_of_le non hrow ((roots P H).2.1.mul_left K))
      ((roots P H).2.1.mul_left K)).trans (by rw [tsum_mul_left];exact mul_le_mul_of_nonneg_left (roots P H).2.2 hK)⟩

end YM.Integration.ManuscriptQLocalRawSourceRoot
end

/-! Entire countable physical fine source and its honest independently masked version. -/

noncomputable section
namespace YM.Integration.ManuscriptQLocalOriginalFineMaskLoss
open Set Filter Finset MeasureTheory Lattice RG RG.Shoot Wilson Marker LocalComparison
open Comparison.Density.RenderM Comparison.Density.RenderM.Token ActualRunPacketRetuning
open ManuscriptQLocalOriginalConditionalTail ManuscriptQLocalIncidentMasks ManuscriptQLocalRawSourceRoot
open scoped Classical BigOperators Topology ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] {Γ : Census V} {n : Side}
  {D : V→ ComparisonDensity.Address.Orbit} (P : MarkedPackets D G n Γ)
  {q : BudgetPoint} {L : V→ Support n} {region : Comparison.Density.Testing.Region (fun v=>(D v).Mood) n}
  {w : V→ℝ} {g width budget : ℝ} {off slope : ℕ} (H : P.Paid q L region w g width budget off slope)
  (x : IndependentTests D)

def plain (i : Live P) (T : Config G n) := Poly.send (P.mode i) (P.term (testInclusion D x) g T i)
def regular (p : BudgetPoint) (i : Live P) (T : Config G n) := Poly.send (P.mode i) (field P p g x i T)

theorem native (T : Config G n) : P.read (testInclusion D x) g T = ∑'i:Live P,plain P (g:=g) x i T := by
  unfold MarkedPackets.read plain
  symm
  apply tsum_subtype_eq_of_support_subset (s:={i:ℕ | (P.packet i).isSome})
    (f:=fun i:ℕ=>Poly.send (P.mode i) (P.term (testInclusion D x) g T i))
  intro i hi
  cases e : P.packet i with
  | none=>exact (hi (by simp [MarkedPackets.term,e])).elim
  | some t=>change (P.packet i).isSome;simp [e]

omit [Fintype V] in
theorem row_borel (i : Live P) : Measurable (fun T=>P.term (testInclusion D x) g T i) := by
  apply Continuous.measurable
  simp only [MarkedPackets.term,chosen P i]
  unfold Token.read Token.touch Slot.atSite expandAt
  fun_prop

theorem full_borel : Measurable (P.read (testInclusion D x) g) := by
  simp_rw [show P.read (testInclusion D x) g = fun T=>∑'i:Live P,plain P (g:=g) x i T by funext T;exact native P x T]
  exact Measurable.tsum fun i=>(Overlay.Bands.sends (P.mode i)).measurable.comp (row_borel P x i)

omit [Fintype V] in
theorem mask_borel (p : BudgetPoint) : Measurable (source P p g x 1) := by
  have h : source P p g x 1 = fun T=>∑'i:Live P,regular P (g:=g) x p i T := funext (physical P p g x)
  rw [h]
  exact Measurable.tsum fun i=>(Overlay.Bands.sends (P.mode i)).measurable.comp
    (masked_measurable _ _ _ (row_borel P x i))

include H in
omit [Fintype V] in
private theorem nonnegative (i : Live P) : 0≤ base P (g:=g) (w:=w) i := by
  have hc := (H.coefficient i (token P i) (chosen P i)).1
  have ht := (Poly.worth H.positive (P.mode i)).le
  dsimp [base,ManuscriptQLocalRawSourceRoot.principal];positivity

include H in
omit [Fintype V] in
private theorem charged (i : Live P) : base P (g:=g) (w:=w) i≤ fare P (g:=g) (w:=w) (width:=width) i := by
  have e := Real.one_le_exp (mul_nonneg H.width_pos.le (Nat.cast_nonneg ((token P i).fall)))
  simpa only [fare,mul_one] using mul_le_mul_of_nonneg_left e (nonnegative P H i)

def bound := (Fintype.card V:ℝ)*((2:ℝ)^P.rankCap*budget)

include H in
theorem original_rows (T : Config G n) : Summable (fun i:Live P=>plain P (g:=g) x i T) ∧
    Poly.price w (P.read (testInclusion D x) g T)≤ bound P (budget:=budget) := by
  have h := roots P H
  have byrow (i : Live P) : Poly.price w (plain P (g:=g) x i T) ≤ fare P (g:=g) (w:=w) (width:=width) i := by
    rw [plain,Poly.solo]
    exact (mul_le_mul_of_nonneg_left (row P H x i T) (Poly.worth H.positive _).le).trans (charged P H i)
  obtain ⟨summ,pay⟩ := Poly.budgeted H.positive h.2.1 byrow
  exact ⟨summ,by rw [native];exact pay.trans h.2.2⟩

include H in
theorem regular_rows (p : BudgetPoint) (T : Config G n) : Summable (fun i:Live P=>regular P (g:=g) x p i T) ∧
    Poly.price w (source P p g x 1 T)≤ bound P (budget:=budget) := by
  have h := roots P H
  have byrow (i : Live P) : Poly.price w (regular P (g:=g) x p i T) ≤ fare P (g:=g) (w:=w) (width:=width) i := by
    rw [regular,Poly.solo]
    by_cases z : Healthy p.threshold (token P i).plot T
    · simp only [field,masked_eq _ _ _ _ z]
      exact (mul_le_mul_of_nonneg_left (row P H x i T) (Poly.worth H.positive _).le).trans (charged P H i)
    · simp only [field,masked_ne _ _ _ _ z,norm_zero,mul_zero]
      exact h.1 i
  obtain ⟨summ,pay⟩ := Poly.budgeted H.positive h.2.1 byrow
  exact ⟨summ,by rw [physical];exact pay.trans h.2.2⟩

omit [Fintype V] in
private theorem projection (s : Γ.Mode) (a b : ℂ) : Poly.send s a-Poly.send s b=Poly.send s (a-b) := by
  ext j
  by_cases h : s=j
  · subst j;simp [Poly.part_send]
  · simp [Poly.part_send,Ne.symm h]

include H in
theorem point (p : BudgetPoint) (T : Config G n) :
    Poly.price w (P.read (testInclusion D x) g T-source P p g x 1 T) ≤ ∑'i:Live P,debit P (g:=g) (w:=w) p.threshold i T := by
  have orig := original_rows P H x T
  have reg := regular_rows P H x p T
  have witnessed (i : Live P) : debit P (g:=g) (w:=w) p.threshold i T ≤ fare P (g:=g) (w:=w) (width:=width) i := by
    unfold debit
    by_cases h : T∈failed (token P i).plot p.threshold
    · rw [Set.indicator_of_mem h];exact charged P H i
    · rw [Set.indicator_of_notMem h];exact (roots P H).1 i
  have supp := Summable.of_nonneg_of_le (fun i=>debit_nonnegative P H p.threshold i T) witnessed (roots P H).2.1
  have sums (i : Live P) : Poly.price w (plain P (g:=g) x i T-regular P (g:=g) x p i T) ≤ debit P (g:=g) (w:=w) p.threshold i T := by
    rw [plain,regular,projection,Poly.solo]
    exact masked P H x i T p.threshold
  rw [native,physical]
  change Poly.price w ((∑'i:Live P,plain P (g:=g) x i T)-(∑'i:Live P,regular P (g:=g) x p i T))≤_
  rw [←orig.1.tsum_sub reg.1]
  exact (Poly.budgeted H.positive supp sums).2

include H in
theorem means_quiet (p : BudgetPoint) (T : Config G n) :
    (P.read (testInclusion D x) g T).part Γ.quiet=0 ∧ (source P p g x 1 T).part Γ.quiet=0 := by
  constructor
  · rw [native,Poly.share (original_rows P H x T).1]
    simp [plain,Poly.part_send,fun i:Live P=>(hot P i).symm]
  · rw [physical]
    change (∑'i:Live P,regular P (g:=g) x p i T).part Γ.quiet=0
    rw [Poly.share (regular_rows P H x p T).1]
    simp [regular,Poly.part_send,fun i:Live P=>(hot P i).symm]

include H in
theorem integrated (μ : Measure (Config G n)) [IsProbabilityMeasure μ] (p : BudgetPoint)
    {d A : ℝ} (hd : 0≤ d) (hA : Real.exp (q.supportExponent*off)≤ A)
    (events : ∀i : Live P, μ.real (failed (token P i).plot p.threshold)≤(faces (token P i).plot).card*d) :
    let K := ((Fintype.card PlaqAxes*4:ℕ):ℝ)*(2*q.B+1)^4*(A/q.supportExponent)*d
    ∫T,Poly.price w (P.read (testInclusion D x) g T-source P p g x 1 T) ∂μ ≤ K*bound P (budget:=budget) := by
  let f := debit P (g:=g) (w:=w) p.threshold
  have hs := exposure P H μ p.threshold hd hA events
  have h0 (i : Live P) (T : Config G n) : 0≤ f i T := debit_nonnegative P H p.threshold i T
  have meas (i : Live P) : Measurable (f i) := measurable_const.indicator (ManuscriptQLocalIncidentMasks.measured _ _)
  have paid (T : Config G n) : SumBudget (fun i=>f i T) (bound P (budget:=budget)) := by
    have hg i : f i T≤ fare P (g:=g) (w:=w) (width:=width) i := by
      by_cases h : T∈failed (token P i).plot p.threshold
      · simpa only [f,debit,Set.indicator_of_mem h] using charged P H i
      · simpa only [f,debit,Set.indicator_of_notMem h] using (roots P H).1 i
    have s := Summable.of_nonneg_of_le (fun i=>h0 i T) hg (roots P H).2.1
    exact ⟨fun i=>h0 i T,s,(s.tsum_le_tsum hg (roots P H).2.1).trans (roots P H).2.2⟩
  have int (i : Live P) : Integrable (f i) μ := (integrable_const _).indicator (ManuscriptQLocalIncidentMasks.measured _ _)
  have hn : Summable (fun i=>∫T,‖f i T‖ ∂μ) := by
    have norm (i T) : ‖f i T‖=f i T := Real.norm_of_nonneg (h0 i T)
    simpa only [norm] using hs.2.1
  have full : Integrable (fun T=>∑'i,f i T) μ := (integrable_const (bound P (budget:=budget))).mono'
    (Measurable.tsum meas).aestronglyMeasurable (ae_of_all _ fun T=>by
      rw [Real.norm_of_nonneg (tsum_nonneg (fun i=>h0 i T))];exact (paid T).2.2)
  calc _ ≤ ∫T,∑'i,f i T ∂μ := integral_mono_of_nonneg (ae_of_all _ fun T=>Poly.nonnegative H.positive _) full
         (ae_of_all _ fun T=>point P H x p T)
       _ = ∑'i,∫T,f i T ∂μ := (integral_tsum_of_summable_integral_norm int hn).symm
       _ ≤ _ := hs.2.2

end YM.Integration.ManuscriptQLocalOriginalFineMaskLoss
end

/-! Fixed physical thermal window for the complete all-roster raw regular source. -/

noncomputable section
namespace YM.Integration.ManuscriptQLocalRawMaskCalendar
open Function Filter Set Finset MeasureTheory Lattice Wilson RG RG.Shoot Marker
open Function Filter Set Finset MeasureTheory Lattice Wilson RG RG.Supply Next.Rank Push.GridApprox WardBin.Wheels
open MergeProof PhysicalNext.Repeat.Legato PhysicalNext.Repeat Next.Scheduling Next.Scheduling.Clock
open Push.PriceCompiler Next.Foundations OPE.Therm
open Comparison.Density.RenderM Comparison.Density.RenderM.Token ActualRunPacketRetuning
open LocalComparison FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open ManuscriptQLocalRegularConditional ManuscriptQLocalMeasuredMarkDifference Pert.Asymptotics
open scoped Classical BigOperators Topology
variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] {Γ : Census V}
  (R : Run G) (hG : G.Simple) (W : Poetry R.family.path.levels) {J : Request V}
  (A : NumericSchedule R.family J)

include hG W in
theorem physical (d j : ℕ) : ∀ᶠ m:ℕ in atTop,∀z:LocalFormal.Datum R.family Γ,z.level=m→
    ∀ (F : AnalyticInput J A z) (x : IndependentTests J.tests),
    let n := Fintype.card V
    let g := regulatorRun R.family z.cutoff z.period (z.level+1)
    let q := A.inputNorm z.level
    let B := (R.family.path.rep z.cutoff z.period (z.level+1)).p
    let w := fun v=>F.inputRadii v/F.kernelCosts v
    let X := F.packets.read (testInclusion J.tests x) g
    let Y := ManuscriptQLocalOriginalConditionalTail.source F.packets B g x 1
    let L S := ManuscriptQLocalMeasuredMarkTransport.logarithm R.family (N:=z.cutoff) S
    let b := (n:ℝ)*((2:ℝ)^F.packets.rankCap*A.admittedCost z.level)
    let v := (Fintype.card Γ.Mode:ℝ)*expBill n b
    let K := ((Fintype.card PlaqAxes*4:ℕ):ℝ)*(2*q.B+1)^4*(A.admittedCost z.level/q.supportExponent)*
      (R.family.path.levels.clock.forcedAllowance (z.level+1))^d
    ∫U,(Poly.price w (L X U-L Y U))^(j+1) ∂scene R.family.path z.cutoff z.period z.level ≤
      (2*logBill n v)^j*(logMod n v*expMod n b)*(K*b) := by
  obtain ⟨j₀,hj₀⟩ := eventually_atTop.1 (ManuscriptQLocalIncidentMasks.hot W hG R.makes.wilson d)
  filter_upwards [eventually_ge_atTop j₀] with m hm z hz F x
  subst m
  have cash := hj₀ (z.level+1) (by omega)
  let gf := regulatorRun R.family z.cutoff z.period (z.level+1)
  let B := (R.family.path.rep z.cutoff z.period (z.level+1)).p
  let X := F.packets.read (testInclusion J.tests x) gf
  let Y := ManuscriptQLocalOriginalConditionalTail.source F.packets B gf x 1
  let n := Fintype.card V
  let b := (n:ℝ)*((2:ℝ)^F.packets.rankCap*A.admittedCost z.level)
  let v := (Fintype.card Γ.Mode:ℝ)*expBill n b
  let μ := scene R.family.path z.cutoff z.period (z.level+1)
  letI : IsProbabilityMeasure μ := probability (H:=R.family.path) (p:=z.period) R.makes.wilson z.below
  have H := F.input_paid
  have hb : 0≤ b := mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (by positivity) (A.admitted_cost_nonnegative _))
  have vb : 0≤ v := mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun _ _=>mul_nonneg (norm_nonneg _) (pow_nonneg hb _))
  have high (T) := ManuscriptQLocalOriginalFineMaskLoss.original_rows F.packets H x T
  have regular (T) := ManuscriptQLocalOriginalFineMaskLoss.regular_rows F.packets H x B T
  have quiet (T) := ManuscriptQLocalOriginalFineMaskLoss.means_quiet F.packets H x B T
  have raw := ManuscriptQLocalMeasuredMarkTransport.powers H.positive R.family R.makes z.below X Y
    (ManuscriptQLocalOriginalFineMaskLoss.full_borel F.packets x) (ManuscriptQLocalOriginalFineMaskLoss.mask_borel F.packets x B)
    hb (fun T=>(high T).2) (fun T=>(regular T).2) (fun T=>(quiet T).1) (fun T=>(quiet T).2) j
  apply raw.trans (mul_le_mul_of_nonneg_left (ManuscriptQLocalOriginalFineMaskLoss.integrated F.packets H x μ B
    (pow_nonneg (Real.exp_pos _).le d) F.cover_cost (fun i=>cash z.cutoff z.below z.period _)) ?_)
  have hL : 0≤ logBill n v := Finset.sum_nonneg fun i _=>mul_nonneg (norm_nonneg _) (pow_nonneg (by linarith : 0≤ v+1) _)
  have p := ManuscriptQLocalMeasuredMarkDifference.nonnegative (Finset.range n) (fun i=>(-1:ℂ)^i/(i+1:ℂ)) (fun i=>i+1) (by linarith : 0≤ v+1)
  have e := ManuscriptQLocalMeasuredMarkDifference.nonnegative (Finset.range (n+1)) (fun i=>(i.factorial:ℂ)⁻¹) id hb
  exact mul_nonneg (pow_nonneg (mul_nonneg (by norm_num) hL) _) (mul_nonneg p e)

end YM.Integration.ManuscriptQLocalRawMaskCalendar
end
