import YM.Integration.WilsonPhysicalHistoryRetainedSpringTemperature

/-! One numerical allowance at the reporting date covers all later cutoffs and
all periods on the entire genuine incoming roster, at each occupied site. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.OriginalMarkedRunAction
open Filter Lattice Wilson RG Precision Comparison.RG02 Comparison.RG02.Assembly
open PhysicalNext.Repeat.Legato WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Physical WilsonLimitConstruction
open scoped Topology BigOperators Classical
variable {G : Gauge}

theorem period_packet_price (Z : SeriesA G) (r : ℕ) {b c : ℝ} (positive : 0≤b) (unit : |c| ≤ 1)
    (grades : fromBefore Z (r+1)) :
    packetBill Z c b ≤ (Z.length:ℝ)*(b*2^(r+2)) := by
  induction Z with
  | nil => simp [packetBill]
  | cons a z ih =>
    have grade:=grades a (List.mem_cons_self ..)
    have rank:=a.rankA
    have power : (2:ℝ)^(a.rise+2) ≤ 2^(r+2) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have one : |c|^(a.grade-a.rise) ≤ 1:=pow_le_one₀ (abs_nonneg _) unit
    have pay : |c|^(a.grade-a.rise)*(b*2^(a.rise+2)) ≤ b*2^(r+2) :=
      (mul_le_of_le_one_left (by positivity) one).trans (mul_le_mul_of_nonneg_left power positive)
    have tail:=ih (fun a h=>grades a (List.mem_cons_of_mem _ h))
    simp only [packetBill,List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one,add_mul,one_mul] at tail ⊢
    linarith

def springAllowance (R : Run G) (T : Credit) (j r : ℕ) (b : ℝ) : ℝ :=
  let D:=R.family.path.levels.params j
  (1/2:ℝ)*(quadraticBill D.clip D.paths+24*D.paths)+
    T.buy (zz R.family.path.levels j)*(24*D.paths)+
      (3*R.family.path.levels.clock.hatBeta j)*((meterPre (r+1):ℝ)*(b*2^(r+2)))

theorem cofinal_site_allowance (R : Run G) (simple : G.Simple) (v : ℕ→Gear G→ℝ)
    (rows : FundedMarkedCoverRows.prices v R.kit) (r : ℕ) :
    ∃ T : Credit, ∀ᶠ j : ℕ in atTop, ∀ N>j,∀ n : ℕ,∀ {σ b : ℝ} (Z : SeriesA G),
      Draw Z σ b → fromBefore Z (r+1) → Z.length ≤ meterPre (r+1) →
      let g:=Pert.Asymptotics.regulatorRun R.family N n j
      springSiteBill R N j r Z g b ≤ springAllowance R T j r b := by
  obtain ⟨T,paid⟩:=cofinal_temperature R simple v rows r
  refine ⟨T,?_⟩
  filter_upwards [paid] with j earn N later n σ b Z drawn grades size
  obtain ⟨alpha,tail,_,_,c,p⟩:=earn N later n
  let D:=R.family.path.levels.params j
  have paths:=D.paths_pos.le
  have q : 0≤quadraticBill D.clip D.paths:=by unfold quadraticBill; positivity
  have β : 0≤R.family.path.levels.clock.hatBeta j :=
    le_trans zero_le_one (R.family.path.levels.fits.delayed j).le
  let g:=Pert.Asymptotics.regulatorRun R.family N n j
  let cl:=g/Real.sqrt (finitePitch R N j r g)
  have charge:=period_packet_price Z r drawn.1 c grades
  have bill : 0≤packetBill Z cl b:=by
    unfold packetBill
    apply List.sum_nonneg
    intro a ha
    obtain ⟨w,_,rfl⟩:=List.mem_map.mp ha
    have h:=drawn.1
    positivity
  have bound : (Z.length:ℝ) ≤ (meterPre (r+1):ℝ) := by exact_mod_cast size
  unfold springSiteBill springAllowance
  apply add_le_add (add_le_add (mul_le_mul_of_nonneg_right tail (add_nonneg q (by positivity)))
    (mul_le_mul_of_nonneg_right alpha (by positivity))) 
  exact mul_le_mul p (charge.trans (mul_le_mul_of_nonneg_right bound (mul_nonneg drawn.1 (by positivity)))) bill (by positivity)

end YM.Integration.OriginalMarkedRunAction
