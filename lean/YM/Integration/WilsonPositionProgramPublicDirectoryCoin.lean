import YM.Integration.WilsonPositionCompactEpochSampling
import YM.Integration.WilsonPositionProgramPublicWideHearing

/-! Every positive order of the authentic finite Handoff on the same public
mesh. The measured auxiliary bare scalar can be chosen after the finite
directory; the degree and all tariffs precede both physical regulators. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 450000
noncomputable section
namespace YM.Integration.WilsonPositionProgramPublicDirectoryCoin
open Filter Set Finset Function Metric MeasureTheory Lattice Maxwell XSpace XSpace.Cirrus XSpace.Normalize
open XSpace.Structure1 FVA2 FVA2.Register FVA2.Scale MS MS.Land PowerSeries
open WilsonPositionRawFiling WilsonPositionProtectedTuplePrice
open private powers weight_one from YM.Integration.WilsonPositionProtectedTuplePrice
open private entry from YM.Integration.WilsonPositionCompactEpochSampling
open scoped Topology BigOperators Classical
variable {G:Gauge} (Z:WilsonPrescription G) {g:G.Simple}
    {M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))} {T:Prescription (Press.portDeck G)}
    {dial:Bool} (H:Main.Match Z g M T dial) {n d:ℕ} (v:Tags G d n) (q:ℕ)
    {K:Set (Points n)} (compact:IsCompact K) (sep:K⊆conf n)

include H compact sep in
theorem terms : ∃ C:ℝ, 0≤C ∧ ∀ᶠ i:ℕ in atTop,∀ {B} (P:Handoff.Directory Z i B),
    Handoff.Directory.budget G n d+q≤B → ∀ s:Sample n, s.F=Z.run.step i →
    Notch.Entry (1/16) s → familiar s∈K → ∀ k≤q,
    ‖WilsonPositionOriginalEpochQuadrature.point P d v s.layout k‖ ≤
      C*(1+WilsonPositionRawMesh.mass Z (Z.run.step i) q)^q := by
  obtain ⟨c,hc,fees⟩ := forms Z H v q compact sep (show (0:ℝ)<1/16 by norm_num)
  refine ⟨((q+1:ℕ):ℝ)*c*((q+1:ℕ):ℝ)^q,by positivity,?_⟩
  have use := (goesFront (Expense.Stretched.runs Z.run)).eventually (Rose.usable Z.scheme Z.criterion g)
  filter_upwards [fees,use] with i h use' B P cover s hs he hK k hk
  let m := Z.run.step i
  let w := weight Z q m
  let x := Reg.Point.story (Speed.forms_t Z.scheme Z.criterion s d) v
  let D := Rose.chosen Z.scheme Z.criterion m
  have hw := weight_one Z q m
  have z : constantCoeff D = 0 := Rose.zero_choice ..
  have ck :
      ‖WilsonPositionOriginalEpochQuadrature.point P d v s.layout k‖ ≤ ((q+1:ℕ):ℝ) * (c * w^q) := by
    rw [WilsonPositionBarePointCoefficient.read P d v s hs use' k (by omega)]
    change ‖coeff k (PowerSeries.subst D x)‖ ≤ _
    rw [FPS.coeff_substituted x z k]
    calc
      _ ≤ ∑ j∈range (k+1), ‖coeff j x • coeff k (D^j)‖ := norm_sum_le ..
      _ ≤ ∑ _j∈range (k+1), c*w^q := by
        apply sum_le_sum
        intro j hj
        have hj' : j≤q := by have := mem_range.mp hj; omega
        have hx : ‖coeff j x‖≤c := by simpa only [x,Reg.Point.story,coeff_mk] using h s hs he hK j hj'
        rw [smul_eq_mul,norm_mul]
        exact mul_le_mul hx ((powers Z q m j k hk).trans (pow_le_pow_right₀ hw hj')) (norm_nonneg _) hc
      _ ≤ _ := by
        rw [sum_const,card_range,nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.succ_le_succ hk) (mul_nonneg hc (pow_nonneg (zero_le_one.trans hw) _))
  calc _ ≤ ((q+1:ℕ):ℝ)*(c*w^q) := ck
       _ = _ := by dsimp [w,weight];rw [mul_pow]; ring

def drawValue {i B:ℕ} (P:Handoff.Directory Z i B) (u:ℝ) (x:pack n) : ℂ :=
  ∑ k∈range (q+1), WilsonPositionOriginalEpochQuadrature.point P d v x k*(u:ℂ)^k

include H compact sep in
theorem remainder : ∃ C:ℝ,0≤C ∧ ∀ᶠ i:ℕ in atTop, ∀ {B} (P:Handoff.Directory Z i B),
    Handoff.Directory.budget G n d+q≤B → ∀ s:Sample n, s.F=Z.run.step i →
    welcome s → familiar s∈K → ∀u:ℝ, |u|≤1 →
    ‖drawValue Z v q P u s.layout - WilsonPositionOriginalEpochQuadrature.point P d v s.layout 0‖ ≤
      C*((1+WilsonPositionRawMesh.mass Z (Z.run.step i) q)^q*|u|) := by
  obtain ⟨C,hC,ticket⟩ := terms Z H v q compact sep
  have fine:=H.onSchedule.eventually frontier.smaller
  have large:∀ᶠ i:ℕ in atTop,16≤((Z.run.step i).p.side.val:ℝ) :=
    (frontier.horizon.comp H.onSchedule).eventually_ge_atTop 16
  refine ⟨q*C,by positivity,?_⟩
  filter_upwards [ticket,fine,large] with i bill unit side B P cover s hs center near u hu
  let m:=Z.run.step i
  let A:=(1+WilsonPositionRawMesh.mass Z m q)^q
  have nonneg : 0≤A := by
    have h:0≤WilsonPositionRawMesh.mass Z m q:=Finset.sum_nonneg fun _ _=>abs_nonneg _
    exact pow_nonneg (by linarith) _
  have bought:=bill P cover s hs (entry s (by rw [hs];exact_mod_cast side) (by rw [hs];exact unit) center) near
  unfold drawValue
  rw [Finset.sum_range_succ',pow_zero,mul_one,add_sub_cancel_right]
  calc _ ≤ ∑ k∈range q, ‖WilsonPositionOriginalEpochQuadrature.point P d v s.layout (k+1)*(u:ℂ)^(k+1)‖ := norm_sum_le ..
       _ ≤ ∑ _k∈range q, C*A*|u| := by
         apply sum_le_sum
         intro k hk
         rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,pow_succ]
         have exp:=mul_le_mul_of_nonneg_right (pow_le_one₀ (abs_nonneg u) hu (n:=k)) (abs_nonneg u)
         simpa only [one_mul] using mul_le_mul (bought (k+1) (by have := mem_range.mp hk;omega))
           exp (by positivity) (mul_nonneg hC nonneg)
       _ = _ := by rw [sum_const,card_range,nsmul_eq_mul];ring

include H compact sep in
theorem original (l:Filter ℝ) {t:ℝ→ℝ} (pos:∀ᶠ r in l,0<t r)
    (small:Tendsto t l (𝓝 0)) (D:ℕ) (J:ℝ) {δ:ℝ} (hδ:0<δ) :
    ∀ᶠ r in l, ∀ i≥WilsonPositionAuxiliaryMesh.floor Z.run q (t r),
      (i:ℝ)≤J*(-Real.log (t r))^D → ∀ {B} (P:Handoff.Directory Z i B),
      Handoff.Directory.budget G n d+q≤B → ∀ s:Sample n,s.F=Z.run.step i →
      welcome s → familiar s∈K → ∀u:ℝ, |u|≤8*t r →
      ‖drawValue Z v q P u s.layout - WilsonPositionOriginalEpochQuadrature.point P d v s.layout 0‖ ≤ δ := by
  obtain ⟨C,hC,fees⟩ := remainder Z H v q compact sep
  obtain ⟨i₀,hi⟩ := eventually_atTop.mp fees
  have funded:=WilsonPositionBareScalarDiagonal.paid Z H q D J l pos small (δ:=δ/(8*(1+C))) (by positivity)
  have starts:=(WilsonPositionAuxiliaryMesh.grows Z.run q l pos small).eventually_ge_atTop i₀
  filter_upwards [funded,starts,pos,small.eventually (gt_mem_nhds (show (0:ℝ)<1/8 by norm_num))] with r wages floor positive low i ge le B P cover s hs hc hK u hu
  let A:=(1+WilsonPositionRawMesh.mass Z (Z.run.step i) q)^q
  have h:0≤WilsonPositionRawMesh.mass Z (Z.run.step i) q := Finset.sum_nonneg fun _ _=>abs_nonneg _
  have ha:0≤A := pow_nonneg (by linarith) _
  have used:=hi i (floor.trans ge) P cover s hs hc hK u (by linarith)
  have room:= wages i ge le
  rw [abs_of_pos positive] at room
  have spent:= (le_div_iff₀ (by positivity:0<8*(1+C))).mp room
  change A*t r*(8*(1+C))≤δ at spent
  change _≤C*(A*|u|) at used
  exact used.trans (by nlinarith [mul_nonneg hC (mul_nonneg ha (sub_nonneg.mpr hu)),mul_nonneg ha positive.le])
end YM.Integration.WilsonPositionProgramPublicDirectoryCoin
