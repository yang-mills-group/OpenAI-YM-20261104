import YM.Integration.WilsonThermometerCourseMoments
import YM.Integration.WilsonFirstReceivedGalleryRegular
import YM.Integration.WilsonReceivedInheritedFee

/-! Remove the actual issued regular residual on the fully interacting
three-source post, before testing it against any older Wilson law. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerRegularCofactors
open Finset Function Filter MeasureTheory Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler AllOrder.Transit.WheelP
open QuadraticLocal.Rebirth QuadraticLocal.Affinity Pressure OriginalForcedAddresses
open FVA1 WilsonPositionThermometerCapStation WilsonPositionThermometerGradedSource
open WilsonThermometerCourseHearing WilsonThermometerCourseResidual WilsonThermometerCourseIntake
open MergeProof MergeProof.East MeasureTheory Comparison.RG02 Comparison.RG02.Order
open Extraction Table Climb Trace.Pilot Next.Rank Next.UVStress ConnectedActivityE6
open IterationFour Push.AbsoluteSums.Animals OPE.Therm WilsonPositionThermometerGradedReading
open scoped Classical BigOperators Topology
local notation "J" => Stock.census (Fin 3)
local notation "modes" => (Fintype.card ((J).Mode) : ℝ)

private theorem logCost {G : Gauge} {n : Side} {T I : Type} {a b : ℝ} {o : Fin 3 → Site n}
    {P : RG.Rep G n} (L : Lamps T I G P.p o J) {w : Fin 3 → ℝ} (hw : ∀ j, 0 < w j)
    (fund : L.Paid w P.p.B a b) (ha : 0 ≤ a) (t : T) (U : Config G n) :
    Poly.price w (L.log t U) ≤ modes*b := by
  have bp : 0 ≤ b := Push.AbsoluteSums.budget_nonneg (fund.budget.choose_spec.2.2 (o 0))
  calc
    _ ≤ ∑ _s : (J).Mode,b := by
      apply Finset.sum_le_sum
      intro s _
      by_cases hs : s.val.Nonempty
      · obtain ⟨v,hv⟩ := hs
        exact WilsonFirstReceivedGalleryRegular.occupied L fund ha hw t U s v hv
      · have eq : s=(J).quiet := Subtype.ext (Finset.not_nonempty_iff_eq_empty.mp hs)
        rw [eq,Lamps.quiet_of_hasSum t U (fund.sums ha hw t U),norm_zero,mul_zero]
        exact bp
    _ = _ := by simp

private theorem discount (w : Fin 3 → ℝ) (hw : ∀ j, 0 < w j) (r : Poly J)
    {d : ℝ} (bill : Poly.price w r ≤ d) (small : d ≤ 1) :
    Poly.price w (1-Poly.pass (-r)) ≤ 4*d := by
  have d0 := (Poly.nonnegative hw r).trans bill
  have neg : Poly.price w (-r) = Poly.price w r := by simp only [Poly.price,Poly.part_neg,norm_neg]
  have zero : Poly.price w (0 : Poly J) ≤ d := by rw [Poly.zero_price]; exact d0
  have exp := WilsonThermometerCourseMoments.seven w hw 0 (-r) zero (neg.le.trans bill)
  rw [Next.Rank.Exponential.pass_zero,zero_sub,neg_neg] at exp
  have power : (1+d)^2 ≤ 4 := by nlinarith only [sq_nonneg (1-d),mul_nonneg (show 0 ≤ 1-d by linarith) (show 0 ≤ 3+d by linarith)]
  exact exp.trans (mul_le_mul power bill (Poly.nonnegative hw _) (by norm_num))

private theorem ordinary (w : Fin 3 → ℝ) (hw : ∀ j, 0 < w j) (S r : Poly J)
    (s : (J).Mode) {d K g : ℝ} (gp : 0 < g) (loss debt : ℕ)
    (radii : ∀ t : (J).Mode, g^loss ≤ Poly.toll w t) (log : Poly.price w r ≤ d)
    (small : d ≤ 1) (seen : ∀ t : (J).Mode,‖S.part t‖ ≤ K/g^debt) :
    ‖(S-Poly.pass (-r)*S).part s‖ ≤ (modes*(4*d/g^loss))*(modes*(K/g^debt)) := by
  let err := 1-Poly.pass (-r)
  let one : Fin 3 → ℝ := fun _ => 1
  have one0 : ∀ j,0 < one j := fun _ => zero_lt_one
  have a (t : (J).Mode) : ‖err.part t‖ ≤ 4*d/g^loss := by
    apply (le_div_iff₀ (pow_pos gp _)).mpr
    rw [mul_comm]
    exact ((mul_le_mul_of_nonneg_right (radii t) (norm_nonneg _)).trans
      (Poly.member hw t err)).trans (discount w hw r log small)
  have sum (x : Poly J) {c : ℝ} (h : ∀ t,‖x.part t‖ ≤ c) : Poly.price one x ≤ modes*c := calc
    _ ≤ ∑ _t : (J).Mode,c := Finset.sum_le_sum (fun t _ => by simpa [one,Poly.toll] using h t)
    _ = _ := by simp
  have hit := (Poly.member one0 s (err*S)).trans (Poly.multiplication one0 err S)
  have real : 0 ≤ modes*(4*d/g^loss) := (Poly.nonnegative one0 _).trans (sum err a)
  have sub : S-Poly.pass (-r)*S=err*S := by unfold err; rw [sub_mul,one_mul]
  rw [sub]; simpa only [one,Poly.toll,Finset.prod_const_one,one_mul] using
    hit.trans (mul_le_mul (sum err a) (sum S seen) (Poly.nonnegative one0 S) real)

variable {G : Gauge} (R : Run G) (A : Group R.family 6) (simple : G.Simple) {i m N per k : ℕ}
  (live : i < N) (o : Positions (Fin 3) (R.family.side N per))
  (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ) (ahead : Mentor.Forecast D R.rolls Q φ books)
  (order shelf seats : ℕ) (floor : m ≤ i)
local notation "ages" => (fun j : Fin 3 => (grade j).val)
variable (P : WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead disks sectors ages
    order shelf seats i floor (offered R A simple live o))
local notation "gs" => Coat.gStep (R.family.path.rep N per (i+1)).beta
local notation "Ω" => Oak.expenseReal R hk D Q π Γ books floor P.op P.lesson ahead order shelf
local notation "T" => table R A simple live.le o
local notation "r" W => P.output.old.log fired W
local notation "student" => Oak.student (n:=per) R hk D Q π Γ books floor P.op P.lesson ahead disks P.model order P.voter
local notation "gr" => Coat.gStep (Ψ (i+1)).beta
local notation "lights" => rendered student (Ψ i).p gr
local notation "common" => Tint.Patrol.report student P.output gr
local notation "ν" j => scene R.family.path N per j
private def planted (t : (J).Mode) (U : Config G (R.family.side N per)) : ℂ :=
  ∏ j ∈ t.val, R.family.O N per (A.station.wheel.atCut (N,per) (index A (grade j)) (vector A univ j)) (o.origin j) U

private theorem posted (W : Config G (R.family.side i per)) :
    (T) W = (((R.family.path.rep N per i).eval W : ℂ)⁻¹) • (common).density fired W := by
  have push := WilsonOriginalReceivedChain.report R hk D Q π Γ Ψ books ahead disks sectors ages order shelf seats i floor _ P fired
  have input := congrArg (LocalComparison.actualPush R.family N per i) (fired_input R A simple live o).symm
  have travel := (step R A simple live o).symm.trans (input.trans push)
  exact congrArg (fun t : Poly J => (((R.family.path.rep N per i).eval W : ℂ)⁻¹) • t) (congrFun travel W)

private theorem shed (x y z : Poly J) (c d : ℂ) (qr : y.part (J).quiet = 0)
    (total : Poly J) (quoted : Poly.pass total = Poly.pass x*Poly.pass y) :
    Poly.pass (-y)*(c • d • (Poly.pass total*z)) = c • d • (Poly.pass x*z) := by
  have pair : Poly.pass (-y)*(Poly.pass total*z) = Poly.pass x*z := calc
    _ = (Poly.pass (-y)*Poly.pass y)*(Poly.pass x*z) := by rw [quoted]; ac_rfl
    _ = _ := by rw [Next.Rank.Exponential.pass_neg _ qr,one_mul]
  rw [mul_smul_comm,mul_smul_comm,pair]

/-- The complete forced gas and its true Wilson normalizer remain after the
signed regular deletion, including at configurations with distant flags. -/
theorem same (W : Config G (R.family.side i per)) :
    Poly.pass (-(r W))*(T) W =
      (((R.family.path.rep N per i).eval W : ℂ)⁻¹) •
        (Real.exp ((Ψ i).exponent W) : ℂ) • (Poly.pass ((lights).log fired W)*(common).gas fired W) := by
  letI := P.modelCount
  have summ := (Scene.Armada.paid student P.w ages P.issued.earning (Ψ i).p P.issued.Waffle.soon).sums
    (by linarith only [(Ψ i).p.exponent_pos]) P.salary.positive fired W
  have old := P.issued.tuition.sums (by linarith only [(Ψ i).p.exponent_pos]) P.salary.positive fired W
  have both : Poly.pass ((common).E.log fired W) = Poly.pass ((lights).log fired W)*Poly.pass (r W) :=
    (congrArg Poly.pass (Lamps.joinLog fired W summ old)).trans (Next.Rank.Exponential.pass_add _ _
      (Lamps.quiet_of_hasSum fired W summ) (Lamps.quiet_of_hasSum fired W old))
  rw [posted R A simple live o hk D Q π Γ Ψ books ahead order shelf seats floor P W]
  exact shed ((lights).log fired W) (r W) ((common).gas fired W) _ _ (Lamps.quiet_of_hasSum fired W old) _ both

private theorem quoted (q : ℕ) (deep : 2*(q+1)+8 ≤ order) (aged : q+4 ≤ 3*k+2)
    {ε : ℝ} (ee : 0 < ε)
    (late : WilsonFirstReceivedEarnedFee.opening R simple seats q order k deep aged ee ≤ i)
    (W : Config G (R.family.side i per)) :
    Poly.price P.w (r W) ≤ modes*((8*Ω^seats)*P.rent+ε*(gs)^q) := by
  letI := P.modelCount
  have earned := WilsonReceivedInheritedFee.original R hk D Q π Γ Ψ books floor live P.op P.lesson ahead disks
    P.model P.w ages order shelf P.voter P.cost sectors P.input P.rent P.output P.issued simple
    q deep aged ee (by simpa only [P.capacity] using late)
  have funds := logCost P.output.old P.salary.positive P.issued.tuition
    (by linarith only [(Ψ i).p.exponent_pos]) fired W
  apply funds.trans
  exact mul_le_mul_of_nonneg_left (by simpa only [P.capacity] using earned) (Nat.cast_nonneg _)

/-- Return the entire regular change through every older true posterior in
reporting units. The native tuition is bought at the prescribed order. Its
genuine full-group cofactor uses the seven bounded microscopic faces. -/
theorem physical (ref : ∀ t : Fin 3, R.family.ref (grade t) ≤ N) (loss debt : ℕ)
    (deep : 2*((loss+debt+2)+1)+8 ≤ order) (aged : (loss+debt+2)+4 ≤ 3*k+2)
    {ε K : ℝ} (ee : 0 < ε) (kk : 0 ≤ K)
    (late : WilsonFirstReceivedEarnedFee.opening R simple seats (loss+debt+2) order k deep aged ee ≤ i)
    (radii : ∀ t : (J).Mode, (gs)^loss ≤ Poly.toll P.w t)
    (rent : (8*Ω^seats)*P.rent ≤ ε*(gs)^(loss+debt+2))
    (small : modes*(2*ε*(gs)^(loss+debt+2)) ≤ 1)
    (raw : ∀ (t : (J).Mode) U, ‖planted R A o t U‖ ≤ K/(gs)^debt)
    {u : ℕ} (old : u ≤ i) (s : (J).Mode) :
    let gm := Pert.Asymptotics.regulatorRun R.family N per m
    let f := fun W => (gm^7 : ℝ) • (((T) W-Poly.pass (-(r W))*(T) W).part s)
    (∀ U,‖actualTransport R.family (N:=N) f old U‖ ≤ 32*modes^3*K*ε*gm^9) ∧
      ‖∫ U,actualTransport R.family (N:=N) f old U ∂scene R.family.path N per u‖ ≤ 32*modes^3*K*ε*gm^9 := by
  intro gm f
  letI := P.modelCount
  let q := loss+debt+2
  have gp : 0 < gs := ActualRunKernelPackets.regulator_pos R N per (i+1) live
  have rp : 0 < gm := ActualRunKernelPackets.regulator_pos R N per m (floor.trans live.le)
  have band : (gs) ≤ 2*gm := WilsonLocalCompactRichPortUnits.compared R simple (floor.trans (Nat.le_succ i)) live per
  let d := modes*(2*ε*(gs)^q)
  have abs (W : Config G (R.family.side i per)) : ‖f W‖ ≤ 32*modes^3*K*ε*gm^9 := by
    have fees := quoted R A simple live o hk D Q π Γ Ψ books ahead order shelf seats floor P q deep aged ee late W
    have kept : Poly.price P.w (r W) ≤ d := fees.trans (mul_le_mul_of_nonneg_left (by
      change (8*Ω^seats)*P.rent+ε*(gs)^q ≤ 2*ε*(gs)^q
      linarith only [rent]) (Nat.cast_nonneg _))
    have field (t : (J).Mode) : ‖((T) W).part t‖ ≤ K/(gs)^debt := by
      rw [observed R A simple live.le o ref W t]
      exact actualTransport_norm_le R.family R.makes (le_refl N) (raw t) live.le W
    have charged := ordinary P.w P.salary.positive ((T) W) (r W) s gp loss debt radii kept small field
    have algebra : (modes*(4*d/(gs)^loss))*(modes*(K/(gs)^debt)) = 8*modes^3*K*ε*(gs)^2 := by
      dsimp only [d,q]; rw [pow_add,pow_add]; field_simp; ring
    rw [show ‖f W‖ = gm^7*‖((T) W-Poly.pass (-(r W))*(T) W).part s‖ from
      (norm_smul ..).trans (congrArg (·*_) (Real.norm_of_nonneg (pow_nonneg rp.le _)))]
    calc
      _ ≤ gm^7*(8*modes^3*K*ε*(gs)^2) := mul_le_mul_of_nonneg_left (charged.trans_eq algebra) (pow_nonneg rp.le _)
      _ ≤ gm^7*(8*modes^3*K*ε*(2*gm)^2) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ gp.le band _) (by positivity)) (pow_nonneg rp.le _)
      _ = _ := by ring
  have every := actualTransport_norm_le R.family R.makes live.le abs old
  letI : IsProbabilityMeasure (scene R.family.path N per u) := probability R.makes.wilson (old.trans live.le)
  refine ⟨every,?_⟩
  simpa using norm_integral_le_of_norm_le_const (μ:=scene R.family.path N per u) (ae_of_all _ every)

end YM.Integration.WilsonThermometerRegularCofactors
end
