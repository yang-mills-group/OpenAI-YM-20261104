import YM.Integration.WilsonCenteredFiledAtoms
import YM.Integration.WilsonCenteredCrossedGas
import YM.Integration.WilsonCenteredFiledGallery

/-! One positive-horizon capture on the original rep, between the actual
returned gallery and its signed reference with common compulsory inventory.
The mixed numerator retains both independently placed singleton products. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCenteredSignedCapture
open Finset Function Lattice RG Wilson Marker Ac QuadraticLocal Source Labels Push.Local
open Planned.GuardedAtom Extra.Trajectories WilsonCenteredFiledAtoms Comparison.RG02.Cumulants
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} {V X ι μ : Type} [DecidableEq V] [Fintype V]
    {P : Rep G n} {o : V→Site n} {R : Census V} {d : ℕ} {F : Frame G d}

private theorem blank (y : Site n) : ForceFormat P.p P.activities y 0 :=
  ⟨by simp,by simp,fun _ _ _=>rfl,fun _ _ _ _ _=>rfl,fun _=>measurable_const⟩

omit [Fintype V] in
theorem compulsory (D : Lamps X μ G P.p o R) (A : Gallery X ι o P R)
    (w : V→ℝ) (hw : ∀ i,0<w i) {δ κ v : ℝ}
    (debt : D.Paid w P.p.B (P.p.supportExponent+2) δ) (wage : A.K.Paid w P.p.B (P.p.supportExponent+2) κ)
    (quiet : P.activities.KBound P.p v) (hv : 0≤v) (room : hitWidth P.p*v≤1)
    (a b : V) (Z : Support n) (za : o a∈Z) (zb : o b∈Z) (hk : 0<κ)
    (K : Guard.Keeper P.p P.activities) (serial : (μ×ℕ)×Finset ℕ ↪ ℕ) (x : X) :
    let bill := 2*Real.exp ((P.p.supportExponent+2)*coverNumber P.p.B Z)*δ
    ForceCost P.p P.activities (WilsonCenteredCapturedHardFace.row D A a b Z K serial x)
      (κ*((w a*w b)⁻¹*(bill+hitWidth P.p*v*bill))) := by
  intro bill
  obtain ⟨e,cash,caps⟩:=WilsonCenteredCapturedHardPrice.original D A w hw debt wage quiet hv room a b Z za zb hk K serial
  let t := κ*(w a*w b)⁻¹
  have ht : 0≤t:=mul_nonneg hk.le (inv_pos.mpr (mul_pos (hw a) (hw b))).le
  refine ⟨fun j=>t*e j,?_,fun j=>⟨mul_nonneg ht (caps j).1,fun U=>?_⟩⟩
  · have priced:=sumBudget_mul_left cash ht
    convert priced using 1
    · ext j;unfold BudgetPoint.mass;ring
    · dsimp [t,bill];ring
  calc
    _ = t*(κ⁻¹*(w a*w b)*‖WilsonCenteredCapturedHardFace.row D A a b Z K serial x j U‖) := by
      dsimp [t];field_simp [ne_of_gt hk,ne_of_gt (hw a),ne_of_gt (hw b)]
    _ ≤ _ := mul_le_mul_of_nonneg_left ((caps j).2 x U) ht

theorem original [Countable ι] [Countable μ] (L : Lamps X ι G P.p o R) (D : Lamps X μ G P.p o R)
    (H : Hard X P.p P.activities.forced P.activities.K o R)
    (w : V→ℝ) (hw : ∀ i,0<w i) {M δ κ : ℝ}
    (model : L.Paid w P.p.B (P.p.supportExponent+2) M) (debt : D.Paid w P.p.B (P.p.supportExponent+2) δ)
    (hard : H.Paid w P.p.B (P.p.supportExponent+2) κ)
    (a b c : V) (s : R.Mode) (apart : a≠b) (pair : s.val={a,b}) (x : X)
    (y : Site n) (Z : Support n) (root : y∈Z) (za : o a∈Z) (zb : o b∈Z) (zc : o c∈Z)
    (rad : ℕ) (na : separation (o a) y≤rad) (nb : separation (o b) y≤rad) (nc : separation (o c) y≤rad)
    (K : Guard.Keeper P.p P.activities) {σ ζ Λ r η u : ℝ} (law : P.Lawful σ ζ Λ r η)
    (hk : 0<κ) (hη : 0≤η) (room : hitWidth P.p*η≤1)
    (S : SectionData F) (Y : Hol G) (read : Readable Y S P.p n u) :
    let A : Gallery X (ι⊕μ) o P R := ⟨L.join D,H⟩
    let B : Gallery X ι o P R := ⟨L,H⟩
    let Zfee := Real.exp ((P.p.supportExponent+2)*coverNumber P.p.B Z)
    let t₁ := WilsonCenteredLampCapture.stage P.p rad ({()}:Finset Unit)
    let t₂ := WilsonCenteredLampCapture.stage P.p rad ({false,true}:Finset Bool)
    let bill := 2*Zfee*δ
    let fee := cartage P.p Y S u η κ
    let mixed := fee (t₁*(Zfee*((Poly.toll w s)⁻¹*δ))) ((w a*w b)⁻¹*(bill+hitWidth P.p*η*bill))
    let centre := fee (t₁*(Zfee*((Poly.toll w (R.fire c))⁻¹*δ))) 0
    let oldFresh := fee (t₂*(Zfee*(((w a)⁻¹*δ)*((w b)⁻¹*(M+δ))))) 0
    let freshOld := fee (t₂*(Zfee*(((w a)⁻¹*M)*((w b)⁻¹*δ)))) 0
    Store P S Y y κ (((mixed+centre)+oldFresh)+freshOld) (fun U=>
      ((A.density x U).part s-(A.density x U).part (R.fire c))-
      ((B.density x U).part s-(B.density x U).part (R.fire c))) := by
  intro A B Zfee t₁ t₂ bill fee mixed centre oldFresh freshOld
  let serial := WilsonCenteredLampCapture.docket ((μ×ℕ)×Finset ℕ)
  let row := WilsonCenteredCapturedHardFace.row D B a b Z K serial x
  have wage : B.K.Paid w P.p.B (P.p.supportExponent+2) κ := hard
  have pq := law.labels.boundK
  have valid := WilsonCenteredCapturedHardFace.formed D B a b Z K serial x y root law.labels.forced
  have force := compulsory D B w hw debt wage pq hη room a b Z za zb hk K serial x
  have source := single D x s a (by rw [pair];simp) w hw debt y Z root za rad na 1 K law hk room hη S Y read row valid force
  have no : ForceCost P.p P.activities (0 : ℕ→ Config G n→ℂ) (κ*0) := by
    rw [mul_zero];exact ⟨fun _=>0,Extra.Histories.budget0 _ _,by simp⟩
  have alternative := single D x (R.fire c) c (mem_singleton_self _) w hw debt y Z root zc rad nc 1 K law hk room hη S Y read 0 (blank _) no
  have left := couple D (L.join D) x a b w hw debt (Lamps.joinPaid model debt) y Z root za zb rad na nb 1 K law hk room hη S Y read 0 (blank _) no
  have right := couple L D x a b w hw model debt y Z root za zb rad na nb 1 K law hk room hη S Y read 0 (blank _) no
  have assembled := add law hk (add law hk (sub law source alternative) left) right
  have width : 0≤P.p.supportExponent+2 := by have:=P.p.exponent_pos;linarith
  have equalsAt U := WilsonCenteredFiledGallery.original L D H w hw width model debt a b c s apart pair x U
  have crossed U := WilsonCenteredCrossedGas.original D B w hw debt wage pq hη room a b Z za zb hk K serial x U
  obtain ⟨Q,legal,paid,atU⟩:=assembled
  refine ⟨Q,legal,?_,fun U=>?_⟩
  · simpa only [norm_one,one_mul] using paid
  rw [atU]
  apply Eq.trans ?_ (equalsAt U).symm
  simp only [Pi.add_apply,Pi.sub_apply,map_zero,tsum_zero,mul_zero,add_zero,one_mul]
  have ls := model.sums width hw x U
  have ds := debt.sums width hw x U
  have zT := Lamps.quiet_of_hasSum x U ls
  have zE := Lamps.quiet_of_hasSum x U ds
  have sumQuiet : (L.log x U+D.log x U).part R.quiet=0 := by rw [Poly.part_plus,zT,zE,add_zero]
  have H0 := Hard.packet_of_quiet H x U (Hard.packet_summing _ hard width hw x U)
  have singleton (j : V) (T : Poly R) (zero : T.part R.quiet=0) :
      (Poly.pass T).part (R.fire j)=T.part (R.fire j) := by
    rw [←lamp j _ (Poly.pass_part T zero),connected_pass zero]
  rw [Lamps.joinLog x U ls ds,singleton b _ sumQuiet,singleton a _ zT]
  change _ = _*((B.gas x U).part R.quiet * _ + _ + _)
  rw [show (B.gas x U).part R.quiet=(P.activities.gas P.p U:ℂ) from H0]
  rw [show (∑' C,gasMark P.p P.activities U C row)=_ from crossed U]
  simp only [Rep.eval,Complex.ofReal_mul]
  ring

end YM.Integration.WilsonCenteredSignedCapture
