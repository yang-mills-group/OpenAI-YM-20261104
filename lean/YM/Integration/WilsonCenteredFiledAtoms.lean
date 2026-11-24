import YM.Integration.WilsonCenteredLampCapture
import YM.Push.RELAY_DIFFERENCE.Subtraction

/-! Physical re-expression of one complete filed mode, or two complete
independently seated singleton modes. The source sum is taken before the
native coefficient is tested. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCenteredFiledAtoms
open Finset Function RG Lattice Wilson Source Labels QuadraticLocal Ac Marker Push.Local
open Planned.GuardedAtom Extra.Histories WilsonCenteredCaptureLampRoster WilsonCenteredLampCapture
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} {V X ι μ : Type} [DecidableEq V]
    {P : Rep G n} {o : V→Site n} {R : Census V} {d : ℕ} {F : Frame G d}

def cartage (p : BudgetPoint) (Y : Hol G) (S : SectionData F) (w v κ a b : ℝ) :=
  let D := factor Y S p.supportExponent w
  D*a + ((b+(hitWidth p*v/κ)*a)+(hitWidth p*v/κ)*(D*a))

def Store (P : Rep G n) (S : SectionData F) (Y : Hol G) (y : Site n) (κ b : ℝ)
    (φ : Config G n→ℂ) : Prop :=
  ∃ Q : Coefficient F n,Q.Format y Y P ∧ Q.remBound y P κ b ∧ ∀ U,Q.density y S P U=φ U

theorem sub {S : SectionData F} {Y : Hol G} {y : Site n} {κ a b σ C Λ δ v : ℝ}
    (law : P.Lawful σ C Λ δ v) {φ ψ : Config G n→ℂ}
    (first : Store P S Y y κ a φ) (second : Store P S Y y κ b ψ) :
    Store P S Y y κ (a+b) (φ-ψ) := by
  obtain ⟨Q,fit,paid,actual⟩:=first
  obtain ⟨B,registered,fee,old⟩:=second
  exact ⟨Push.RelayDifference.combine Q B,Push.RelayDifference.combo_format fit registered,
    Push.RelayDifference.combo_cap fit registered paid fee,fun U=>
      (congrFun (Push.RelayDifference.combo_density fit registered paid fee law S) U).trans
        (congrArg₂ Sub.sub (actual U) (old U))⟩

theorem empty (S : SectionData F) (Y : Hol G) (y : Site n) {κ : ℝ} (hk : 0<κ) :
    Store P S Y y κ 0 0 := by
  refine ⟨Extra.Histories.primary y 0,Extra.Histories.primary_format 0,
    Extra.Histories.primary_rem 0 hk,fun U=>?_⟩
  simp [Extra.Histories.primary_density]

theorem add {S : SectionData F} {Y : Hol G} {y : Site n} {κ a b σ C Λ δ v : ℝ}
    (law : P.Lawful σ C Λ δ v) (hk : 0<κ) {φ ψ : Config G n→ℂ}
    (first : Store P S Y y κ a φ) (second : Store P S Y y κ b ψ) :
    Store P S Y y κ (a+b) (φ+ψ) := by
  have subtract := sub law first (sub law (empty S Y y hk) second)
  simpa only [zero_add,zero_sub,sub_neg_eq_add] using subtract

theorem single [Countable ι] (L : Lamps X ι G P.p o R) (x : X) (s : R.Mode)
    (v : V) (member : v∈s.val) (w : V→ℝ) (prices : ∀ i,0<w i)
    {E : ℝ} (wage : L.Paid w P.p.B (P.p.supportExponent+2) E)
    (y : Site n) (Z : Support n) (root : y∈Z) (seat : o v∈Z) (rad : ℕ)
    (near : separation (o v) y≤rad) (g : ℂ)
    (K : Guard.Keeper P.p P.activities) {σ C Λ δ η κ μ b : ℝ}
    (law : P.Lawful σ C Λ δ η) (div : 0<κ) (room : hitWidth P.p*η≤1) (hη : 0≤η)
    (S : SectionData F) (Y : Hol G) (read : Readable Y S P.p n μ)
    (hard : ℕ→ Config G n→ℂ) (format : ForceFormat P.p P.activities y hard)
    (force : ForceCost P.p P.activities hard (κ*b)) :
    let α := P.p.supportExponent+2
    let a := (‖g‖*stage P.p rad ({()}:Finset Unit))*(Real.exp (α*coverNumber P.p.B Z)*((Poly.toll w s)⁻¹*E))
    Store P S Y y κ (cartage P.p Y S μ η κ a b) (fun U=>
      (P.eval U:ℂ)*(g*(L.log x U).part s)+(Real.exp (P.exponent U):ℂ)*∑' B,gasMark P.p P.activities U B hard) := by
  intro α a
  have width : 0≤α := by have := P.p.exponent_pos;dsimp [α];linarith
  obtain ⟨e,-,caps,quote⟩:=WilsonCenteredCaptureLampRoster.single L s v member w prices width wage Z seat
  let each (_ : Row L s) := ({()}:Finset Unit)
  let sites (i : Row L s) (_ : Unit) := i.val
  let seats (_ : Row L s) (_ : Unit) := o v
  have cash : SumBudget (fun i=>reservedMass P.p (WilsonCenteredCaptureRegularAtoms.domain L (each i) (sites i) Z)
      (‖g‖*(stage P.p rad (each i)*∏ j∈each i,e i))) a := by
    have H := sumBudget_mul_left quote (mul_nonneg (norm_nonneg g) (zero_le_one.trans (funded P.p rad ({()}:Finset Unit))))
    convert H using 1
    ext i
    simp [each,sites,WilsonCenteredCaptureRegularAtoms.domain,reservedMass,α]
    ring
  obtain ⟨Q,fit,tab,val⟩:=counted L x y Z root each sites seats rad (fun _ _ _=>near)
    (fun _=>g) (fun i _=>e i) (fun i _ _=>caps i x) cash K law div hη room S Y read 0 hard format force
  refine ⟨Q,fit,tab.bound le_rfl,fun U=>?_⟩
  have term := WilsonCenteredCaptureLampRoster.published L s x U (wage.sums width prices x U)
  rw [val]
  simp only [map_zero,Pi.zero_apply,zero_add,each,sites,prod_singleton]
  rw [(term.mul_left g).tsum_eq]

/-- The two singleton positions need only be in the common physical halo.
They retain separate original lamp indices and can carry independent tests. -/
theorem couple [Countable ι] [Countable μ] (L : Lamps X ι G P.p o R)
    (D : Lamps X μ G P.p o R) (x : X) (a b : V) (w : V→ℝ) (prices : ∀ i,0<w i)
    {E H : ℝ} (first : L.Paid w P.p.B (P.p.supportExponent+2) E)
    (second : D.Paid w P.p.B (P.p.supportExponent+2) H)
    (y : Site n) (Z : Support n) (root : y∈Z) (za : o a∈Z) (zb : o b∈Z) (rad : ℕ)
    (na : separation (o a) y≤rad) (nb : separation (o b) y≤rad) (g : ℂ)
    (K : Guard.Keeper P.p P.activities) {σ C Λ δ η κ u h : ℝ}
    (law : P.Lawful σ C Λ δ η) (div : 0<κ) (room : hitWidth P.p*η≤1) (hη : 0≤η)
    (S : SectionData F) (Y : Hol G) (read : Readable Y S P.p n u)
    (hard : ℕ→ Config G n→ℂ) (format : ForceFormat P.p P.activities y hard)
    (force : ForceCost P.p P.activities hard (κ*h)) :
    let α := P.p.supportExponent+2
    let A := (‖g‖*stage P.p rad ({false,true}:Finset Bool))*
      (Real.exp (α*coverNumber P.p.B Z)*(((w a)⁻¹*E)*((w b)⁻¹*H)))
    Store P S Y y κ (cartage P.p Y S u η κ A h) (fun U=>
      (P.eval U:ℂ)*(g*((L.log x U).part (R.fire a)*(D.log x U).part (R.fire b)))+
        (Real.exp (P.exponent U):ℂ)*∑' B,gasMark P.p P.activities U B hard) := by
  intro α A
  have width : 0≤α := by have := P.p.exponent_pos;dsimp [α];linarith
  obtain ⟨e,k,-,-,ca,cb,quote⟩:=WilsonCenteredCaptureLampRoster.pair L D a b w prices width first second Z za zb
  let RowPair := Row L (R.fire a) × Row D (R.fire b)
  let each (_ : RowPair) := ({false,true}:Finset Bool)
  let sites (i : RowPair) : Bool→ι⊕μ := fun b=>if b then Sum.inr i.2.val else Sum.inl i.1.val
  let seats (_ : RowPair) : Bool→Site n := fun t=>if t then o b else o a
  let toll (i : RowPair) := Sum.elim (fun _ : ι=>e i.1) (fun _ : μ=>k i.2)
  have close (i : RowPair) (t : Bool) (_ : t∈each i) : separation (seats i t) y≤rad := by
    cases t;exact na;exact nb
  have cap (i : RowPair) (t : Bool) (_ : t∈each i) :
      P.p.supBounds (seats i t) ((L.join D).ground (sites i t)) ((L.join D).nominal x (sites i t)) (toll i (sites i t)) := by
    cases t;exact ca i.1 x;exact cb i.2 x
  have cash : SumBudget (fun i=>reservedMass P.p (WilsonCenteredCaptureRegularAtoms.domain (L.join D) (each i) (sites i) Z)
      (‖g‖*(stage P.p rad (each i)*∏ j∈each i,toll i (sites i j)))) A := by
    have both := sumBudget_mul_left quote (mul_nonneg (norm_nonneg g) (zero_le_one.trans (funded P.p rad ({false,true}:Finset Bool))))
    convert both using 1
    ext i
    simp [each,sites,WilsonCenteredCaptureRegularAtoms.domain,reservedMass,α,Lamps.ground,Lamps.join,toll,Finset.union_assoc]
    ring
  obtain ⟨Q,fit,tab,val⟩:=counted (L.join D) x y Z root each sites seats rad close
    (fun _=>g) toll cap cash K law div hη room S Y read 0 hard format force
  refine ⟨Q,fit,tab.bound le_rfl,fun U=>?_⟩
  have fa:=WilsonCenteredCaptureLampRoster.published L (R.fire a) x U (first.sums width prices x U)
  have fb:=WilsonCenteredCaptureLampRoster.published D (R.fire b) x U (second.sums width prices x U)
  have same (i : RowPair) :
      (∏ j∈each i,(L.join D).light x (sites i j) U)=L.light x i.1.val U*D.light x i.2.val U := by
    simp [each,sites,Lamps.light,Lamps.ground,Lamps.join]
  rw [val]
  simp only [map_zero,Pi.zero_apply,zero_add,same,←fa.tsum_eq,←fb.tsum_eq,
    tsum_mul_tsum_of_summable_norm fa.summable.norm fb.summable.norm,tsum_mul_left]
  rfl

end YM.Integration.WilsonCenteredFiledAtoms
