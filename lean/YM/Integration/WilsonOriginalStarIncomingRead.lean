import YM.Integration.WilsonOriginalStarIncoming

/-! The tested cost on the actual occupied intake with independently rendered primary rows. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalStarIncomingRead
open Function Finset Filter Lattice Wilson RG Source Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Tint
open QuadraticLocal.Fusion.Attached MergeProof.Accent WilsonOriginalStarIncoming
open WilsonOriginalDepositedRegular WilsonOriginalDepositedRegularWindow WilsonOriginalDepositedRegularHearing
open scoped Topology Classical BigOperators
variable {G : Gauge} {n : Side} {d : ℕ} {F : Labels.Frame G d} {A : Hol G}
  {P : Rep G n} {V T I S₀ S₁ : Type} [DecidableEq V] {J : Census V} {o : V → Site n}
  (old : Incoming (Passport.point o) P T I J)
  (j : V) (q : Coefficient F n) (law : q.Format (o j) A P) (t : T → ℂ) (D : ℕ)

def primary (C : SectionData F) (U : Config G n) : ℂ :=
  q.x 0 + masked P.p.threshold (C.footprint (o j)) (C.places (F.scaled P.p.threshold⁻¹ (F.core q.x)) (o j)) U

def exhibit (M : Lamps T S₀ G P.p o J) : Gallery T (S₀⊕I) o P J :=
  ⟨M.join old.old,old.hard⟩

variable [Fintype V] (M₀ : Lamps T S₀ G P.p o J) (M₁ : Lamps T S₁ G P.p o J) (C : SectionData F)
   (w : V → ℝ) (hw : ∀ v, 0<w v) (test : ∀x, ‖t x‖≤1) {κ B k h a₀ a₁ : ℝ}
   (fund : q.remBound (o j) P κ B) (wide : 1 ≤ P.p.supportExponent)
local notation "α_" => P.p.supportExponent+1+1

include fund wide hw test in
theorem omitted (x : T) (U : Config G n) :
    ((lamps (J:=J) j q law t (fun i=> ¬small P q D i)).log x U).part (J.fire j) = t x * tail P q D U := by
  have s := (long (J:=J) j q law t D w hw test fund wide).sums (le_refl 0) hw x U
  rw [Lamps.log,Poly.share s,tail,←tsum_mul_left]
  apply tsum_congr
  intro i
  rw [row]
  by_cases hi : small P q D i <;> simp [rejected,hi]

include fund wide hw test in
theorem original (pr₀ : M₀.Paid w P.p.B (α_) a₀) (pr₁ : M₁.Paid w P.p.B (α_) a₁)
    (reg : old.old.Paid w P.p.B (α_) k) (hard : old.hard.Paid w P.p.B P.p.supportExponent h)
    (x : T) (U : Config G n) :
    ((exhibit (enter old j q law t D) M₁).density x U).part (J.fire j) -
      ((exhibit old M₀).density x U).part (J.fire j) - t x * q.density (o j) C P U =
      (P.eval U:ℂ) * (((M₁.log x U).part (J.fire j) - (M₀.log x U).part (J.fire j)) -
        t x*primary (P:=P) (o:=o) j q C U - t x*tail P q D U) := by
  let inc := enter old j q law t D
  let before := exhibit old M₀
  let after := exhibit inc M₁
  let short₀ := lamps (J:=J) j q law t (small P q D)
  have α : 0 ≤ (α_) := by linarith
  have shortPrice := short (J:=J) j q law t D w hw test fund
  have shortSum := shortPrice.sums (by linarith) hw x U
  obtain ⟨ri,ki⟩ := funded old j q law t D w hw test fund reg hard
  have oldPrice := Lamps.joinPaid pr₀ reg
  have newPrice := Lamps.joinPaid pr₁ ri
  have oldQuiet : (before.E.log x U).part J.quiet=0 :=
    Lamps.quiet_of_hasSum x U (oldPrice.sums α hw x U)
  have newQuiet : (after.E.log x U).part J.quiet=0 :=
    Lamps.quiet_of_hasSum x U (newPrice.sums α hw x U)
  have oldGas : (before.gas x U).part J.quiet=(P.activities.gas P.p U:ℂ) :=
    Hard.packet_of_quiet old.hard x U (Hard.packet_summing _ hard P.p.exponent_pos.le hw x U)
  have newGas : (after.gas x U).part J.quiet=(P.activities.gas P.p U:ℂ) :=
    Hard.packet_of_quiet inc.hard x U (Hard.packet_summing _ ki P.p.exponent_pos.le hw x U)
  have hardRow : (after.gas x U).part (J.fire j) - (before.gas x U).part (J.fire j) =
      t x*∑'i,q.marked P i U := WilsonOriginalDepositedHardTable.full old.hard j q law t w hw hard test fund x U
  have span := whole (J:=J) j q law t D w hw test fund wide x U
  rw [omitted j q law t D w hw test fund wide x U] at span
  have om : before.E.log x U=M₀.log x U+old.old.log x U :=
    Lamps.joinLog x U (pr₀.sums α hw x U) (reg.sums α hw x U)
  have nm : after.E.log x U=M₁.log x U+(old.old.log x U+short₀.log x U) := by
    change (M₁.join inc.old).log x U=_
    rw [Lamps.joinLog x U (pr₁.sums α hw x U) (ri.sums α hw x U)]
    exact congrArg (M₁.log x U+·) (Lamps.joinLog x U (reg.sums α hw x U) shortSum)
  change (after.density x U).part _ - (before.density x U).part _ - _ = _
  rw [Gallery.density,Gallery.density,Poly.part_smul,Poly.part_smul,shock,shock,oldGas,newGas,
    Poly.pass_part _ newQuiet,Poly.pass_part _ oldQuiet,whisper J _ newQuiet,whisper J _ oldQuiet,
    om,nm]
  simp only [Poly.part_plus,Coefficient.density,Coefficient.exponentialEntry,primary,
    Rep.eval,Complex.ofReal_mul]
  change (short₀.log x U).part (J.fire j)+t x*tail P q D U=t x*∑'i,q.maskedTerm P i U at span
  linear_combination (Real.exp (P.exponent U):ℂ)*hardRow +
    (Real.exp (P.exponent U):ℂ)*(P.activities.gas P.p U:ℂ)*span

end YM.Integration.WilsonOriginalStarIncomingRead
