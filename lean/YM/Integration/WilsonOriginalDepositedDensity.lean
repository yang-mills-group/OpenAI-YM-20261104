import YM.Integration.WilsonOriginalDepositedHardTable

/-! The original transported singleton in a previously marked gallery on its own vacuum. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalDepositedDensity
open Filter Function Finset Lattice Wilson RG Source Marker QuadraticLocal QuadraticLocal.Fusion.Attached
open MergeProof.Accent WilsonOriginalDepositedHard WilsonOriginalDepositedHardTable
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} {d : ℕ} {F : Labels.Frame G d} {A : Hol G}
  {P : Rep G n} {V T I : Type} [DecidableEq V] [Fintype V] {J : Census V} {o : V → Site n}
  (old : Gallery T I o P J) (j : V) (q : Coefficient F n) (law : q.Format (o j) A P)
  (C : SectionData F) (t : T → ℂ)

def density (x : T) (U : Config G n) : Poly J :=
  (Real.exp (P.exponent U) : ℂ) • (Poly.pass (old.E.log x U +
    Poly.send (J.fire j) (t x*q.exponentialEntry (o j) C P U)) *
     ∑' i, packet P.activities P.p ((joined old.K j q law t).hard x) U i)

theorem original (w : V → ℝ) (hw : ∀ v, 0 < w v) {e κ B E H : ℝ} (he : 0 ≤ e)
    (regular : old.E.Paid w P.p.B e E) (hard : old.K.Paid w P.p.B P.p.supportExponent H)
    (test : ∀ x, ‖t x‖ ≤ 1) (actual : q.remBound (o j) P κ B) (x : T) (U : Config G n) :
    (density old j q law C t x U).part (J.fire j) - (old.density x U).part (J.fire j) =
        t x * q.density (o j) C P U := by
  let L := old.E.log x U
  let L' := L+Poly.send (J.fire j) (t x*q.exponentialEntry (o j) C P U)
  let K := old.gas x U
  let K' := ∑' i, packet P.activities P.p ((joined old.K j q law t).hard x) U i
  let s : ℂ := Real.exp (P.exponent U)
  have hL : L.part J.quiet=0 := Lamps.quiet_of_hasSum x U (regular.sums he hw x U)
  have hL' : L'.part J.quiet=0 := by
    simp only [L',Poly.part_plus,hL,Poly.part_send,if_neg (J.fire_hot j).symm,add_zero]
  have hE : L'.part (J.fire j)=L.part (J.fire j)+t x*q.exponentialEntry (o j) C P U := by
    simp [L',Poly.part_plus]
  have hK : K.part J.quiet=(P.activities.gas P.p U : ℂ) :=
    Hard.packet_of_quiet old.K x U (Hard.packet_summing _ hard P.p.exponent_pos.le hw x U)
  have hK' : K'.part J.quiet=(P.activities.gas P.p U : ℂ) := Hard.packet_of_quiet _ x U
    (Hard.packet_summing _ (paid old.K j q law t w hw hard test actual) P.p.exponent_pos.le hw x U)
  have changed : K'.part (J.fire j) - K.part (J.fire j) = t x*∑' i,q.marked P i U :=
    full old.K j q law t w hw hard test actual x U
  change (s • (Poly.pass L'*K')).part (J.fire j) - (s • (Poly.pass L*K)).part (J.fire j) = _
  rw [Poly.part_smul,Poly.part_smul,shock,shock,Poly.pass_part _ hL,Poly.pass_part _ hL',
    whisper J _ hL,whisper J _ hL',hK,hK',hE]
  unfold Coefficient.density Rep.eval
  rw [Complex.ofReal_mul]
  dsimp only [s]
  linear_combination (Real.exp (P.exponent U):ℂ)*changed

end YM.Integration.WilsonOriginalDepositedDensity
