import YM.Integration.ActualPolynomialContraction
import YM.Integration.ActualWilsonAbsoluteTransport

/-! Weighted all-mode L¹ contraction along an arbitrary finite part of one
genuine physical history, for complete signed input densities. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.OriginalMarkedPriceTransport
open Function Set Finset MeasureTheory Lattice Wilson RG Marker OPE.Therm
open scoped Classical BigOperators

variable {G : Gauge} {V : Type} [DecidableEq V] {Γ : Census V}
    (C : Family G) (hC : C.Makes) {N p : ℕ} {w : V→ℝ} (hw : ∀i,0<w i)

include hC in
theorem weighted {j : ℕ} (hj : j ≤ N) {F : Config G (C.side j p)→Poly Γ}
    (hF : Integrable (fun T=>(C.path.rep N p j).eval T • F T) (prior G _)) :
    Integrable (fun T=>(C.path.rep N p j).eval T • Poly.price w (F T)) (prior G _) := by
  apply (ActualPolynomialContraction.price_integrable w hF).congr (ae_of_all _ fun T=>?_)
  exact ActualPolynomialContraction.price_real_smul w (F T)
    (Multi.AxisShift.chosen_positive hC.wilson hj T).le

include hC hw in
theorem dominated {j m : ℕ} (hj : j ≤ N) {F : Config G (C.side j p)→Poly Γ}
    (hF : Integrable (fun T=>(C.path.rep N p j).eval T • F T) (prior G _))
    (hm : m ≤ j) (U : Config G (C.side m p)) :
    Poly.price w (actualTransport C (N:=N) F hm U) ≤
      actualTransport C (N:=N) (fun T=>Poly.price w (F T)) hm U := by
  have hr := weighted C hC (w:=w) hj hF
  induction hm using Nat.decreasingInduction with
  | self => simp only [actualTransport_base C hC hj,le_rfl]
  | of_succ l hl ih =>
    rw [actualTransport_step C hC hj F hl,actualTransport_step C hC hj (fun T=>Poly.price w (F T)) hl]
    have h0 := ActualWilsonAbsoluteTransport.slice C
      (actualTransport_weighted_integrable_of_integrable C hC hj hF hl) U
    have h1 := ActualWilsonAbsoluteTransport.slice C
      (actualTransport_weighted_integrable_of_integrable C hC hj hr hl) U
    apply (ActualPolynomialContraction.price_integral_le hw h0).trans
    apply integral_mono (ActualPolynomialContraction.price_integrable w h0) h1
    intro T
    have hn := actualConditionalDensity_nonneg C hC (hl.trans_le hj) U T
    exact (ActualPolynomialContraction.price_real_smul w (actualTransport C (N:=N) F hl T) hn).le.trans
      (mul_le_mul_of_nonneg_left (ih T) hn)

include hC hw in
theorem first {j m : ℕ} (hj : j ≤ N) {F : Config G (C.side j p)→Poly Γ}
    (hF : Integrable (fun T=>(C.path.rep N p j).eval T • F T) (prior G _)) (hm : m ≤ j) :
    ∫ U,Poly.price w (actualTransport C (N:=N) F hm U) ∂scene C.path N p m ≤
      ∫ T,Poly.price w (F T) ∂scene C.path N p j := by
  have hr := weighted C hC (w:=w) hj hF
  have h := actualTransport_weighted_integrable_of_integrable C hC hj hF hm
  have h' := actualTransport_weighted_integrable_of_integrable C hC hj hr hm
  apply (integral_mono (ActualPolynomialContraction.price_integrable w
    (actualScene_integrable_of_weighted C hC (hm.trans hj) h))
    (actualScene_integrable_of_weighted C hC (hm.trans hj) h') (dominated C hC hw hj hF hm)).trans
  exact (actualScene_transport C hC hj hr hm).le

include hC in
theorem mode {j m : ℕ} (hj : j ≤ N) {F : Config G (C.side j p)→Poly Γ}
    (hF : Integrable (fun T=>(C.path.rep N p j).eval T • F T) (prior G _))
    (hm : m ≤ j) (s : Γ.Mode) (U : Config G (C.side m p)) :
    (actualTransport C (N:=N) F hm U).part s =
      actualTransport C (N:=N) (fun T=>(F T).part s) hm U := by
  let read := (Poly.get s).restrictScalars ℝ
  induction hm using Nat.decreasingInduction with
  | self => simp only [actualTransport_base C hC hj]
  | of_succ l hl ih =>
    rw [actualTransport_step C hC hj F hl,actualTransport_step C hC hj (fun T=>(F T).part s) hl]
    have h := ActualWilsonAbsoluteTransport.slice C
      (actualTransport_weighted_integrable_of_integrable C hC hj hF hl) U
    change read (actualAverage C (N:=N) (actualTransport C (N:=N) F hl) U)=_
    unfold actualAverage
    rw [←read.integral_comp_comm h]
    apply integral_congr_ae
    exact ae_of_all _ fun T=> (read.map_smul _ _).trans
      (congrArg (fun t : ℂ=>actualConditionalDensity C N p l U T • t) (ih T))

include hC in
theorem quiet {j m : ℕ} (hj : j ≤ N) {F : Config G (C.side j p)→Poly Γ}
    (hF : Integrable (fun T=>(C.path.rep N p j).eval T • F T) (prior G _))
    (neutral : ∀T,(F T).part Γ.quiet=1) (hm : m ≤ j) (U : Config G (C.side m p)) :
    (actualTransport C (N:=N) F hm U).part Γ.quiet=1 := by
  rw [mode C hC hj hF hm Γ.quiet U]
  simpa only [neutral] using actualTransport_const C hC hj (1 : ℂ) hm U

include hC in
theorem subtract {j m : ℕ} (hj : j ≤ N) {F Q : Config G (C.side j p)→Poly Γ}
    (hF : Integrable (fun T=>(C.path.rep N p j).eval T • F T) (prior G _))
    (hQ : Integrable (fun T=>(C.path.rep N p j).eval T • Q T) (prior G _)) (hm : m ≤ j) :
    actualTransport C (N:=N) (fun T=>F T-Q T) hm =
      fun U=>actualTransport C (N:=N) F hm U-actualTransport C (N:=N) Q hm U := by
  induction hm using Nat.decreasingInduction with
  | self => simp only [actualTransport_base C hC hj]
  | of_succ l hl ih =>
    funext U
    simp only [actualTransport_step C hC hj _ hl,ih]
    unfold actualAverage
    simp_rw [smul_sub]
    exact integral_sub (ActualWilsonAbsoluteTransport.slice C
      (actualTransport_weighted_integrable_of_integrable C hC hj hF hl) U)
      (ActualWilsonAbsoluteTransport.slice C
        (actualTransport_weighted_integrable_of_integrable C hC hj hQ hl) U)

include hC in
theorem signed {j m : ℕ} (hj : j ≤ N) {F D : Config G (C.side j p)→Poly Γ}
    (hD : ∀T,D T=(C.path.rep N p j).eval T • F T) (hm : m ≤ j) :
    actualSignedTransport C (N:=N) D hm = actualTransport C (N:=N) F hm := by
  have input : (fun T=>((C.path.rep N p j).eval T)⁻¹ • D T)=F := by
    funext T
    rw [hD,smul_smul,inv_mul_cancel₀ (Multi.AxisShift.chosen_positive hC.wilson hj T).ne',one_smul]
  unfold actualSignedTransport
  rw [input]

include hC hw in
theorem comparison {j m : ℕ} (hj : j ≤ N) {F Q D E : Config G (C.side j p)→Poly Γ}
    (hF : Integrable (fun T=>(C.path.rep N p j).eval T • F T) (prior G _))
    (hQ : Integrable (fun T=>(C.path.rep N p j).eval T • Q T) (prior G _))
    (hD : ∀T,D T=(C.path.rep N p j).eval T • F T)
    (hE : ∀T,E T=(C.path.rep N p j).eval T • Q T) (hm : m ≤ j) :
    ∫ U,Poly.price w (actualSignedTransport C (N:=N) D hm U-actualSignedTransport C (N:=N) E hm U)
      ∂scene C.path N p m ≤ ∫ T,Poly.price w (F T-Q T) ∂scene C.path N p j := by
  rw [signed C hC hj hD hm,signed C hC hj hE hm]
  have diff : Integrable (fun T=>(C.path.rep N p j).eval T • (F T-Q T)) (prior G _) :=
    (hF.sub hQ).congr (ae_of_all _ fun T=>(smul_sub _ (F T) (Q T)).symm)
  simpa only [subtract C hC hj hF hQ hm] using first C hC hw hj diff hm

end YM.Integration.OriginalMarkedPriceTransport
end
