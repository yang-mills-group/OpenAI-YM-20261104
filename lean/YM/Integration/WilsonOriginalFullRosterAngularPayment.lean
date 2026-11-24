import YM.Integration.WilsonOriginalFullRosterAngularReturn
import YM.Integration.WilsonOriginalFullRosterCropFare
import YM.Integration.WilsonOriginalCensusAngularFace

/-! The actual signed angular account pays the difference of the original two unmasked posts
on the common short field, with the genuine group and derivative tails. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalFullRosterAngularPayment
open Function Finset Lattice RG Wilson Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Earn.Scene QuadraticLocal.Sunrise
open Comparison.Density Comparison.Density.Mirrors Comparison.Density.Transport
open WilsonOriginalCensusAngularFace WilsonEmittedFiledCatalogue
open AnalyticBridge.SectorAffine.Offset
open scoped BigOperators ContDiff Classical Matrix.Norms.Frobenius
private abbrev sign (a:Bool):ℝ:=if a then -1 else 1
variable {G:Gauge}{n:Side}{V:Type}[Fintype V][DecidableEq V]{Γ:Census V}
  {I X:Bool→Type}{P:Bool→Passport n V}(M:(a:Bool)→I a→Row (P a) Γ G (X a))
  (w:Bool→V→ℝ)(grades:Bool→V→ℕ)(x:(a:Bool)→X a)
  (B:BudgetPoint)(σ b θ:Bool→ℝ)(p pieces depth:Bool→ℕ)(g:ℝ)
  (s:Multi.Hot Γ)(v:V)(o:Site n)(tube:LinkTube G)

/-- The only increased clock opening depends on the requested Taylor test and the size
of its actual finite rooted roster. -/
def opening (T n:ℕ):ℝ:=(256*((T*(4*(n+1)):ℕ)+1:ℝ))^2

omit [Fintype V] in
theorem original {K:Bool→ℝ}
    (scope:∀a,Invoice.Supports B (K a) (B.supportExponent+2) g (σ a) (θ a))
    (wallet:∀a v,0<w a v)(income:∀a,0 ≤ b a)
    {δ:ℝ}(q:Probe M w grades x B σ b θ p pieces depth g s v o tube δ)
    (fronts:ℕ)(enrolled:64*(fronts+1) ≤ B.B)(late:opening q.T fronts ≤ Real.log q.hat):
    WilsonOriginalFullRosterAngularReturn.price G s w q.ℓ p pieces depth b θ B g q.width
      q.ε q.pole q.T q.J fronts ≤ δ:=by
  let cropAt:=WilsonOriginalSeparatedFrontClusters.crop B.B fronts
  let strength:=q.T*(4*(fronts+1))
  have positive:0<g:=(scope false).1
  have coin:g^2=q.beta⁻¹:=calc
    g^2=((Real.sqrt q.beta)⁻¹)^2:=congrArg (fun z:ℝ=>z^2) q.atDate
    _=q.beta⁻¹:=by rw [inv_pow,Real.sq_sqrt q.beta_pos.le]
  have invH:q.hat⁻¹ ≤ g:=by
    have compare:q.hat⁻¹ ≤ 2*g^2:=by
      rw [coin,←div_eq_mul_inv,←one_div]
      exact (div_le_div_iff₀ q.hat_pos q.beta_pos).mpr (by linarith only [q.thermal])
    exact compare.trans (by nlinarith [mul_nonneg positive.le (sub_nonneg.mpr q.small)])
  have wpos (a:Bool):0<Poly.toll (w a) s.val:=Poly.worth (wallet a) s.val
  have tpos (a:Bool):0<θ a:=(scope a).2.2.2.2.2.2.1
  have lengths (a:Bool):Real.exp (-(θ a))^cropAt ≤ g^q.T:=by
    have same:WilsonEmittedLengthWindow.strip (θ a) (σ a)=θ a:=max_eq_left (q.strip a)
    have issued:=(WilsonEmittedLengthWindow.decays (scope a) q.side (q.reserve a) q.tax strength late).2
    rw [same] at issued
    have eqn:4*θ a/4=θ a:=by ring
    have cut:=WilsonOriginalFullRosterCropFare.original B.B fronts q.T (σ:=4*θ a) enrolled
      q.hat_pos (mul_pos (by norm_num) (tpos a)) (by simpa only [eqn] using issued)
    rw [eqn,←inv_pow] at cut
    exact cut.trans (pow_le_pow_left₀ (inv_nonneg.mpr q.hat_pos.le) invH _)
  have jets:=WilsonOriginalPrintedLength.regular (G:=G) s.val w sign q.ℓ B
    (p:=p) (pieces:=pieces) (depth:=depth) (α:=fun _=>B.supportExponent+2)
    q.J cropAt wpos income tpos lengths
  have words:=WilsonOriginalPrintedLength.unmasked s.val w sign (fun _=>0) B
    (p:=p) (pieces:=pieces) (depth:=depth) cropAt wpos income tpos positive lengths
  have base:groupPrice tube 0=1:=by
    simp [groupPrice,Comparison.Density.Transport.quote,Push.Uniform.composeCost]
  have paid:=WilsonOriginalPrintedOrder.original (ε:=q.ε) q.pole q.debit q.target q.T q.chosen positive
    (q.small.trans (by norm_num)) q.radius q.held (price_nonneg _ _) q.cost_nn jets le_rfl
    (pow_nonneg positive.le _) q.jet_tariff
    (words.trans (mul_le_mul_of_nonneg_right q.word_tariff (pow_nonneg positive.le _)))
  unfold WilsonOriginalFullRosterAngularReturn.price
  simpa only [base,one_mul] using paid.trans q.quote

end YM.Integration.WilsonOriginalFullRosterAngularPayment
end
