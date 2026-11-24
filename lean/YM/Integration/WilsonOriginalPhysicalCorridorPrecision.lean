import YM.Integration.WilsonOriginalMountedOrder

/-! Accuracy of an ordinary face after restoring its priced peers on the genuine finite Wilson interval. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalPhysicalCorridorPrecision
open Function Finset Filter Lattice Wilson RG Tree Marker Multi QuadraticLocal Ac MeasureTheory
open Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit
open WheelP AnalyticBridge VerifiedReset PhysicalNext PhysicalNext.Repeat Legato
open Pressure ConnectedActivityE6 Push.AbsoluteSums MergeProof.Accent QuadraticLocal.Advent
open WilsonOriginalOccupiedStencil WilsonOriginalOccupiedCorridor WilsonThermometerMixedCollarSubpower
open WilsonPhysicalMarkedDefect.RegularProjection WilsonMeasuredCoefficientTransport
open Source Labels
open Pert.Asymptotics WilsonOriginalOccupiedWindow WilsonOriginalJointTrialHearing
open scoped Classical BigOperators

theorem shares (L:ℕ)(t:Fin L→ℝ){z:ℝ}(zp:0 ≤ z)(cap:∀j,t j ≤ z):
    ∑j:Fin L,t j/WilsonOriginalOccupiedDateShare.weight j.val ≤ z:=by
  have total:∑j:Fin L,1/WilsonOriginalOccupiedDateShare.weight j.val ≤ 1:=by
    rw [Fin.sum_univ_eq_sum_range (fun a => 1/WilsonOriginalOccupiedDateShare.weight a)]
    rw [WilsonOriginalOccupiedDateShare.total]
    exact sub_le_self _ (by positivity)
  calc
    _ ≤ ∑j:Fin L,z*(1/WilsonOriginalOccupiedDateShare.weight j.val):=sum_le_sum fun j _=>by
      rw [mul_one_div];exact div_le_div_of_nonneg_right (cap j) (by unfold WilsonOriginalOccupiedDateShare.weight;positivity)
    _ = z*∑j:Fin L,1/WilsonOriginalOccupiedDateShare.weight j.val:=(mul_sum ..).symm
    _ ≤ z:=by simpa only [mul_one] using mul_le_mul_of_nonneg_left total zp

theorem wallet (L p H P:ℕ){g e c:ℝ}(gp:0<g)(gs:g ≤ 1)(ep:0 ≤ e)(cp:0 ≤ c)(order:P+H ≤ p)
    (t:Fin L→ℝ)(cap:∀j,t j ≤ (g^H)⁻¹):
    (e*g^p*c)*(∑j:Fin L,t j/WilsonOriginalOccupiedDateShare.weight j.val) ≤ e*c*g^P:=by
  have ht:=shares L t (inv_nonneg.mpr (pow_nonneg gp.le H)) cap
  have hg:g^p ≤ g^(P+H):=pow_le_pow_of_le_one gp.le gs order
  calc
    _ ≤ (e*g^p*c)*(g^H)⁻¹:=mul_le_mul_of_nonneg_left ht (by positivity)
    _ ≤ (e*g^(P+H)*c)*(g^H)⁻¹:=mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hg ep) cp) (by positivity)
    _ = _:=by rw [pow_add];field_simp

theorem dates (L P:ℕ){g C A:ℝ}(gp:0 ≤ g)(cp:0 ≤ C)(length:(L:ℝ)*g ≤ A)(t:Fin L→ℝ)
    (fee:∀j,t j ≤ C*g^(P+1)):∑j:Fin L,t j ≤ A*C*g^P:=by
  calc
    _ ≤ ∑_j:Fin L,C*g^(P+1):=sum_le_sum fun j _=>fee j
    _ = ((L:ℝ)*g)*(C*g^P):=by simp [pow_succ];ring
    _ ≤ A*(C*g^P):=mul_le_mul_of_nonneg_right length (by positivity)
    _ = _:=(mul_assoc ..).symm

variable {G:Gauge}(R:Run G)(simple:G.Simple)
variable {V:Type}[DecidableEq V][Fintype V](marks:Marker.Census V)
local notation "H" j:max => R.family.path.levels.clock.hatBeta j
include simple in
theorem original (n d a p desired debt ext:ℕ)(np:0<n)(load:∀s:marks.Mode,s.val.card ≤ n)(C e A:ℝ)(cp:0 ≤ C)(ep:0<e)(order:desired+ext ≤ p):
    ∃start:ℕ,∀(b N per m k L:ℕ),start ≤ b → m ≤ b+1 → ∀(live:b+1+L ≤ N),
    (∀j:Fin L,(j.val:ℝ) ≤ C*(1+Real.log (H (b+j.val+1)))^d) →
    ∀(_way:WayStation R.kit)(D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
    (Q:D.Tab R.rolls)(π:ℕ → Layout G)(Γ:ℕ → Pace.Coin)(Ψ:∀j,RG.Rep G (R.family.side j per)),
    Concourse R.alloy R.kit R.T π Γ m N per k Ψ → TicketP R.alloy R.kit D Q →
    ∀(physical:Config G (R.family.side N per)→Poly marks),
    Integrable physical (prior G _) →
    ∀(trial:∀j,Config G (R.family.side j per)→Poly marks),
    (∀i,b+1 ≤ i → i ≤ b+1+L → Integrable (trial i) (prior G _)) →
    ∀(P:∀j:Fin L,Slice R marks (Ψ (b+j.val+1))),
    (∀j:Fin L,(P j).A.density (P j).x=LocalComparison.actualPush R.family N per (b+j.val+1) (trial (b+j.val+1+1))) →
    ∀(s:marks.Mode)(S:Fin L → V → ℝ),(∀j v,0 < S j v) → (∀j:Fin L,(WilsonOriginalOccupiedSalary.debit (P j).regular (P j).hard)^s.val.card ≤
      (H (b+j.val+1))^a*(Poly.toll (S j) s*Poly.toll (P j).w s)) →
    ∀W:Config G (R.family.side (b+1) per),flags (Ψ (b+1)).p.threshold W=∅ →
    ∀{d₀:ℕ}{frame:Frame G d₀}(section_:SectionData frame)(group:Hol G)
    (F:∀j:Fin L,WilsonOriginalMountedRegular.Filing R (Ψ (b+j.val+1)) (P j) (trial (b+j.val+1)) s),
    let enter:=read R N per W (show b+1 ≤ b+1+L by omega)
      (gust R.family.path N per N physical (b+1+L) live-trial (b+1+L)) s
    let spring:=WilsonOriginalDecoderSpring.bill (R.family.path.levels.clock.op (b+1) per)
      (R.family.path.β N per (b+1+1)) W
    let g:=regulatorRun R.family N per (b+1)
    0<g → g ≤ 1 → (L:ℝ)*g ≤ A → (∀j,0 ≤ R.alloy.B.a.clock.hatBeta (b+(j:Fin L).val+1)) →
    (∀j,Poly.toll (S j) s ≤ (g^ext)⁻¹) → (∀j,(F j).M ≤ (g^debt)⁻¹) →
    (∀j,(F j).W*(F j).rent+(F j).W*((Real.exp ((F j).α*(F j).h))⁻¹*(F j).gross)+(F j).δ ≤
      g^(desired+1+debt*s.val.card)) →
    (∀j,WilsonOriginalMountedOrder.event (F j) (b+1) e (R.alloy.B.a.clock.hatBeta (b+j.val+1)) spring p ≤
      g^(desired+1+debt*s.val.card)) →
    ‖read R N per W (show b+1 ≤ N by omega) physical s-
      (((R.family.path.rep N per (b+1)).eval W:ℂ)⁻¹)*(trial (b+1) W).part s‖ ≤
      ‖enter‖+(A*WilsonOriginalOrdinaryFaceOrder.constant s s.val.card+e*(shards marks s).card)*g^desired:=by
  obtain ⟨start,Coeff⟩:=WilsonOriginalSignedPhysicalCorridor.original R simple marks n d a p np load C e cp ep
  refine ⟨start,?_⟩
  intro b N per m k L age mb live span way D Q π Γ Ψ course ticket physical hp trial ht slices source s S sp wage W clear
    d₀ frame section_ group F
  dsimp only
  let g:=regulatorRun R.family N per (b+1)
  let spring:=WilsonOriginalDecoderSpring.bill (R.family.path.levels.clock.op (b+1) per)
    (R.family.path.β N per (b+1+1)) W
  let reg (j:Fin L):=(F j).bill (b+1) e (R.alloy.B.a.clock.hatBeta (b+j.val+1)) spring p
  intro gp gs length positive toll gross small failed
  have c0:0 ≤ WilsonOriginalOrdinaryFaceOrder.constant s s.val.card:=by unfold WilsonOriginalOrdinaryFaceOrder.constant;positivity
  have perdate (j:Fin L):reg j ≤ WilsonOriginalOrdinaryFaceOrder.constant s s.val.card*g^(desired+1):=
    WilsonOriginalMountedOrder.original (F j) (b+1) p debt (desired+1) ep.le (positive j) gp gs (gross j) (small j) (failed j)
  have sums:=dates L desired gp.le c0 length reg perdate
  have hard:=wallet L p ext desired gp gs ep.le (Nat.cast_nonneg (shards marks s).card) order (fun j=>Poly.toll (S j) s) toll
  exact (Coeff b N per m k L age mb live span way D Q π Γ Ψ course ticket physical hp trial ht slices source s S sp wage W clear
    section_ group F).trans ((add_le_add (add_le_add le_rfl sums) hard).trans_eq (by ring))

end YM.Integration.WilsonOriginalPhysicalCorridorPrecision
end
