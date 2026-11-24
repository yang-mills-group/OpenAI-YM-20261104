import YM.Integration.WilsonMacroscopicRichOutputNorm

/-! A signed change of the independently filed coefficient on the same nonlinear regulator probes. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichMSProbeTransition
open Function Pert Pert.Position MS MS.Local.Physical MS.Menus MS.Land MS.Theater
open FVA2 FVA2.O FVA2.ColorCode RegulatorIR.FVAAlt2.Lodge Extra.FD OPE.Levy
open FVA2.Scale Extraction Table Spec Climb PhysicalNext.Repeat.Legato PhysMS
open Wilson Lattice Trace.Physical.GermGraph Trace.Physical RG16 RG16.Literal Analysis
open Push.Local Source Labels ProjectorNext.Equivariance RGComparison.Core16
open WilsonMacroscopicRichCapturedProbes WilsonMacroscopicRichCapturePropagation
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G){S:Table R.family.book}
local notation "B₀" => Press.portDeck G

def error {h u b N p:ℕ}(P:Finset (Probe G h))(J:ℝ→tower S)(r:ℝ)
    (door:Opened R.family h u p)(ub:u≤b)(uN:u≤N)(A:Glyph B₀ h→ℂ)
    (Z:Config G (R.family.side b p)→ℂ):ℝ:=
  ∑t∈P,‖(∑a:Glyph B₀ h,A a*WilsonMacroscopicRichMSProbe.read R J r door uN t
    ((exactField R.family.labels h).symm ((Daylight B₀ h) a)))-
    Germ.jet R.family.params t (R.family.path.rep N p u).p.threshold 0 (returned R (N:=N) ub h Z)‖

theorem filed {n h u:ℕ}(M:MS_Data G (Position.OpenAxis.Plot B₀))(J:ℝ→tower S)(doors:∀p,Opened R.family h u p):
    ∃K:ℝ,0≤K ∧ ∀(r:ℝ)(N p b:ℕ)(ub:u≤b)(uN:u≤N)(P:Finset (Probe G h))(d:Fin n→ℕ)
      (v:(i:Fin n)→(Bel R.family.book).Field (d i))(μ:ℝ)(x:Points n)(γ:ℝ)(q:ℕ)
      (A:Glyph B₀ h→ℂ)(Z:Config G (R.family.side b p)→ℂ),
      let c:=WilsonMacroscopicRichMSCoefficient.coefficient R M d v μ x γ q (h:=h)
      let e:Glyph B₀ h→(Bel R.family.book).Field h:=fun a=>(exactField R.family.labels h).symm ((Daylight B₀ h) a)
      WilsonMacroscopicRichIndependentHearing.debit R P (doors p) ub uN
        (S.representative h (J r h (WilsonMacroscopicRichMSCoefficient.field R M h d v μ x γ q))) Z≤
          error R P J r (doors p) ub uN A Z +
          (∑t∈P,‖runProbe (R.family.labels.level h) t‖*K)*
            ∑a:Glyph B₀ h,‖c a-A a‖*‖S.representative h (J r h (e a))‖:=by
  classical
  obtain ⟨K,nn,sold⟩:=WilsonMacroscopicRichOutputNorm.purchased R h u doors
  refine ⟨K,nn,?_⟩
  intro r N p b ub live P d v μ x γ q A Z
  let c:=WilsonMacroscopicRichMSCoefficient.coefficient R M d v μ x γ q (h:=h)
  let e:Glyph B₀ h→(Bel R.family.book).Field h:=fun a=>(exactField R.family.labels h).symm ((Daylight B₀ h) a)
  let mark:Glyph B₀ h→R.family.label h:=fun a=>S.representative h (J r h (e a))
  let row (t:Probe G h)(a:Glyph B₀ h):=WilsonMacroscopicRichMSProbe.read R J r (doors p) live t (e a)
  let L (t:Probe G h):=runProbe (R.family.labels.level h) t
  let cash:=∑a:Glyph B₀ h,‖c a-A a‖*‖mark a‖
  let jet (t:Probe G h):=Germ.jet R.family.params t (R.family.path.rep N p u).p.threshold 0 (returned R (N:=N) ub h Z)
  have delta (t:Probe G h):‖(∑a,c a*row t a)-(∑a,A a*row t a)‖≤(‖L t‖*K)*cash:=by
    rw [←Finset.sum_sub_distrib]
    calc
      _ ≤ ∑a,‖c a*row t a-A a*row t a‖:=norm_sum_le _ _
      _ ≤ ∑a,(‖L t‖*K)*(‖c a-A a‖*‖mark a‖):=by
        refine Finset.sum_le_sum fun a _=>?_
        have pr:‖row t a‖≤‖L t‖*(K*‖mark a‖):=((L t).le_opNorm _).trans
          (mul_le_mul_of_nonneg_left (sold N p live (mark a)) (L t).opNorm_nonneg)
        rw [←sub_mul,norm_mul]
        exact (mul_le_mul_of_nonneg_left pr (norm_nonneg _)).trans_eq (by ring)
      _ = _:= (Finset.mul_sum ..).symm
  rw [WilsonMacroscopicRichMSProbe.observed]
  change (∑t∈P,‖(∑a,c a*row t a)-jet t‖)≤(∑t∈P,‖(∑a,A a*row t a)-jet t‖)+(∑t∈P,‖L t‖*K)*cash
  rw [Finset.sum_mul,←Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun t _=>?_
  have tri:=dist_triangle (∑a,c a*row t a) (∑a,A a*row t a) (jet t)
  simp only [dist_eq_norm] at tri
  exact tri.trans ((add_le_add (delta t) le_rfl).trans_eq (add_comm _ _))

end YM.Integration.WilsonMacroscopicRichMSProbeTransition
