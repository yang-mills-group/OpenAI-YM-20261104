import YM.Integration.WilsonPositionOriginalDressedQJointMoment

/-! Quantitative removal of the short lamps on the original pair of physical
dates. Each of the two corrected arms has its own true, disjoint support. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionOriginalDressedQCutSquare
open Set Function MeasureTheory Lattice Wilson RG Marker Cells QuadraticLocal Push.GridApprox
open PhysicalNext.Repeat.Legato OPE.Therm QLocalPhysicalPathKernel WilsonMacroscopicForwardTransfer
open WilsonPositionOriginalDressedQFailedPath WilsonPositionOriginalDressedQLiteralLamp
open WilsonRootedKioskOccupiedSlip
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G){N p i:ℕ}{V T I:Type}
  [DecidableEq V][Countable I]{o:V→Site (R.family.side i p)}
  {P:BudgetPoint}{Γ:Census V}(L:Lamps T I G P o Γ){w:V→ℝ}{a d:ℝ}
open private pulled from YM.Integration.WilsonPositionOriginalDressedQPathHearing

def bound (s:Γ.Mode):ℝ:=(Poly.toll w s)⁻¹*d
def tailFee (m:ℕ)(s:Γ.Mode):ℝ:=(Poly.toll w s*Real.exp (a*m))⁻¹*d

private theorem subtract {Ω:Type}[MeasurableSpace Ω]{F H:Ω→ℂ}(f:Envelope F)(h:Envelope H):
    Envelope fun x=>F x-H x:=by
  obtain ⟨A,af⟩:=f.cost;obtain ⟨B,bh⟩:=h.cost
  exact ⟨f.meas.sub h.meas,A+B,fun x=>(norm_sub_le ..).trans (add_le_add (af x) (bh x))⟩

theorem original (live:i<N)(lengthCut B:ℕ)(hw:∀v,0<w v)(ha:0 ≤ a)(cash:Gross L w B a d)
    (z z':V)(s u:Γ.Mode)(zs:z∈s.val)(zt:z'∈u.val)(t:T)
    (separate:Disjoint (region B lengthCut (o z)) (region B lengthCut (o z')))
    (Q₁ Q₂:Config G (R.family.side (i+1) p)→ℂ)(h₁:Measurable Q₁)(h₂:Measurable Q₂)
    (fee₁ fee₂:ℝ)(f₁:∀U,‖Q₁ U‖≤fee₁)(f₂:∀U,‖Q₂ U‖≤fee₂):
    let A:=short L B lengthCut s t
    let C:=short L B lengthCut u t
    let step:=backTo R.family.path N p (Nat.le_succ i)
    ‖(∫U,(Q₁ U-step A U)*(Q₂ U-step C U) ∂scene R.family.path N p (i+1))-
    (∫ω:ConfigurationPath R p,(Q₁ (ω (i+1))-(bare L t (ω i)).part s)*
      (Q₂ (ω (i+1))-(bare L t (ω i)).part u) ∂path R.family R.makes N p)‖≤
      tailFee (w:=w) (a:=a) (d:=d) lengthCut s*(fee₂+bound (w:=w) (d:=d) u)+
      (fee₁+bound (w:=w) (d:=d) s)*tailFee (w:=w) (a:=a) (d:=d) lengthCut u:=by
  intro A C step
  have eA:=cylinder L B lengthCut hw ha cash s z zs t
  have eC:=cylinder L B lengthCut hw ha cash u z' zt t
  have q₁:Envelope Q₁:=⟨h₁,fee₁,f₁⟩
  have q₂:Envelope Q₂:=⟨h₂,fee₂,f₂⟩
  rw [←WilsonPositionOriginalDressedQPathSquare.original R live Q₁ Q₂ q₁ q₂ A C eA eC separate]
  let law:=path R.family R.makes N p
  letI:IsProbabilityMeasure law:=path_probability R.family R.makes N p
  let X:ConfigurationPath R p → Config G (R.family.side (i+1) p):=fun ω=>ω (i+1)
  let W:ConfigurationPath R p → Config G (R.family.side i p):=fun ω=>ω i
  let G₁:=fun U=>(bare L t U).part s
  let G₂:=fun U=>(bare L t U).part u
  have old₁:Envelope (G₁ ∘ W):=pulled (WilsonPositionOriginalDressedQPublishedField.entire L hw ha cash s z zs t) (measurable_pi_apply _)
  have old₂:Envelope (G₂ ∘ W):=pulled (WilsonPositionOriginalDressedQPublishedField.entire L hw ha cash u z' zt t) (measurable_pi_apply _)
  have hi₁:Envelope (Q₁ ∘ X):=pulled q₁ (measurable_pi_apply _)
  have hi₂:Envelope (Q₂ ∘ X):=pulled q₂ (measurable_pi_apply _)
  have cut₁:Envelope (A ∘ W):=pulled (cylinder_env eA) (measurable_pi_apply _)
  have cut₂:Envelope (C ∘ W):=pulled (cylinder_env eC) (measurable_pi_apply _)
  have first:=((subtract hi₁ cut₁).mulC (subtract hi₂ cut₂)).integrableC law
  have next':=((subtract hi₁ old₁).mulC (subtract hi₂ old₂)).integrableC law
  have split:=integral_sub first next'
  simp only [comp_apply,X,W,G₁,G₂,law] at split
  rw [←split]
  have budget (ω:ConfigurationPath R p):
      ‖((Q₁ (X ω)-A (W ω))*(Q₂ (X ω)-C (W ω)))-
        ((Q₁ (X ω)-G₁ (W ω))*(Q₂ (X ω)-G₂ (W ω)))‖ ≤
        tailFee (w:=w) (a:=a) (d:=d) lengthCut s*(fee₂+bound (w:=w) (d:=d) u)+
        (fee₁+bound (w:=w) (d:=d) s)*tailFee (w:=w) (a:=a) (d:=d) lengthCut u:=by
    have eqn:((Q₁ (X ω)-A (W ω))*(Q₂ (X ω)-C (W ω)))-
        ((Q₁ (X ω)-G₁ (W ω))*(Q₂ (X ω)-G₂ (W ω)))=
      (G₁ (W ω)-A (W ω))*(Q₂ (X ω)-C (W ω))+(Q₁ (X ω)-G₁ (W ω))*(G₂ (W ω)-C (W ω)):=by ring
    rw [eqn]
    apply (norm_add_le ..).trans
    simp only [norm_mul]
    have t₁:=tail L B lengthCut hw ha cash s z zs t (W ω)
    have t₂:=tail L B lengthCut hw ha cash u z' zt t (W ω)
    have g₁:=WilsonPositionOriginalDressedQPublishedField.charged L hw ha cash s z zs t (W ω)
    have g₂:‖C (W ω)‖≤bound (w:=w) (d:=d) u:=by
      simpa [C,short,bound] using WilsonPositionOriginalDressedQLampColumn.original (m:=0) L hw ha cash u z' zt
        (fun j=>coverNumber B (L.ground j)<lengthCut) (fun _ _ _=>Nat.zero_le _) t (W ω)
    exact add_le_add (mul_le_mul t₁ ((norm_sub_le ..).trans (add_le_add (f₂ _) g₂)) (norm_nonneg _) ((norm_nonneg _).trans t₁))
      (mul_le_mul ((norm_sub_le ..).trans (add_le_add (f₁ _) g₁)) t₂ (norm_nonneg _)
        (add_nonneg ((norm_nonneg _).trans (f₁ (X ω))) ((norm_nonneg _).trans g₁)))
  simpa [law,X,W,G₁,G₂] using norm_integral_le_of_norm_le_const (ae_of_all law budget)

end YM.Integration.WilsonPositionOriginalDressedQCutSquare
