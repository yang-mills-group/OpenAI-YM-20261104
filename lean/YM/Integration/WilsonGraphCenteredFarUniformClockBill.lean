import YM.Integration.WilsonGraphCenteredFarBentHeater
import YM.Integration.WilsonGraphCenteredFarUniformBilinearStock

set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section
namespace YM.FVA2.GradedFar.AppointedUniformClockBill
open Function Filter Real PowerSeries Finset Continuation Growth
open Register MS MS.Native MS.Land MS.Book MS.Book.Program
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Enh O.Score O.Canon Scale Dframe Reg.Point Jury
open YangMills YM.Answer.ContinuumLimit YM.Integration
open scoped Topology BigOperators Classical
universe u
variable (g : GaugeGroup) (hg : g.IsSimple) (periods : ℕ → ℕ) (strict : StrictMono periods)
private abbrev Z := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
private abbrev Q := WilsonGraphPaperPublication.perspective.{u} g hg
private abbrev θ := ElectedMeasurement.clock
  (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order periods strict)) (Z g hg)

theorem onStage (h p : ℕ) {C B : ℝ} (hC : 0<C) (hB : 0<B) :
    ∃ D : ℝ, 0≤D ∧ ∃ a : ℕ, ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ s≥0,
      exp s≤C*(gYM g.core r)^(-B) → ∀ (farBorn : Bool) (x : Scale.Stage 2) (u v : Sec g.core h),
      let ψ := GroupS.ψ (Z g hg).criterion (Q.{u} g hg).MS (Teller.logNu 1) (-s)
      let A := Kseries (Z g hg) (Q.{u} g hg).MS h s
      let V := AppointedFixedBilinearCrop.secondField (Z g hg) (Q.{u} g hg).MS h s farBorn
      let F := AppointedBilinearCauchy.full (Z g hg) h x A V u v
      ‖crop p (θ.{u} g hg periods strict (r*exp s)) F -
          crop p (θ.{u} g hg periods strict r) (F.subst ψ)‖ ≤
        (AppointedSignedInsertion.budget (Z g hg) h p x*‖chair g.core h u‖*‖chair g.core h v‖)*
          (D*(gYM g.core r)^(p+1)*(1+s)^a) := by
  let N := Z g hg
  let M := (Q.{u} g hg).MS
  let law := ((Q.{u} g hg).matching.dilation (Teller.logNu 1)).check
  obtain ⟨D,hD,a,bend⟩ := AppointedBentHeater.original.{u} g hg periods strict p hC hB
  obtain ⟨E,hE,e,billed⟩ := AppointedUniformBilinearStock.uniform N M (Q.{u} g hg).matching h p p
  obtain ⟨L,hL,b,clock⟩ := Appointed220.Zones.clock_log law p
  obtain ⟨_,_,_,far⟩ := AppointedCenteredTransport.farHeaterRate.{u} g hg periods strict p hC hB
  let J := max 1 L
  have j1 : 1≤J := le_max_left _ _
  have j0 : 0≤J := zero_le_one.trans j1
  let d1 := E*p*D
  let d2 := p*J^p*E*2^(p+1)
  have h1 : 0≤d1 := by dsimp only [d1]; positivity
  have h2 : 0≤d2 := by dsimp only [d2]; positivity
  refine ⟨d1+d2,add_nonneg h1 h2,e+a+b*p,?_⟩
  filter_upwards [bend,far] with r bent measured s hs eligible farBorn x u v
  intro ψ A V F
  let X := AppointedSignedInsertion.budget N h p x*‖chair g.core h u‖*‖chair g.core h v‖
  have hX : 0≤X := mul_nonneg (mul_nonneg (AppointedSignedInsertion.budgetNonneg N h p x) (norm_nonneg _)) (norm_nonneg _)
  let t := θ.{u} g hg periods strict r
  let f := θ.{u} g hg periods strict (r*exp s)
  let z := gYM g.core r
  have hv : |f|≤1 := (measured s hs eligible).2
  obtain ⟨error,hw,ht,nt,hz⟩ := bent s hs eligible
  have base : 1≤1+s := le_add_of_nonneg_right hs
  have pos : 0≤1+s := zero_le_one.trans base
  let bill := J*(1+s)^b
  have below : 1≤bill := (one_le_mul_of_one_le_of_one_le j1 (one_le_pow₀ base))
  have massq : Appointed220.Eval.mass p ψ≤bill := by
    have c : Appointed220.Eval.mass p ψ≤L*(1+s)^b := by simpa only [abs_neg,abs_of_nonneg hs] using clock (-s)
    exact c.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg pos _))
  have mass : Appointed220.Eval.mass p F≤X*(E*(1+s)^e) := by
    change AppointedScalarOverflow.mass p F≤_
    exact (AppointedUniformBilinearStock.fullMass N h p x A V u v).trans (billed s hs farBorn x u v)
  have m0 := Appointed220.Eval.mass_nonneg F p
  have zm := pow_nonneg hz (p+1)
  have cp : 0≤(p:ℝ) := Nat.cast_nonneg _
  have tp : |t|^(p+1)≤2^(p+1)*z^(p+1) := by simpa only [mul_pow] using pow_le_pow_left₀ (abs_nonneg t) nt (p+1)
  have first :
      Appointed220.Eval.mass p F*(p*‖(f:ℂ)-Appointed220.Eval.value p ψ (t:ℂ)‖) ≤
        X*(d1*z^(p+1)*(1+s)^(e+a+b*p)) := by
    calc _ ≤ (X*(E*(1+s)^e))*(p*(D*z^(p+1)*(1+s)^a)) := mul_le_mul mass
            (mul_le_mul_of_nonneg_left error cp) (mul_nonneg cp (norm_nonneg _)) (mul_nonneg hX (mul_nonneg hE (pow_nonneg pos _)))
         _ = X*(d1*z^(p+1)*(1+s)^(e+a)) := by dsimp only [d1];rw [pow_add];ring
         _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ base (by omega)) (mul_nonneg h1 zm)) hX
  have second :
      (p*bill^p)*Appointed220.Eval.mass p F*|t|^(p+1) ≤ X*(d2*z^(p+1)*(1+s)^(e+a+b*p)) := by
    have b0 : 0≤p*bill^p := mul_nonneg cp (pow_nonneg (zero_le_one.trans below) _)
    calc _ ≤ (p*bill^p)*(X*(E*(1+s)^e))*(2^(p+1)*z^(p+1)) :=
            mul_le_mul (mul_le_mul_of_nonneg_left mass b0) tp (pow_nonneg (abs_nonneg _) _)
              (mul_nonneg b0 (mul_nonneg hX (mul_nonneg hE (pow_nonneg pos _))))
         _ = X*(d2*z^(p+1)*(1+s)^(e+b*p)) := by dsimp only [d2,bill];rw [mul_pow,pow_add (1+s) e (b*p),pow_mul (1+s) b p];ring
         _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ base (by omega)) (mul_nonneg h2 zm)) hX
  have paid := AppointedScalarRecomposition.price p F ψ (law.led (-s)).start f t hv ht hw bill below massq
  exact paid.trans ((add_le_add first second).trans_eq (by ring))

end YM.FVA2.GradedFar.AppointedUniformClockBill
