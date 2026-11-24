import YM.Integration.WilsonMovingForkChronologicalTable
import YM.Integration.WilsonReceivedChronologicalMaterialEndpoint

/-! A funded post for the chosen independent material declares the actual
full density used by the optical decoder. This identification is simultaneous
in the group field and every ordinary mask. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 1500000
noncomputable section
namespace YM.Integration.WilsonMovingForkEnrolledPrint
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor QuadraticLocal.Affinity Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open Push Push.PriceCompiler Push.AbsoluteSums Stationary Comparison.RG02 QuadraticLocal.Rebirth
open VowsR LocalComparison ConnectedActivityE6 Multi Pert.Asymptotics WilsonOriginalMixedBlockRows
open WilsonMovingForkTerminalFile (Source programme)
open WilsonMovingForkChronologicalTable (density ordinary)
open WilsonMovingForkDepositedPrint (board)
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){m i N per k:ℕ}
  (hk:Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)(Q:D.Tab R.rolls)
  (π:ℕ → Layout G)(Γ:ℕ → Pace.Coin)(Ψ:∀j,Rep G (R.family.side j per))
  (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
  {φ:ℕ → ℕ}(books:Mentor.Offices.Books D R.rolls Q φ)(base:m ≤ i)
  (op:Mentor.Opportunity (R.alloy.B.a.clock.J (i+1)) (R.alloy.B.a.clock.J i))
  (lesson:Lesson (N:=N) R hk D Q π Γ base)(ahead:Mentor.Forecast D R.rolls Q φ books)
  {n K u:ℕ}{d:Fin n → ℕ}(issued:Source R d u K)(kn:K ≤ N)(ui:u ≤ i+1)(ik:i+1<K)
  (w:∀a,R.family.label (d a))(pins:Fin n → Site (R.family.side K per))

private theorem filedWidth {W:Type}[Fintype W]{size a N₀ t:ℕ}{σ τ:ℝ}{marks:Fin n → ℕ}
    {p₀:Passport (R.family.side a size) (Fin n)}{B:W → Binder p₀ (Stock.census (Fin n))}
    (M:WilsonOriginalCensusDatedMaterial.Material R N₀ a t marks σ B)(same:σ=τ)
    (g:ℝ)(x:Wallet (room (Fin n)))(U:Config G (R.family.side a size)):
    WilsonOriginalTwoFlatIRMounted.value B marks (WilsonOriginalCensusDatedMaterial.words
      (same ▸ M:WilsonOriginalCensusDatedMaterial.Material R N₀ a t marks τ B)) g x U=
    WilsonOriginalTwoFlatIRMounted.value B marks (WilsonOriginalCensusDatedMaterial.words M) g x U:=by
  cases same
  rfl

include course in
theorem original (order shelf:ℕ)(income:Fin n → ℝ)(tol:ℝ):
    let H:=issued N per kn w pins (i+1) ui ik
    let port:=Passport.point (WilsonMovingForkPrintedFile.parent R ik.le per pins)
    ∀width:H.strip=Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1)),
    let native:WilsonOriginalCensusDatedMaterial.Material R N (i+1) H.order H.load
        (Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1))) H.binder:=width ▸ H.source
    let gain:=WilsonOriginalMixedBlockBudget.roots H.binder (WilsonIndependentCollarMaterialWallet.bill native income)
    let fees:=fun a:Fin n=>income a*max 1 gain
    WilsonOriginalCensusMaterialPosting.Posted R hk D Q π Γ Ψ books base op lesson ahead
      port H.binder H.load order shelf H.order income native tol →
    ∃Z:WilsonOriginalDatedCensusInput.Filed (N:=N) R hk D Q π Γ Ψ books base ahead fees
        (((∑a,H.load a)+1+5)*(Fintype.card (Fin n))) (density (programme issued) N per w pins (i+1)),
      Z.x=H.wallet ∧ Z.grades=H.load ∧ Z.post.passport=port:=by
  intro H port width native gain fees bought
  have live:i<N:=by omega
  obtain ⟨Z,ink,grades,houses,film⟩:=WilsonReceivedChronologicalMaterialEndpoint.original
    R hk D Q π Γ Ψ course books base live op lesson ahead port H.binder H.load order shelf H.order
      income native tol bought H.wallet
  let rep:=R.family.path.rep N per (i+1)
  have name:programme issued N per w pins (i+1) ik=board H:=dif_pos ⟨kn,ui⟩
  let T:=WilsonReceivedChronologicalMaterialEndpoint.submitted R D Ψ port H.binder H.load H.order native H.wallet
  have heat:=WilsonReceivedChronologicalMaterialEndpoint.heat R π Γ Ψ course base live
  have same:T=density (programme issued) N per w pins (i+1):=by
    funext U s
    have nz:(rep.eval U:ℂ)≠0:=Complex.ofReal_ne_zero.mpr
      (AxisShift.chosen_positive R.makes.wilson (Nat.succ_le_of_lt live) U).ne'
    have heard:=congrArg (fun z:ℂ=>(rep.eval U:ℂ)*z) (film U s)
    change (rep.eval U:ℂ)*((rep.eval U:ℂ)⁻¹*(T U).part s)=_ at heard
    rw [←mul_assoc,mul_inv_cancel₀ nz,one_mul] at heard
    refine heard.trans ?_
    change (rep.eval U:ℂ)*(WilsonOriginalTwoFlatIRMounted.value H.binder H.load
      (WilsonOriginalCensusDatedMaterial.words native) (Coat.gStep (Ψ (i+1)).beta) H.wallet U).part s=
      (rep.eval U:ℂ)*(ordinary (programme issued) N per w pins (i+1) U).part s
    rw [heat,filedWidth R H.source width]
    unfold ordinary
    rw [dif_pos ik,name]
    rfl
  rw [←same]
  exact ⟨Z,ink,grades,houses⟩

end YM.Integration.WilsonMovingForkEnrolledPrint
