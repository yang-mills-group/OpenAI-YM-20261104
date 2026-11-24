import YM.Integration.WilsonPhysicalMarkedDefectSource
import YM.Integration.WilsonOriginalAlternativeSelectedPage

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalAlternativeQuietShelf
open Function Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Affinity
open Push.Corrected Push.AbsoluteSums Fusion Fusion.Attached ConnectedActivityE6
open scoped Classical BigOperators
variable {G:Gauge} {n:Side} {V E:Type} [DecidableEq V] [Fintype V] {J:Census V}
  {X:V→Type} [∀j,AddCommGroup (X j)] [∀j,Module ℝ (X j)] (actors:∀j,Set (X j))
  (pieces:∀j,Submodule ℝ (X j)) (A:Passport n V) (W:Rep G n)
  {fee:ℝ} (rent:Hard.Rent W.activities.forced W.activities.K W.p W.p.supportExponent fee)
  (L:Lamps (Wallet actors) E G W.p A.origin J)
def intake:Tint.Incoming A W (Wallet actors) E J:=⟨L,Hard.rent rent⟩
local notation "M_" => (Empty.elim : Empty→Row A J G (Wallet actors))
local notation "Z_" => intake actors A W rent L
omit [Fintype V] in
theorem original {w:V→ℝ} : (Z_).hard.Paid w W.p.B W.p.supportExponent fee ∧
    Crown A.support actors pieces (Z_).hard ∧
    ∀x a U,(Z_).hard.hard x a U=Poly.bead J ((W.activities.K a U:ℝ):ℂ):=by
  refine ⟨Hard.leasing rent,?_,fun _ _ _=>rfl⟩
  exact (WilsonPhysicalMarkedDefect.model_input_addresses (A:=A) actors pieces rent).2

omit [∀j,AddCommGroup (X j)] [∀j,Module ℝ (X j)] in
theorem field {w:V→ℝ} (wp:∀i,0<w i) {money:ℝ}
    (paid:L.Paid w W.p.B W.p.supportExponent money) (x:Wallet actors) (U:Config G n):
    (Tint.Patrol.picture M_ (Z_)).density x U=(W.eval U:ℂ) • Poly.pass (L.log x U):=by
  let G₀:=Tint.Patrol.picture M_ (Z_)
  have log:G₀.E.log x U=L.log x U:=by
    change ((rendered M_ W.p (Coat.gStep W.beta)).join L).log x U=_
    rw [Lamps.joinLog x U (hasSum_fintype _).summable (paid.sums W.p.exponent_pos.le wp x U),
      show (rendered M_ W.p (Coat.gStep W.beta)).log x U=0 from tsum_empty,zero_add]
  have gas:G₀.gas x U=Poly.bead J ((W.activities.gas W.p U:ℝ):ℂ):=
    WilsonPhysicalMarkedDefect.model_input_gas (A:=A) rent wp x U
  change G₀.density x U=_
  rw [Gallery.density,log,gas,mul_comm (Poly.pass _),Poly.product_bead,smul_smul,Rep.eval,Complex.ofReal_mul]

end YM.Integration.WilsonOriginalAlternativeQuietShelf
