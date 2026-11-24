import YM.Integration.WilsonOlderFreshLocatedBook

/-! Translating the earned real group field on a common appointed upper
film and word roster, before any sampling or Wilson conditioning. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 180000
noncomputable section
namespace YM.Integration.WilsonNeutralReportPlacedWord
open FormalBulk08 Lattice Wilson RG QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Affinity
open WilsonOlderFreshGraphSlate WilsonOlderFreshLocatedBook
open PhysicalNext.Repeat.Legato
open scoped Classical BigOperators
variable {G:Gauge}{d Q:ℕ}{n:Side}{σ:ℝ}

theorem atom {k:ℕ} (a:RG.Atom G k)(x y:Site n)(U:Config G n):
    a.unmasked (Lattice.translate y U) x=a.unmasked U (x+y):=by
  unfold RG.Atom.unmasked
  congr 1
  funext i
  unfold RG.Slot.atSite
  congr 1
  funext e
  simp [expandAt,Lattice.translate,add_assoc]

theorem word_shift (T:Copy G d Q σ)(x y:Site n)(A:Unit → Set ℂ)(t:Wallet A)(g:ℝ)(U:Config G n):
    word T x A t g (Lattice.translate y U)=word T (x+y) A t g U:=by
  let P:=WilsonOlderFreshGraphPointWallet.point x
  let Q₀:=WilsonOlderFreshGraphPointWallet.point (x+y)
  have full:Spill.Foundry.uncut (T.rows P A) g t (Lattice.translate y U)=Spill.Foundry.uncut (T.rows Q₀ A) g t U:=by
    unfold Spill.Foundry.uncut
    apply tsum_congr
    intro z
    unfold Spill.raw
    rw [T.group,T.group]
    rw [show P.center=x from rfl,show Q₀.center=x+y from rfl,atom]
    rfl
  exact congrArg (fun v=>v.part ((Stock.census Unit).fire ())) full

end YM.Integration.WilsonNeutralReportPlacedWord
