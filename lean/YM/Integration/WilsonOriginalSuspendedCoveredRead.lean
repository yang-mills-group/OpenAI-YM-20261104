import YM.Integration.WilsonOriginalMixedCoveredRead

/-! Mixed jets after clearing a real Laurent power on the original counted covered group field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalSuspendedCoveredRead
open Function Finset Lattice RG Wilson Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Poetry QuadraticLocal.Sunrise Stationary
open Further.PhysicalPeriodLimitF933 Macrame FVA1Physical FVA1Physical.TwoReset
open WilsonOriginalPaidWalkCover WilsonOriginalSuspendedWord WilsonEmittedRootedJetWage WilsonOriginalSuspendedFootprint
open WilsonOriginalMixedCoveredRead
open scoped Classical BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge} {n N:Side} {V X ι:Type} [DecidableEq V] {o:Passport n V} {J:Census V}

def shift (A:Row o J G X) (s:ℕ): Row o J G X :=
  { A with lamp := { A.lamp with e:=s+A.lamp.e, crest:=by have H:=A.lamp.crest;omega }, atom:=A.atom }

theorem stamp (A:Row o J G X) (s:ℕ): (shift A s).lamp.stamp=s+A.lamp.stamp:=by
  have H:=A.lamp.crest
  simp only [shift,Loan.stamp]
  omega

theorem purchased (M:ι→Row o J G X) {w:V→ℝ} {grades:V→ℕ} {σ C:ℝ} {order seats shelf:ℕ}
    (stock:Scene.Armada M w grades σ C order seats shelf) (s:ℕ):
    Scene.Armada (fun i=>shift (M i) s) w grades σ C (s+order) seats shelf:=
  { stock with suggests:=stock.suggests, honor:=stock.honor, purchases:=
    ⟨stock.purchases.spend,fun i=>⟨Nat.add_le_add_left (stock.purchases.usable i).1 s,(stock.purchases.usable i).2⟩⟩ }

variable (h:n.val∣N.val) (M:ι→Row o J G X) (t:X) (p:Fin (Pages n N)) (which:ι→Prop)

private theorem shifted (i:ι)(s:ℕ):
    colored (row h (shift (M i) s) p) t 0=colored (row h (M i) p) t s:=by
  funext z
  unfold colored Loan.letter
  change (M i).paint t*(z.1^0*(z.1^(shift (M i) s).lamp.stamp*(M i).atom.unmasked (RG.increment 1 z.2) _):ℝ)=_
  rw [stamp,pow_add,pow_zero,one_mul,mul_assoc]
  rfl

theorem original {w:V→ℝ} {grades:V→ℕ} {σ C:ℝ} {order seats shelf:ℕ}
    (stock:Scene.Armada M w grades σ C order seats shelf) (σ0:0<σ) (s r:ℕ) (u:Fin r→Slot G N):
    HasSum (fun i=>if which i then «at» (row h (M i) p) t s r u else 0)
      (iteratedFDeriv ℝ r (fun z:Joint G N=>(z.1^s:ℝ)*field h M t p which z) 0 (peg G N ∘ u)):=by
  have H:=WilsonOriginalMixedCoveredRead.original h (fun i=>shift (M i) s) t p which (purchased M stock s) σ0 r u
  have val:field h (fun i=>shift (M i) s) t p which=
      fun z:Joint G N=>(z.1^s:ℝ)*field h M t p which z:=by
    funext z
    unfold field
    rw [←tsum_mul_left]
    apply tsum_congr
    intro i
    split_ifs with active
    · have W:=congrFun (shifted h M t p i s) z
      unfold colored at W
      simp only [pow_zero,one_mul,Complex.ofReal_mul] at W
      change (row h (shift (M i) s) p).paint t * _ = (z.1 ^ s : ℝ) * ((row h (M i) p).paint t * _)
      rw [W]
      ring
    · rw [mul_zero]
  rw [val] at H
  apply H.congr_fun
  intro i
  split_ifs with active
  · unfold WilsonOriginalSuspendedFootprint.at
    rw [shifted]
  · rfl

end YM.Integration.WilsonOriginalSuspendedCoveredRead
