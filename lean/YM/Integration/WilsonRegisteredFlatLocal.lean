import YM.Integration.WilsonAxialWindow
import YM.Integration.WilsonRegisteredAffineLedger
import YM.Integration.WilsonRegisteredAffineForest
import YM.MSbar.Sat.Probe

/-! A projected old regular input has zero constant even when the original
saved compact exterior is arbitrary. Only its supported observable is
evaluated in a based local gauge. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRegisteredFlatLocal
open Filter Set Lattice RG Wilson Source Labels MSbar.Heath OPE.Therm
open scoped Classical
variable {G:Gauge} {n:Side}

theorem constant {d:ℕ} (A:Hol G) {o:Site n} {F:Config G n → ℂ} (zero:A.PiVanish d o F):
    F 1=0 := by
  let T:Jet G:=0
  have f: A.testLinks d o T 0=1:=by funext e; change A.links d T 0 _=1;rw [A.flat];rfl
  have hz:=(zero T).2 0 (Nat.zero_le _)
  simpa only [iteratedDeriv_zero,f] using hz

theorem bounded {p:BudgetPoint} (J:Voice G) (clear:Clear G J) (a:Lattice.Order) (o:Site n) (H:ℕ)
    (room:2*H<n.val) (τ r:ℝ) (weak:0 ≤ τ) (rp:0<r) (U:Config G n)
    (cut:U∈House.chilly (WilsonAxialWindow.cells o H) τ):
    let c:=(4*(H:ℝ)*Fintype.card PlaqAxes)*τ
    c ≤ J.δ → J.C*c ≤ r*p.threshold → r*p.threshold ≤ J.r → 4*J.C*r ≤ 1 → 
    ∃D:Directions G n,(∀ e, ‖D e‖ ≤ p.threshold) ∧ p.dirBound o D ∧
      (∀t∈Set.Icc 0 r,∀Y:Support n,Healthy p.threshold Y (increment 1 (t • D))) ∧
      ∀{Y:Support n} {F:Config G n → ℂ},p.Regular Y F → 
      (∀x∈Y,separation o x<H) → F U=F (increment 1 (r • D)) := by
  intro c small cash openBall stay
  let U':=Lattice.gauge (WilsonAxialWindow.frame a o U) U
  let W:Config G n:=fun e=>if separation o e.1<H then U' e else 1
  let X:Directions G n:=fun e=>J.decode (W e)
  let D:Directions G n:=r⁻¹ • X
  have J0:0 ≤ J.C:=zero_le_one.trans clear.cost
  have c0:0 ≤ c:=by dsimp [c];positivity
  have each (e:Edge (Site n)):G.chord (W e) ≤ c:=by
    by_cases h:separation o e.1<H
    · simpa only [W,if_pos h,U',c] using WilsonAxialWindow.bound a o U H room e h weak cut
    · simpa only [W,if_neg h,G.chord_one] using c0
  have backed (e:Edge (Site n)):G.lieExp (X e)=W e ∧ ‖X e‖ ≤ r*p.threshold:=by
    have read:=clear.near (W e) ((each e).trans small)
    exact ⟨read.2.1,read.2.2.trans ((mul_le_mul_of_nonneg_left (each e) J0).trans cash)⟩
  have dcap (e:Edge (Site n)):‖D e‖ ≤ p.threshold:=by
    change ‖r⁻¹ • X e‖ ≤ p.threshold
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr rp)]
    exact (mul_le_mul_of_nonneg_left (backed e).2 (inv_pos.mpr rp).le).trans_eq (by field_simp)
  have license:p.dirBound o D:=by
    intro e
    have power:(1:ℝ) ≤ (1+(separation e.1 o:ℝ))^p.power:=one_le_pow₀ (le_add_of_nonneg_right (Nat.cast_nonneg _))
    exact (dcap e).trans (le_mul_of_one_le_right p.threshold_pos.le power)
  refine ⟨D,dcap,license,?_,?_⟩
  · intro t ht Y
    let P:=increment (1:Config G n) (t • D)
    have cost (e:Edge (Site n)):G.chord (P e*((1:Config G n) e)⁻¹) ≤ J.C*(r*p.threshold):=by
      have t0:=ht.1
      have d:‖t • D e‖ ≤ r*p.threshold:=by
        rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg t0]
        exact mul_le_mul ht.2 (dcap e) (norm_nonneg _) rp.le
      simpa only [P,increment,Pi.one_apply,Pi.smul_apply,inv_one,mul_one] using
        ((clear.small (t • D e) (d.trans openBall)).2.trans (mul_le_mul_of_nonneg_left d J0))
    apply Finset.disjoint_left.mpr
    intro x _ flag
    obtain ⟨z,_,bad⟩:=(flags_spec _ _ x).mp flag
    have ps:=WilsonRegisteredAffineForest.plaquette (1:Config G n) P cost z
    have finish:4*(J.C*(r*p.threshold)) ≤ p.threshold:=by
      calc _ = (4*J.C*r)*p.threshold:=by ring
           _ ≤ 1*p.threshold:=mul_le_mul_of_nonneg_right stay p.threshold_pos.le
           _=_:=one_mul _
    have flat:faceValue (1:Config G n) z=1:=by simp [faceValue,square]
    rw [flat,G.chord_one,zero_add] at ps
    exact (not_lt_of_ge (ps.trans finish)) bad
  · intro Y F good here
    have endpt:increment (1:Config G n) (r • D)=W:=by
      funext e
      have ends:r • (r⁻¹ • X e)=X e:=by rw [smul_smul,mul_inv_cancel₀ rp.ne',one_smul]
      simpa only [increment,Pi.smul_apply,D,Pi.one_apply,mul_one,ends] using (backed e).1
    rw [endpt,←good.symmetry (WilsonAxialWindow.frame a o U) U]
    apply good.sites
    intro e tail _
    change U' e=W e
    exact (if_pos (here e.1 tail)).symm

theorem projected {d:ℕ} (A:Hol G) {p:BudgetPoint} {o:Site n} {Y:Support n} {F:Config G n → ℂ}
    (good:p.Regular Y F) {c:ℝ} (income:p.supBounds o Y F c) (zero:A.PiVanish d o F)
    {r:ℝ} (rp:0<r) (D:Directions G n) (admitted:p.dirBound o D)
    (healthy:∀t∈Set.Icc (0:ℝ) r,Healthy p.threshold Y (increment 1 (t • D))):
    ‖F (increment 1 (r • D))‖ ≤ r*c := by
  have spent:=WilsonRegisteredAffineTaylor.original good income (1:Config G n) D admitted rp healthy 0 ((by decide : 0+1≤6).trans p.order_ge)
  simpa [WilsonRegisteredAffineTaylor.jet,leftDerivs,constant A zero,mul_comm] using spent

theorem based {p:BudgetPoint} (J:Voice G) (clear:Clear G J) (a:Lattice.Order) (o:Site n) (H:ℕ)
    (room:2*H<n.val) (τ r:ℝ) (weak:0 ≤ τ) (rp:0<r) (U:Config G n)
    (cut:U∈House.chilly (WilsonAxialWindow.cells o H) τ):
    let c:=(4*(H:ℝ)*Fintype.card PlaqAxes)*τ
    c ≤ J.δ → J.C*c ≤ r*p.threshold → r*p.threshold ≤ J.r → 4*J.C*r ≤ 1 → 
    ∃D:Directions G n,p.dirBound o D ∧
      (∀t∈Set.Icc 0 r,∀Y:Support n,Healthy p.threshold Y (increment 1 (t • D))) ∧
      ∀{Y:Support n} {F:Config G n → ℂ},p.Regular Y F → 
      (∀x∈Y,separation o x<H) → F U=F (increment 1 (r • D)) := by
  intro c small cash openBall stay
  obtain ⟨D,_,budget,healthy,same⟩ :=
    bounded (p:=p) J clear a o H room τ r weak rp U cut small cash openBall stay
  exact ⟨D,budget,healthy,same⟩

end YM.Integration.WilsonRegisteredFlatLocal
end

