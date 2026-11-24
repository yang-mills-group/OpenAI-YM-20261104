import YM.Integration.WilsonOriginalRadialDerivativeCalendar

/-! Read every derivative through the probe horizon on one genuine radial grid. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalRadialCommonGrid
open Function Finset Filter Set MeasureTheory Labels Lattice Wilson RG Source Marker
open Multi Stationary Comparison.RG02 Planned.AtomRegular RG01.Kernel.Wheel WardBin.Lies
open Next.Foundations PhysicalNext.Repeat.Legato Pert.Asymptotics Push.Local
open WilsonOriginalJointTrialHearing WilsonCapturedPrimaryAngles WilsonCapturedPrimaryPaid
open WilsonFirstReceivedRadialStencil WilsonOriginalPhysicalRadialDerivative
open scoped Classical Topology ContDiff
variable {G:Gauge}(R:Run G)
local notation "H" => R.family.path
local notation "A" => R.family.params

def target (d P:ℕ):ℕ:=P+2*d+1
def ratio (k D:ℕ):ℝ:=((k+1:ℕ):ℝ)/(D+1:ℕ)
private theorem ratio_pos (k D:ℕ):0<ratio k D:=by unfold ratio;positivity
private theorem ratio_one {k D:ℕ}(le:k≤D):ratio k D≤1:=by
  apply (div_le_one₀ (by positivity)).2
  exact_mod_cast Nat.succ_le_succ le
private theorem same (k D j:ℕ)(t:ℝ):(t*ratio k D)*node k j=t*node D j:=by
  unfold ratio node
  field_simp

/-- The same purchased radial array serves every k≤d. All derivative debits are
charged against its actual transported whole face. -/
theorem original (simple:G.Simple)(d P:ℕ)(F:Labels.Frame G d):
    ∀ᶠ i:ℕ in atTop,∀k≤d,∀a∈tests F,∀ {N per K D:ℕ} (_live:K≤N)(past:i<K),
      d≤D → 1≤((H).levels.budget i).supportExponent →
      ∀{V:Type}[DecidableEq V]{J:Census V}
       (Z:Config G (R.family.side K per)→Poly J),Integrable Z (prior G _) →
       ∀(s:J.Mode)(M:ℝ),0≤M → (∀U,‖face R (N:=N) Z s U‖≤M) → ∀(values:ℕ→ℂ)(E:ℝ),
       (∀j≤D,‖read R N per (WilsonCapturedPrimaryWeakTrialRadial.field R d N per i (target d P) D a j)
           past.le Z s-values j‖≤E) →
       let g:=regulatorRun R.family N per (i+1)
       let B:=(H).levels.budget i
       let r:=radiusAt R (N:=N) (per:=per) (i:=i) d (target d P)
       let t:=g^gap (target d P) 1*ratio k D
       let f:ℝ→ℂ:=fun x=>read R N per (WilsonCapturedPrimaryRays.field A B 0 r a x) past.le Z s
       ‖iteratedDeriv k f 0-WilsonOriginalRadialFiniteDifference.divided k t values‖≤
         WilsonCapturedPrimarySamples.price k*(E/t^k+WilsonOriginalRadialSpringTariff.factor H A a (k+1)*M*g^P):=by
  have all:∀ᶠ i:ℕ in atTop,∀k∈range (d+1),∀a∈tests F,∀{N per:ℕ}(_live:i<N),
      let b:=(H).levels.budget i
      let g:=regulatorRun R.family N per (i+1)
      let r:=radiusAt R (N:=N) (per:=per) (i:=i) d (target d P)
      1≤b.supportExponent → 0<g ∧ g≤1 ∧ g^gap (target d P) 1*wallet A a r≤1 ∧
      b.threshold*(1+(r:ℝ))^2≤1 ∧ ∀(M:ℝ),0≤M →
        WilsonOriginalRadialSpringRemainder.bill H (N:=N) (p:=per) (i:=i) A b 0 r a (k+1) M*g^(2*(k+1)+1)
          ≤WilsonOriginalRadialSpringTariff.factor H A a (k+1)*M:=
    (Filter.eventually_all_finset (range (d+1))).2 (fun k _=>WilsonOriginalRadialDerivativeCalendar.panel
        R simple F (target d P) (k+1))
  filter_upwards [all] with i funded
  intro k dk a ha N per K D live past dD width V de J Z enrolled s M mp gross values E heard g B r t f
  have sold:=funded k (mem_range.mpr (Nat.lt_succ_of_le dk)) a ha (N:=N) (per:=per) (past.trans_le live) width
  have gp:0<g:=sold.1
  have gc:g≤1:=sold.2.1
  have base:g^gap (target d P) 1≤1:=pow_le_one₀ gp.le gc
  have tp:0<t:=mul_pos (pow_pos gp _) (ratio_pos k D)
  have ts:t≤g^gap (target d P) 1:=mul_le_of_le_one_right (pow_nonneg gp.le _) (ratio_one (dk.trans dD))
  have wpos:0≤wallet A a r:=zero_le_one.trans (wallet_one ..)
  have short:t*wallet A a r≤1:=(mul_le_mul_of_nonneg_right ts wpos).trans sold.2.2.1
  let F':=actualTransport R.family (N:=N) (face R (N:=N) Z s) past
  obtain ⟨source,eqn⟩:=received R live past Z enrolled s gross
  let fee:=WilsonOriginalRadialSpringRemainder.bill H (N:=N) (p:=per) (i:=i) A B 0 r a (k+1) M
  have posFee:0≤fee:=by
    let T:=WilsonOriginalRadialSpringRemainder.total H (N:=N) (p:=per) (i:=i)
      (WilsonCapturedPrimaryRough.quadratic B) 0 (active 0 r) (k+1) M
    have posT:0≤T:=sum_nonneg fun _ _=>abs_nonneg _
    change 0≤(WilsonCapturedPrimaryRough.price G (k+1) (wallet A a r))*T
    unfold WilsonCapturedPrimaryRough.price
    exact mul_nonneg (mul_nonneg (patterns_nonneg _) (mul_nonneg (baseCost_nonneg ..) (pow_nonneg wpos _))) posT
  have gridE:∀j≤k,‖WilsonOriginalRadialSpringRemainder.curve H (N:=N) A B 0 r a (fun _=>F') (t*node k j)-values j‖≤E:=by
    intro j hj
    have nodeSame:WilsonCapturedPrimaryWeakTrialRadial.field R d N per i (target d P) D a j=
        WilsonCapturedPrimaryRays.field A B 0 r a (t*node k j):=by
      unfold WilsonCapturedPrimaryWeakTrialRadial.field WilsonCapturedPrimaryPotential.lifted
      rw [WilsonCapturedPrimaryPotential.sampled gp,WilsonCapturedPrimaryAngles.physical]
      dsimp only [t];rw [same];rfl
    have h:=heard j (hj.trans (dk.trans dD))
    rw [nodeSame] at h
    change ‖RG01.Kernel.conditional H N i per _ (fun _=>F')-values j‖≤E
    rw [←congrFun eqn _];exact h
  have raw:=WilsonOriginalRadialFiniteDifference.original H R.makes.wilson (past.trans_le live)
    (fun _=>F') source mp A B 0 r a k dk tp (ts.trans base) short sold.2.2.2.1 values gridE
  have fEq:f=WilsonOriginalRadialSpringRemainder.curve H (N:=N) A B 0 r a (fun _=>F'):=by
    funext x;exact congrFun eqn _
  rw [fEq]
  refine raw.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) (WilsonCapturedPrimarySamples.price_nonneg _))
  change fee*t≤_
  calc _ ≤ fee*g^(2*(k+1)+1+P):=by
              apply mul_le_mul_of_nonneg_left (ts.trans (pow_le_pow_of_le_one gp.le gc ?_)) posFee
              unfold target gap;omega
       _ ≤ _:=by rw [pow_add,←mul_assoc]
                 exact mul_le_mul_of_nonneg_right (sold.2.2.2.2 M mp) (pow_nonneg gp.le _)

end YM.Integration.WilsonOriginalRadialCommonGrid
