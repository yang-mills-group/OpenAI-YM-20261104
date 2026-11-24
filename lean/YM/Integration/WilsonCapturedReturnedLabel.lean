import YM.Integration.WilsonCapturedFactoryReturn
import YM.Integration.WilsonCapturedFactoryCocycle

/-! Exact inverse of the real periodic germ matrix, the single bare
factory label it determines, and its genuine density at each capture.
An admitted fixed coarse reference can remain identical for all
subexponential price demands. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCapturedReturnedLabel
open Filter Real Lattice Wilson RG Source Labels PhysicalNext.Repeat.Legato
open Trace.Physical Trace.Physical.GermGraph Work.G08
open scoped Classical Topology BigOperators
variable {G : Gauge}

/-- Composition of the actual nonlinear Wilson transfer of a marked
density, in the exact convention of the physical factory. -/
def down (R : Run G) (d N p u : ℕ) : (s : ℕ) →
    (Config G (R.family.side (u+s) p) → ℂ) → (Config G (R.family.side u p) → ℂ)
  | 0, f => f
  | s+1, f => down R d N p u s (transition (C:=R.family) d N p (u+s) f)

theorem carried (R : Run G) (d N p u s : ℕ) (admit : R.family.ref d ≤ u)
    (stop : u+s ≤ N) (x : R.family.label d) :
    down R d N p u s (calValues (C:=R.family) d N p (u+s) x) =
      calValues (C:=R.family) d N p u x := by
  induction s with
  | zero => rfl
  | succ s ih =>
    have iN : u+s < N := stop
    have ref : R.family.ref d ≤ u+s := admit.trans (Nat.le_add_right u s)
    change down R d N p u s
      (transition (C:=R.family) d N p (u+s) (calValues (C:=R.family) d N p ((u+s)+1) x)) = _
    exact (congrArg (down R d N p u s) (factory_eq d N p (u+s) R.makes ref iN x).symm).trans
      (ih iN.le)

/-- In measured coordinates this is a genuine linear equivalence on
the full original label space, at this cutoff and period. -/
def inverseString (R : Run G) (d N p u b : ℕ) (atU : Opened R.family d u p)
    (atB : Opened R.family d b p) (uN : u ≤ N) (bN : b ≤ N) :
    R.family.label d ≃ₗ[ℂ] R.family.label d :=
  (fitting d N p u R.makes atU uN).symm.trans (fitting d N p b R.makes atB bN)

/-- The same exact datum, with any intermediate campaign reference,
has no extra label recalibration on the split. -/
theorem compose (R : Run G) (d N p u j b : ℕ) (au : Opened R.family d u p)
    (aj : Opened R.family d j p) (ab : Opened R.family d b p)
    (uN : u ≤ N) (jN : j ≤ N) (bN : b ≤ N) (x : R.family.label d) :
    inverseString R d N p j b aj ab jN bN (inverseString R d N p u j au aj uN jN x) =
      inverseString R d N p u b au ab uN bN x := by
  let fu := fitting d N p u R.makes au uN
  let fj := fitting d N p j R.makes aj jN
  let fb := fitting d N p b R.makes ab bN
  change fb (fj.symm (fj (fu.symm x))) = fb (fu.symm x)
  exact congrArg (fun a => fb a) (fj.symm_apply_apply (fu.symm x))

/-- The reference, all campaign labels, and the single inverse vector
are independent of the requested asymptotic loss. Uniform g-dependent
short-window bounds use a separate theorem. This statement concerns
only the physical, fixed reference below the original capture b. -/
theorem purchased (R : Run G) (hG : G.Simple) (d : ℕ) :
    ∃ U : ℕ, ∃ M : ℝ → ℝ, (∀ γ > 0, 1 ≤ M γ) ∧
      ∀ u ≥ U, ∀ N p, u ≤ N → ∀ c : R.family.label d, ∃ x : R.family.label d,
        page (C:=R.family) d p u ((R.family.factory d N p).entries u x) = c ∧
        (∀ y : R.family.label d,
          page (C:=R.family) d p u ((R.family.factory d N p).entries u y) = c → y=x) ∧
        ∀ b ≥ u, ∀ hN : b ≤ N, ∃ ob : Opened R.family d b p, ∀ γ > 0,
          let price := M γ*(exp (γ*(R.family.S.scale b-R.family.S.scale u))*
            (R.family.labels.level d).coeffSize c)
          (R.family.labels.level d).coeffSize ((fitting d N p b R.makes ob hN) x) ≤ price ∧
          reads (C:=R.family) d N p b ((R.family.factory d N p).entries b x)
            (2*stock R.family b*price) := by
  obtain ⟨U,opened,pricing⟩ := WilsonCapturedFactoryReturn.coordinates R hG d
  let M := fun γ : ℝ => if g : 0 < γ then (pricing γ g).choose else 1
  refine ⟨U,M,fun γ g => ?_,?_⟩
  · simpa only [M,dif_pos g] using (pricing γ g).choose_spec.1
  intro u Uu N p uN c
  let fu := fitting d N p u R.makes (opened u Uu p) uN
  let x := fu.symm c
  have lower : fu x=c := fu.apply_symm_apply c
  have matchU : page (C:=R.family) d p u ((R.family.factory d N p).entries u x)=c := lower
  refine ⟨x,matchU,?_,?_⟩
  · intro y hy
    exact fu.injective (hy.trans matchU.symm)
  intro b ub bN
  let ob := opened b (Uu.trans ub) p
  refine ⟨ob,?_⟩
  intro γ g price
  have bound := (pricing γ g).choose_spec.2 u Uu N p b ub bN x
  change (R.family.labels.level d).coeffSize ((fitting d N p b R.makes ob bN) x) ≤
    (pricing γ g).choose*(exp (γ*(R.family.S.scale b-R.family.S.scale u))*
      (R.family.labels.level d).coeffSize (fu x)) at bound
  rw [lower] at bound
  have target : (R.family.labels.level d).coeffSize ((fitting d N p b R.makes ob bN) x) ≤ price := by
    simpa only [price,M,dif_pos g] using bound
  have native := graph_cost d N p b R.makes ob bN x
  refine ⟨target,native.1,rem_increase d native.2 (mul_le_mul_of_nonneg_left target ?_)⟩
  exact mul_nonneg zero_le_two (zero_le_one.trans (stage R.family b).columns_ge)

end YM.Integration.WilsonCapturedReturnedLabel
end
