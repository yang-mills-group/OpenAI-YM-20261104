import YM.Integration.WilsonOriginalSuspendedFootprint

/-! All ordered thermal and angular derivatives of the authentic suspended Wilson group at zero. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalSuspendedTensor
open Function Finset Lattice RG Wilson Marker QuadraticLocal QuadraticLocal.Earn Stationary
open WilsonOriginalSuspendedWord WilsonOriginalSuspendedFootprint WilsonEmittedRootedJetWage
open WilsonOriginalResidentAngles WilsonOriginalCenteredSeamSalary
open scoped Classical BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge} {n:Side} {V X:Type} [DecidableEq V] {o:Passport n V} {J:Census V}

abbrev Positions (G:Gauge) (n:Side) (r:ℕ):= Fin r→Slot G n

def paid (T:Row o J G X) (s:Finset V) (x:X) (j r:ℕ) (z:Positions G n r) (b:ℝ) : ℝ :=
  Real.exp (b * radius T.center (targets o s (trace z))) * ‖WilsonOriginalSuspendedFootprint.at T x j r z‖

def fee (G:Gauge) (b:ℝ) (r:ℕ) : ℝ :=
  fare (b/2) (Fintype.card (Loc G 1)+1) r * price G b r

theorem nonnegative (G:Gauge) {b:ℝ} (hb:0<b) (r:ℕ):0≤fee G b r:=by
  unfold fee
  apply mul_nonneg (WilsonOriginalResidentAngles.nonneg _ (half_pos hb) _ _)
  exact WilsonOriginalSuspendedWord.nonnegative _

theorem original (T:Row o J G X) (s:Finset V) (present:s⊆T.mode.val) (t:X)
    {σ:ℝ} (hs:0<σ) (proof:T.Budget) (word:T.Graceful σ)
    (j r:ℕ) :
    (∑z:Positions G n r,paid T s t j r z (σ/2))≤fee G σ r*T.height σ:=by
  let S:=univ.image (visit (r:=r) T)
  have crop:(∑z:Positions G n r,paid T s t j r z (σ/2))=
      ∑z∈S,paid T s t j r z (σ/2):=by
    apply (Finset.sum_subset (Finset.subset_univ S) ?_).symm
    intro z _ off
    have outside:∃i y,z i=some y ∧ y.1∉T.atom.footprint T.center:=by
      by_contra! strip
      apply off
      have one (i:Fin r):∃a:Option ((T.atom.footprint T.center)×Loc G 1),
          a.map (fun q=>(q.1.val,q.2))=z i:=by
        cases eq:z i with
        | none => exact ⟨none,rfl⟩
        | some y => exact ⟨some (⟨y.1,strip i y eq⟩,y.2),rfl⟩
      choose a ha using one
      exact mem_image.mpr ⟨a,mem_univ _,funext ha⟩
    obtain ⟨i,y,hy,hi⟩:=outside
    simp only [paid,away T t j r z i y hy hi,norm_zero,mul_zero]
  rw [crop]
  change (∑z∈univ.image (visit (r:=r) T),paid T s t j r z (σ/2))≤_
  rw [Finset.sum_image (fun a _ b _ e=>unique T r e)]
  let E:=Real.exp (σ/2*T.length)
  have each (a:Chairs T r):paid T s t j r (visit T a) (σ/2) ≤ E*(T.salary*price G σ r):=by
    have geo:=geometry T s (trace (visit T a)) present (authentic T a)
    exact mul_le_mul (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr geo) (half_pos hs).le))
      (WilsonOriginalSuspendedWord.paid T t j r _ hs proof word) (norm_nonneg _) (Real.exp_pos _).le
  have cnt:=WilsonOriginalSuspendedFootprint.volume T r (σ/2) (half_pos hs)
  calc
    _ ≤ ∑ _a:Chairs T r,E*(T.salary*price G σ r):=sum_le_sum fun a _=>each a
    _ = (Fintype.card (Chairs T r):ℝ)*(E*(T.salary*price G σ r)):=by simp
    _ ≤ (fare (σ/2) (Fintype.card (Loc G 1)+1) r * E)*(E*(T.salary*price G σ r)):=by
      apply mul_le_mul_of_nonneg_right cnt
      exact mul_nonneg (Real.exp_pos _).le (mul_nonneg T.sound.le
        (WilsonOriginalSuspendedWord.nonnegative r))
    _ = _ := by
      have join:E*E=Real.exp (σ*T.length):=by
        rw [←Real.exp_add];congr 1;ring
      unfold fee Row.height
      calc
        _ = fare (σ/2) (Fintype.card (Loc G 1)+1) r*price G σ r*T.salary*(E*E):=by ring
        _ = _:=by rw [join];ring

end YM.Integration.WilsonOriginalSuspendedTensor
