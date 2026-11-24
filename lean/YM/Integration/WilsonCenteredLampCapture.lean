import YM.Integration.WilsonCenteredMountedCapture
import YM.Integration.WilsonCenteredCaptureRegularAtoms
import YM.Integration.WilsonCenteredCaptureLampRoster

/-! Centered capture of signed products of the genuine deposited Wilson
lamps, with the test and each constituent's position retained. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCenteredLampCapture
open Finset Function RG Lattice Wilson Source Labels Marker Ac QuadraticLocal Push.Local Next.Foundations
open Planned.GuardedAtom WilsonCenteredCaptureRegularAtoms WilsonCenteredMountedCapture
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} {ι V X μ J : Type} [DecidableEq V] {R : Census V}
    {o : V → Site n} {P : Rep G n} {d : ℕ} {F : Labels.Frame G d}

def docket (ι : Type) [Countable ι] : ι ↪ ℕ := by
  letI := Classical.choice (nonempty_encodable ι)
  exact ⟨Encodable.encode,Encodable.encode_injective⟩

def stage (p : BudgetPoint) (rad : ℕ) (s : Finset J) :=
    (((s.card+1:ℕ) : ℝ)*(1+(rad:ℝ))^p.power)^p.order

lemma funded (p : BudgetPoint) (rad : ℕ) (s : Finset J) : 1 ≤ stage p rad s := by
  apply one_le_pow₀
  apply one_le_mul_of_one_le_of_one_le
  · exact_mod_cast Nat.succ_le_succ (Nat.zero_le s.card)
  apply one_le_pow₀
  exact le_add_of_nonneg_right (Nat.cast_nonneg _)

theorem counted [Countable ι] (L : Lamps X μ G P.p o R) (x : X)
    (y : Site n) (Z : Support n) (hold : y∈Z)
    (rows : ι→Finset J) (sites : ι→J→μ) (seats : ι→J→Site n) (rad : ℕ)
    (near : ∀ i, ∀ j∈rows i,separation (seats i j) y≤rad)
    (gain : ι→ℂ) (e : ι→μ→ℝ) (rate : ∀ i, ∀ j∈rows i,
      P.p.supBounds (seats i j) (L.ground (sites i j)) (L.nominal x (sites i j)) (e i (sites i j)))
    {a b v κ w σ C Λ δ : ℝ}
    (cash : SumBudget (fun i=>reservedMass P.p (domain L (rows i) (sites i) Z)
      (‖gain i‖*(stage P.p rad (rows i)*∏ j∈rows i,e i (sites i j)))) a)
    (K : Guard.Keeper P.p P.activities) (law : P.Lawful σ C Λ δ v) (div : 0<κ)
    (hv : 0≤v) (room : hitWidth P.p*v≤1)
    (S : SectionData F) (Y : Hol G) (read : Readable Y S P.p n w) (seed : F.Coeff)
    (hard : ℕ→ Config G n→ℂ) (bank : ForceFormat P.p P.activities y hard)
    (force : ForceCost P.p P.activities hard (κ*b)) :
    let D := factor Y S P.p.supportExponent w
    ∃ Q : Coefficient F n,Q.Format y Y P ∧
      Tab Q y P κ (D*a) ((b+(hitWidth P.p*v/κ)*a)+(hitWidth P.p*v/κ)*(D*a)) ∧
      ∀ U,Q.density y S P U = (P.eval U:ℂ)*
        (Push.Local.primary S y P.p.threshold seed U+
          ∑' i,gain i*∏ j∈rows i,L.light x (sites i j) U)+
        (Real.exp (P.exponent U):ℂ)*∑' C,gasMark P.p P.activities U C hard := by
  intro D
  let T i := domain L (rows i) (sites i) Z
  let m i := nominal L (rows i) (sites i) x
  let h i := rebate L (rows i) (sites i) x Z
  let f i := gain i • m i
  let slip i := gain i • h i
  let cap i := ‖gain i‖*(stage P.p rad (rows i)*∏ j∈rows i,e i (sites i j))
  have lamp i := WilsonCenteredCaptureRegularAtoms.original L (rows i) (sites i) x Z y (seats i) rad (near i) (e i) (rate i)
  have roots i : y∈T i := mem_union_left _ hold
  have goods i : P.p.Regular (T i) (f i) := regular_smul _ (lamp i).1
  have costs i : P.p.supBounds y (T i) (f i) (cap i) := bound_smul _ (lamp i).2.1
  have attaches i : Push.Local.Attaches P.p.threshold (T i) (slip i) := by
    obtain ⟨loc,sym,meas,van⟩ := (lamp i).2.2.1
    exact ⟨fun U V hUV flags=>congrArg (fun q : ℂ=>gain i*q) (loc U V hUV flags),
      fun k U=>congrArg (fun q : ℂ=>gain i*q) (sym k U),
      measurable_const.mul meas,fun U hU=>(congrArg (fun q : ℂ=>gain i*q) (van U hU)).trans (mul_zero _)⟩
  have bounds i U : ‖slip i U‖≤cap i := by
    have pos := prod_nonneg (s:=rows i) fun j hj=>(rate i j hj).1
    change ‖gain i*h i U‖≤_
    rw [norm_mul];apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact ((lamp i).2.2.2 U).trans (le_mul_of_one_le_left pos (funded P.p rad (rows i)))
  have sumCap : Summable cap := by
    refine Summable.of_nonneg_of_le (fun i=>(costs i).1) (fun i=>?_) cash.2.1
    change cap i≤Real.exp ((P.p.supportExponent+2)*coverNumber P.p.B (T i))*cap i
    apply le_mul_of_one_le_left (costs i).1 (Real.one_le_exp_iff.mpr _)
    have := P.p.exponent_pos; positivity
  have hm U : Summable fun i=>masked P.p.threshold (T i) (f i) U :=
    Summable.of_norm_bounded sumCap fun i=>by
      by_cases good : Healthy P.p.threshold (T i) U
      · rw [masked_eq _ _ _ _ good];exact (costs i).2 U good [] (Nat.zero_le _) (by simp)
      rw [masked_ne _ _ _ _ good,norm_zero];exact (costs i).1
  have he U : Summable fun i=>slip i U := Summable.of_norm_bounded sumCap (fun i=>bounds i U)
  obtain ⟨Q,fit,tab,val,-⟩:=WilsonCenteredMountedCapture.original y T (docket ι) K
    (docket (ι×Finset ℕ)) seed f slip hard S Y law read div hv room roots goods cap cash costs attaches bounds bank force hm he
  refine ⟨Q,fit,tab,fun U=>?_⟩
  rw [val]
  congr 2
  congr 1
  apply tsum_congr
  intro i
  change masked P.p.threshold (T i) (gain i • m i) U+gain i*h i U=_
  have restored := congrFun (posted L (rows i) (sites i) x Z) U
  change (∏ j∈rows i,L.light x (sites i j) U) = masked P.p.threshold (T i) (m i) U + h i U at restored
  rw [restored,mul_add]
  by_cases good : Healthy P.p.threshold (T i) U
  · simp [masked,good]
  simp [masked,good]

end YM.Integration.WilsonCenteredLampCapture
