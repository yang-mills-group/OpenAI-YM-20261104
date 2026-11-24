import YM.Integration.WilsonCenteredAbsoluteHard

/-! File the entire occupied hard contribution in the actual original
one-source coefficient with a single physical hard divisor. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCenteredHardFiled
open Finset RG Lattice Wilson Marker QuadraticLocal Ac Planned.GuardedAtom Push.Local Source Labels Extra.Histories
open WilsonCenteredHardMount WilsonCenteredHardAnswers WilsonCenteredAbsoluteHard WilsonCenteredFiledAtoms
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} {P : Rep G n} {d : ℕ} {F : Frame G d}

theorem source (S : SectionData F) (Y : Hol G) (y : Site n) {κ E : ℝ} (hk : 0<κ)
    (f : ℕ→ Config G n→ℂ) (fit : ForceFormat P.p P.activities y f) (due : ForceCost P.p P.activities f E) :
    Store P S Y y κ (E/κ) (fun U=>(Real.exp (P.exponent U):ℂ)*read (P:=P) f U) := by
  let Q : Coefficient F n := ⟨0,fun _=>{y},0,f⟩
  have main : (Extra.Histories.primary y (0:F.Coeff)).Format y Y P := Extra.Histories.primary_format _
  obtain ⟨e,price,caps⟩:=due
  have pos : 0≤E := (tsum_nonneg price.1).trans price.2.2
  refine ⟨Q,⟨main.smooth,main.origin,main.identity_null,main.projects,fit.forcing,fit.carried,fit.invariant,fit.supported,fit.borel⟩,?_,?_⟩
  · obtain ⟨a,b,ha,hb,bound,_,smooth,_⟩ := Extra.Histories.primary_rem (o:=y) (R:=P) (0:F.Coeff) hk
    have az : a=0 := by linarith
    subst a
    refine ⟨0,E/κ,le_rfl,div_nonneg pos hk.le,(zero_add _).le,hk,smooth,e,?_,caps⟩
    simpa only [mul_div_cancel₀ _ hk.ne'] using price
  intro U
  have off (j : ℕ) : Q.maskedTerm P j U=0 := by
    by_cases clear : Healthy P.p.threshold {y} U <;> simp [Q,Coefficient.maskedTerm,masked,clear]
  have z : Q.exponentialEntry y S P U=0 := by
    change (Extra.Histories.part S y P U) (0:F.Coeff)+(∑' j,Q.maskedTerm P j U)=0
    simp [off]
  rw [Coefficient.density,z,mul_zero,zero_add]
  apply congrArg ((Real.exp (P.exponent U):ℂ)*·)
  apply tsum_congr
  intro F;rw [gasMark_eq];rfl

variable {V X : Type} [DecidableEq V] [Fintype V] {R : Census V} {o : V→Site n}

theorem original (H : Hard X P.p P.activities.forced P.activities.K o R) (w : V→ℝ) (hw : ∀ i,0<w i)
    {κ v σ C Λ δ : ℝ} (wallet : H.Paid w P.p.B P.p.supportExponent κ)
    (hk : 0<κ) (hv : 0≤v) (room : hitWidth P.p*v≤1) (width : 0≤P.p.supportExponent)
    (law : P.Lawful σ C Λ δ v) (K : Guard.Keeper P.p P.activities) (Z : Support n)
    (y : Site n) (center : y∈Z) (S : SectionData F) (Y : Hol G) (x : X)
    (a b c : V) (M : R.Mode) (apart : a≠b) (pair : M.val={a,b}) (za : o a∈Z) (zb : o b∈Z) (zc : o c∈Z)
    (u : ℕ×Finset ℕ ↪ ℕ) (l : (ℕ×ℕ)×Finset ℕ ↪ ℕ) :
    Store P S Y y κ
      ((bill P.p Z v ((Poly.toll w M)⁻¹*κ))/κ+(bill P.p Z v ((Poly.toll w (R.fire c))⁻¹*κ))/κ+
        (bill P.p Z v (((w a)⁻¹*κ)*((w b)⁻¹*κ)))/κ)
      (fun U=>(Real.exp (P.exponent U):ℂ)*((gas H x U).part M-(gas H x U).part (R.fire c))) := by
  have hx : a∈M.val := by rw [pair];simp
  have hab:=WilsonCenteredHardMount.single H w hw wallet law.labels.boundK hv room K law.labels.forced Z y center M a hx za x u
  have hc:=WilsonCenteredHardMount.single H w hw wallet law.labels.boundK hv room K law.labels.forced Z y center (R.fire c) c (mem_singleton_self _) zc x u
  have hb:=WilsonCenteredHardMount.twice H w hw wallet law.labels.boundK hv room K law.labels.forced Z y center a b za zb x l
  have sAB:=source S Y y hk _ hab.1 hab.2
  have sC:=source S Y y hk _ hc.1 hc.2
  have sb:=source S Y y hk _ hb.1 hb.2
  have issued:=WilsonCenteredFiledAtoms.add law hk (WilsonCenteredFiledAtoms.sub law sAB sC) sb
  convert issued using 1
  funext U
  have raw:=WilsonCenteredAbsoluteHard.physical H K Z u l x U a b c M apart pair law.labels.boundK
    (Hard.packet_summing _ wallet width hw x U) hab.2 hc.2 hb.2
  rw [raw,mul_add,mul_sub]
  rfl

end YM.Integration.WilsonCenteredHardFiled
