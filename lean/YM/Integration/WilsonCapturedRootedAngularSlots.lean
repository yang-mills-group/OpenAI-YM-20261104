import YM.Integration.WilsonOriginalPinnedFieldWage
import YM.Integration.WilsonOriginalPinnedGradedPeek

/-! Price the positive angular ranks of the actual homogeneous thermal read.
Each injected angular list has the same occupied sites as the mixed list
with thermal directions in the unused slots. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonCapturedRootedAngularSlots
open Function Finset Lattice RG Stationary Comparison.RG02
open WilsonOriginalLinkedAngularPage WilsonOriginalOccupiedAngularPage
open WilsonEmittedRootedJetWage WilsonOriginalJointDeckMotion
open WilsonOriginalSuspendedFootprint WilsonOriginalCenteredSeamSalary
open scoped Classical BigOperators ContDiff
variable {G:Gauge} {n:Side}
local notation "I" => Site n × Loc G 1
local notation "E" => Link G n
local notation "J" => Joint G n

def thermal (F:J→ℂ) (k:ℕ) (A:E) : ℂ := Assembly.jet F k (1,edgeColor A)

def occupy {X:Type} {k r:ℕ} (u:Fin r ↪ Fin k) (x:Fin r→X) (i:Fin k) : Option X :=
  if h : i∈Set.range u then some (x (u.toEquivRange.symm ⟨i,h⟩)) else none

theorem marked {X:Type} {k r:ℕ} (u:Fin r ↪ Fin k) (x:Fin r→X) (j:Fin r):
    occupy u x (u j)=some (x j):=by simp [occupy]

def lifted {X:Type} {k r:ℕ} (u:Fin r ↪ Fin k) : (Fin r→X) ↪ (Fin k→Option X) where
  toFun:=occupy u
  inj':=by intro f g eq;funext j;simpa only [marked,Option.some.injEq] using congrFun eq (u j)

def sites {r:ℕ} (x:Fin r→I) : Finset (Site n):=univ.image (fun i=>(x i).1)

theorem traced {k r:ℕ} (u:Fin r ↪ Fin k) (x:Fin r→I) : trace (occupy u x)=sites x:=by
  ext a
  constructor
  · intro h
    obtain ⟨i,_,hi⟩:=mem_biUnion.mp h
    by_cases mem:i∈Set.range u
    · obtain ⟨j,rfl⟩:=mem
      rw [marked] at hi
      exact mem_image.mpr ⟨j,mem_univ _,(mem_singleton.mp hi).symm⟩
    · simp [occupy,mem] at hi
  · intro h
    obtain ⟨j,_,rfl⟩:=mem_image.mp h
    exact mem_biUnion.mpr ⟨u j,mem_univ _,by simp [marked]⟩

theorem angular (F:J→ℂ) (k r:ℕ) (x:Fin r→I) :
    coefficient r (thermal F k) x=(k.factorial:ℝ)⁻¹ • ∑ u:Fin r ↪ Fin k,entry k F (occupy u x):=by
  let T:=iteratedFDeriv ℝ k F 0
  let group:= (0:E →L[ℝ] ℝ).prod ((edgeColor (G:=G) (n:=n)).toContinuousLinearMap)
  let P:E→L[ℝ](Fin k→J):=ContinuousLinearMap.pi (fun _=>group)
  let t:Fin k→J:=fun _=>peg G n none
  let H: (Fin k→J)→ℂ:=fun z=>T (t+z)
  have chosen:thermal F k=(k.factorial:ℝ)⁻¹ • (H ∘ P):=by
    funext x
    change (k.factorial:ℝ)⁻¹ • T (fun _=>(1,edgeColor x))=(k.factorial:ℝ)⁻¹ • T (fun _=>(1,0)+(0,edgeColor x))
    simp
  have use:ContDiff ℝ r H:=T.contDiff.comp (contDiff_const.add contDiff_id)
  rw [chosen]
  unfold coefficient WilsonOriginalPolarizedAngularPage.entries
  rw [iteratedFDeriv_const_smul_apply (use.comp P.contDiff).contDiffAt,
    smul_apply,P.iteratedFDeriv_comp_right use _ (le_refl _),map_zero,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  change (k.factorial:ℝ)⁻¹ • iteratedFDeriv ℝ r (fun z=>T (t+z)) 0 _=_
  rw [iteratedFDeriv_comp_add_left,add_zero,T.iteratedFDeriv_eq]
  simp only [ContinuousMultilinearMap.iteratedFDeriv,_root_.sum_apply,
    ContinuousMultilinearMap.iteratedFDerivComponent_apply,Pi.compRightL_apply]
  apply congrArg ((k.factorial:ℝ)⁻¹ • ·)
  apply sum_congr rfl
  intro u _
  change T _=T _
  apply congrArg T
  funext i
  by_cases h:i∈Set.range u
  · obtain ⟨j,rfl⟩:=h
    simp [marked,P,group,peg]
  · simp [h,occupy,t]

theorem income (F:J→ℂ) (k r:ℕ) (z:Site n) (ρ c cash:ℝ) (weight:0 ≤ c)
    (paid:(∑a:Fin k→Slot G n,c*Real.exp (ρ*(radius z (trace a):ℝ))*‖entry k F a‖) ≤ cash):
    (∑x:Fin r→I,c*Real.exp (ρ*(radius z (sites x):ℝ))*‖coefficient r (thermal F k) x‖) ≤
      (k.factorial:ℝ)⁻¹*(Fintype.card (Fin r ↪ Fin k):ℝ)*cash:=by
  let w:=fun x:Fin r→I=>c*Real.exp (ρ*(radius z (sites x):ℝ))
  let pay:=fun a:Fin k→Slot G n=>c*Real.exp (ρ*(radius z (trace a):ℝ))*‖entry k F a‖
  have pos (x):0≤w x:=mul_nonneg weight (Real.exp_pos _).le
  have booked (u:Fin r ↪ Fin k):(∑x:Fin r→I,w x*‖entry k F (occupy u x)‖) ≤ cash:=by
    have term (x:Fin r→I):w x*‖entry k F (occupy u x)‖=pay (lifted u x):=by
      dsimp [w,lifted,pay];rw [traced]
    simp_rw [term]
    rw [←sum_map]
    exact (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _=>by dsimp [pay];positivity)).trans paid
  change (∑x:Fin r→I,w x*‖coefficient r (thermal F k) x‖) ≤ _
  calc
    _ ≤ (k.factorial:ℝ)⁻¹*∑x:Fin r→I,∑u:Fin r ↪ Fin k,w x*‖entry k F (occupy u x)‖:=by
      rw [mul_sum];apply sum_le_sum;intro x _
      rw [angular,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity),←mul_sum,mul_left_comm]
      gcongr
      exact norm_sum_le ..
    _ = (k.factorial:ℝ)⁻¹*∑u:Fin r ↪ Fin k,∑x:Fin r→I,w x*‖entry k F (occupy u x)‖:=by rw [sum_comm]
    _ ≤ (k.factorial:ℝ)⁻¹*∑_:Fin r ↪ Fin k,cash:=
      mul_le_mul_of_nonneg_left (sum_le_sum fun u _=>booked u) (by positivity)
    _ = _:=by simp [mul_assoc]
end YM.Integration.WilsonCapturedRootedAngularSlots
