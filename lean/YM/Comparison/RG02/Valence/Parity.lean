import YM.Comparison.RG02.Valence.General
/-! Export to next-step recalibration: vacuum / logMarked / numerator graded kernels.
Include parity so formal kinetic order convention and changes of coordinated field units can see
both primitive and generated valences. No lift hypothesis needed and no bound inferred. -/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Valence.Parity
open Function Filter Finset MeasureTheory RG Precision Lattice Wilson Exterior Tree
open YM.Analysis YM.Marker YM.Multi Cumulants Cumulants.Wick Order Join Bulk Assembly
open YM.Extra.Trajectories (connected)
open YM.Next.Rank
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

variable {V : Type} [DecidableEq V] [Fintype V] {R : Census V} {r : ℕ}
variable {G : Gauge} {c f : Side} {S : StepData c f} {p : Clip} {P : PathData G} {O : ChartRatio G}
  (K : Bulk.Kernel S p P O) (F : Tree.Forest S.ratio) (w : S.Choices) (W : Bulk.Colors R G f)
  (ξ : V→ℂ) (r:ℕ) (s:R.Mode)
local notation "X" => fieldDir G c 1
local notation "B"=> Board R r
local notation "Δ" => dilation (Board R r) (Sum.elim ξ (fun _=>(-1)))
local notation "Ω" x => Fk K F w W x r

open Mirror
variable (hK : Well W)
lemma re_obs (Q:Grade R r) (k:ℕ) :
    (observe R r (Δ Q) k).part s= shape ξ s k*(observe R r Q k).part s := by
    unfold observe; split
    next H=>
      change _*((Δ Q).part (pair s (pick r k)))= shape ξ s k*((k.factorial:ℂ)⁻¹ * Q.part _)
      rw [dilation_part]
      have he : (∏ a∈(pair s (pick r k)).val, Sum.elim ξ (fun _=> -1) a)=shape ξ s k:= by simp [shape,pair,prod_disjSum,mul_comm,picked r H]
      rw [he]; ring
    next=> simp
lemma log_balance (z : Grade R r) (h : UnitLeading z) : Δ (logMarked z)=logMarked (Δ z) := by
   have hx : UnitLeading (Δ z):=(quiet_dilation _ _).trans h; ext t
   simp_rw [dilation_part, log_m_part t h, log_m_part t hx]; split; exact mul_zero _
   rw [← log_map Δ (quiet_dilation _) h,dilation_part]
lemma vac_balance (z : Grade R r) (h : UnitLeading z) : Δ (logVac z)=logVac (Δ z) := by
   have hx : UnitLeading (Δ z):=(quiet_dilation _ _).trans h; ext t
   simp_rw [dilation_part, log_v_part t h, log_v_part t hx]; split
   · rw [← log_map Δ (quiet_dilation _) h,dilation_part]
   exact mul_zero _

-- read mark with mark projection
variable {n : ℕ} (x:X) (k:ℕ)
def tilted (ξ:ℂ) (f:X→ℂ) := ∀ x, f (-x)=ξ*f x
include hK
lemma moment (h : Sound W ξ) : tilted (shape ξ s k) (fun x=> (observe R r (Ω x) k).part s) := by
   intro x; dsimp only; rw [← Mirror.fk r hK h x]; apply re_obs
lemma mark (h : Sound W ξ) : tilted (shape ξ s k) (fun x=> (observe R r (logMarked (Ω x)) k).part s) := by intro x; dsimp only; rw [← Mirror.fk r hK h x,← log_balance ξ r (Ω x) (fk_unit ..)]; apply re_obs
lemma even_vac (h : Calm W) : tilted (shape (0:V→ℂ) R.quiet k) (fun x=> (observe R r (logVac (Ω x)) k).part R.quiet) := by
   -- use only the vacuum germ. Ignore all marks and their powers.
   let W': Bulk.Colors R G f:= {W with mark:=0,power:=0}; have hw : Well W':= by
      refine ⟨hK.suppose_vac, fun i=> GradeAt.grade_zero _, hK.natural, fun _ _ _ _=>rfl,hK.envelope,?_⟩
      intro i s; exact ⟨measurable_const, ‖(0:ℂ)‖, fun _=>le_rfl⟩
   have hz : Sound W' (0:V→ℂ):= ⟨h, fun i s=> (smul_zero _).symm⟩
   let L(x:X):= Fk K F w W' x r
   have he(x:X): logVac (Ω x)=logVac (L x):= by
      apply congrArg connected; apply Join.both_parts; intro s t
      simp_rw [denominator,bottom_value]; split_ifs
      next h => unfold L; rw [Bulk.table,Bulk.table]; simp_rw [Bulk.clear]; rfl
      next=> rfl
   simp_rw [he]; intro x; dsimp only [L]; rw [← Mirror.fk r hw hz x,← vac_balance (0:V→ℂ) r _ (fk_unit ..)]; apply re_obs

omit hK in
lemma vanish {φ:X→ℂ} {m:ℂ} (h : ContDiffAt ℝ n φ 0) (p : tilted m φ) (hn: (-1:ℂ)^n≠m) : iteratedFDeriv ℝ n φ 0=0 := by
    let L : X→L[ℝ]X:= -ContinuousLinearMap.id ℝ _; let A:ℂ→L[ℝ]ℂ:= ContinuousLinearMap.mul ℝ ℂ m
    have he: φ ∘ L=A ∘ φ:= funext p; let q:= iteratedFDeriv ℝ n φ 0
    apply ContinuousMultilinearMap.ext; intro v
    have hs:= congrArg (fun f:X→ℂ=> iteratedFDeriv ℝ n f 0 v) he
    change iteratedFDeriv _ _ _ _ _= _ at hs
    rw [A.iteratedFDeriv_comp_left h le_rfl, Assembly.contact_right L (show ContDiffAt ℝ n φ (L 0) from L.map_zero.symm ▸ h),L.map_zero] at hs
    change q (fun i=> -(v i))=m*(q v) at hs
    rw [show (fun i=>-v i)=(fun i=>(-1:ℝ) • v i) from funext fun i=>(neg_one_smul ℝ _).symm, q.map_smul_univ (fun _=>-1), Complex.real_smul] at hs
    simp only [prod_const,Finset.card_univ,Fintype.card_fin] at hs; push_cast at hs
    exact (mul_eq_mul_right_iff.mp hs).resolve_left hn

lemma shut_moment (h : Sound W ξ) (hn : (-1:ℂ)^n≠shape ξ s k):
    iteratedFDeriv ℝ n (fun x=> (observe R r (Ω x) k).part s) 0=0 := vanish ((moment_record K F w W r s k).of_le le_top|>.contDiffAt) (moment K F w W ξ r s hK k h) hn
lemma shut (h : Sound W ξ) (hn : (-1:ℂ)^n≠shape ξ s k):
    iteratedFDeriv ℝ n (fun x=> (observe R r (logMarked (Ω x)) k).part s) 0=0 := vanish ((mark_read K F w W _ _ k (every W.power s)|>.smooth.of_le le_top).contDiffAt) (mark K F w W ξ r s hK k h) hn
lemma kinetic (h : Calm W) (hn : (-1:ℂ)^n≠(-1)^k):
    iteratedFDeriv ℝ n (fun x=> (observe R r (logVac (Ω x)) k).part R.quiet) 0=0 := vanish ((vacuum_read K F w W r k).smooth.of_le le_top|>.contDiffAt) (even_vac K F w W r hK k h) (by simpa [shape,Census.quiet] using hn)
lemma lean_loop (h : Calm W) (hn : Odd k):
    iteratedFDeriv ℝ 2 (fun x=> (observe R r (logVac (Ω x)) k).part R.quiet) 0=0 := kinetic K F w W r hK k h (by rw [hn.neg_one_pow]; norm_num)

end YM.Comparison.RG02.Valence.Parity
