import YM.FormalBulk08.Flat.Supply
import YM.Next.STATIONARY.Films.RankColor

/-!
# Adapt stationary freezer machinery to the flat *conditional* problem

Part 1: at the already supplied level metric, put auxiliary root and gauge
slots (will need exact mapping to active coordinates). Choose `After` path
via `amend ... 0`/dummy Clip; no dependence on actual choice of Bed needed
because it cancels on curl inputs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FormalBulk08.Flat
open Filter Set Function Lattice Laurent Bloch Exterior Precision RG Next.Free UVExtension.Free Work.F08
open Stationary
open scoped Topology BigOperators ContDiff Matrix
variable {G : Gauge} {t j : ℕ} {P : Patch} {b f : Side}

def spectator (G : Gauge) (P : Patch) : Eye (Fin 0) (Acts G P) := 0
lemma shines (w : ℝ) (h : w≤1) : Spotlight P (spectator G P) w (Real.exp 4) := by
  refine ⟨h,⟨fun _ _=>rfl,fun _ i=>?_⟩,le_rfl, fun i=> i.elim0⟩
  exact differentiableAt_const _

lemma seats (S : StepData b f) (t : S.Choices) (h : S.patch.Branches S.kernel G) :
    Jaunt (approached (repackM (unitSplit G S 0) (clothe G S) (postroom S t (Stationary.inch S.patch.L))))
      (CanonR (spectator G S.patch) false).tab 0 := by
  let Z : Corn (Co b (Fin 0))→L[ℝ] Bang G b f := 0
  have ht : Turns (spectator G S.patch) (billZ S Z) := by
    refine ⟨0,fun i=>?_,fun i _ _ _=>?_⟩
    · simp only [LinearMap.zero_apply, billZ,Z,ContinuousLinearMap.comp_apply,zero_apply,map_zero]; ext; simp [axes]
    ext i; simp [spectator,tune]
  have hv := (regulator_tour S t false Z ht h (fun x=>rfl)).tab
  unfold cardM at hv; dsimp only at hv; rw [zero_hat S h] at hv; exact hv

/-- Gauge-fixing row in redundant (center+root) coordinates. -/
def shutter (G : Gauge) (P : Patch) := (CanonR (spectator G P) false).tab
lemma meters (S : StepData b f) (t : S.Choices) (h : S.patch.Branches S.kernel G) (W : Bed)
    (E σ : ℝ) (he : W.metric.strip (Stationary.inch S.patch.L*σ) E) (hs : 0<σ) :
    let T := clothe G S
    let U:= postroom (G:=G) S t (Stationary.inch S.patch.L)
    Jaunt (approached (repackM T T (frontR G S W + Uᵀ*U))) (forceK G S.patch (shutter G S.patch) S.kernel.penalty W) 0 := by
  intro T U
  classical
  have hU:=seats S t h
  change Jaunt (approached (repackM T T (frontR G S W)+repackM T T (Uᵀ*U))) _ 0
  rw [prom_addition, repack_multiply _ (unitSplit G S 0), repack_rotate,prom_mul]; exact (gift_turn W hs he).plus (hU.takes.hoist hU)

lemma watches (K : KernelChoices) (j : ℕ) (G : Gauge) (σ ε E : ℝ) (hs : 0<σ) (he : 0<ε) (hE : 0≤E) :
    ∃ w C : ℝ, 0<w ∧ w ≤ σ ∧ 0 ≤ C ∧ ∀ P : Patch, P.J=j → P.Branches K G →
      ∀ B : Bed, B.metric.strip σ E → ∀ (a : Clip), (∀ n,Floor B a n ε E) →
        let F := forceK G P (shutter G P) K.penalty B
        Poster w F ∧ Freezer (slabW G P.L|>.dual) (slabW G P.L) F w C := by
  obtain ⟨τ,D,hτ,hq,hD,h⟩:=amasses G
  let v:=min τ σ
  have hv : 0<v:=lt_min hτ hs
  have hp : v≤ 1 := (min_le_left ..).trans (hq.trans (by norm_num))
  let M:= |tribute2 G j (Real.exp 4) D|
  obtain ⟨η,C,hη,hS,hV,H⟩:=post_cert G j K ε v E M he hv hp hE (abs_nonneg _)
  refine ⟨η,C,hη,hS.trans (min_le_right ..),hV,fun P hP hPG B hB a hA=>?_⟩
  intro F
  let e (i:ℕ) : Side:= walent i*P.L
  let u: Armada walent e P K:=⟨fun i=>rfl⟩
  have he := conquer hPG hv (shines (P:=P) v hp) (h P.L v (min_le_left ..))
  have hx : B.metric.strip (Stationary.inch P.L*v) E:=strip_mono hB ((mul_le_of_le_one_left hv.le (Stationary.inch_le _)).trans (min_le_right ..)) le_rfl
  have ht : Poster v (shutter G P) := he.covered.tab
  have hy (i) : Nonempty (u.boot i).Choices:= by
    unfold StepData.Choices StepData.SitesChoice StepData.BondChoice Patch.FrameTag
    infer_instance
  exact ⟨Poster.skinny (Poster.amounts (gift_lane B _ hx hv) (ht.reverse.forge ht)) hS,
    H P hP hPG B a E (shutter G P) _ _ u walentes hx hA ht (fun i w=> (he.base w).mono (by unfold M; rw [← hP]; exact le_abs_self _)) (fun i=> Classical.choice (hy i)) (fun i=>seats _ _ hPG)⟩

/-- An auxiliary Floor-bearing bed. Precision on horizontal vectors is
exactly that of pink. No assertion it is the path's represented floor. -/
structure After (k : ℝ) (V : Train j) where
  B : Bed
  stands (n : Side) : Precision.K (B.metric.acts n)=Precision.K ((pink k V).acts n)

lemma affiliates (j : ℕ) (h : 4≤j) (k : ℝ) (hk : 0<k) :
    ∃ σ A ε : ℝ,0<σ ∧ 0<A ∧ 0<ε ∧ ∃ a : Clip, ∀ V : Train j,
      ∃ W : After k V, W.B.metric.strip σ A ∧ ∀ n, Floor W.B a n ε A := by
  obtain ⟨γ,σ,ε,C,hγ,hσ,hε,hC,H⟩:= bid_bed k 0 hk le_rfl h
  let a : Clip := ⟨γ,γ/32,1,hγ,by positivity,by linarith,one_pos⟩
  refine ⟨σ,C,ε,hσ,hC,hε,a,fun V=>?_⟩
  obtain ⟨B,hB,hH,hf,-,-⟩:=H a le_rfl V
  let hp : After k V:=⟨B,fun n=> by
    rw [hB.metric]; unfold Precision.K
    rw [Matrix.mul_assoc,(obligations k 0 hk le_rfl h V n).2.2.1,Matrix.mul_assoc]⟩
  exact ⟨hp,hH.2.1,hf⟩
end YM.FormalBulk08.Flat
