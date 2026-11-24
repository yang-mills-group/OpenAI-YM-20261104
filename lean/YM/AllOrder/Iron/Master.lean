import YM.AllOrder.Iron.Wings
import YM.Next.STATIONARY.Films.TraceDifference
import YM.AllOrder.Iron.Rim
import YM.Next.STATIONARY.Films.ThinTrace
import YM.Next.STATIONARY.Block.Static
import YM.TraceExtension.Perfect.Stove
import YM.Next.STATIONARY.Joint.FourPoint
import YM.Next.STATIONARY.Joint.HaarJac
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Iron
open Lattice Laurent RG Filter Tree Metric Finset Function Gauge Matrix Module
open Exterior Wilson Precision Tree MeasureTheory Stationary
open scoped Matrix BigOperators Topology Classical ContDiff InnerProductSpace Matrix.Norms.Frobenius ENNReal
variable {G:Gauge}{c f:Side}{S:StepData c f} (F:Forest S.ratio)(t:S.Choices) {p:Clip}{R:PathData G}

open Work.F05
variable (i: G.ColorIndex)
open Wilson Precision
open Bloch Laurent Audience Push.Uniform
abbrev start (G:Gauge) (P:Patch) : Eye Empty (Acts G P):= fun _=>0
lemma start_w (h: S.patch.Branches S.kernel G):
    Jaunt (approached (repackM (unitSplit G S 0) (clothe G S) (postroom S t (inch S.patch.L)))) (CanonR (start G S.patch) false).tab 0:= by
  let L: Corn (Co c Empty) →L[ℝ] Bang G c f:=0; have hl : Turns (start G S.patch) (billZ S L):= ⟨0,by intro u; rw [Subsingleton.elim u 0,map_zero]; simp, fun i q hx v=>by ext1 x; simp [start,tune]⟩; -- simp
  let K:= (regulator_tour S t false L hl h (fun _=>rfl)).tab; unfold cardM at K; dsimp only at K; rw [zero_hat S h] at K; exact K
lemma start_pay (G : Gauge)(P:Patch) {σ:ℝ}(h:σ≤1): Spotlight P (start G P) σ (Real.exp 4):= ⟨h,⟨fun _ _=> rfl, fun _ _i=> differentiableAt_const _⟩, le_rfl, fun i=> Empty.elim i⟩

-- executive procurement. B,C give pre-L Bed certs; no annular budget forcing yet.
lemma precursor (G : Gauge)(K:KernelChoices)(k:ℕ)(σ C ε:ℝ)(hσ:0<σ)(hC:0 ≤ C)(he:0<ε):
    ∃ η A:ℝ,0<η∧0≤A∧∀ (f c:Side)(S:StepData c f), S.patch.J=k→ S.kernel=K →
    ∀ (t:S.Choices)(p:Clip)(R:PathData G)(B:Bed) (σ' C' Λ D:ℝ), S.patch.Branches S.kernel G → R.Bounds p σ' C' Λ → Attached B R →
      (B.metric.strip (inch S.patch.L*σ) C) → (∀ n, Floor B p n ε D) → Bid.Sworn B f G →
      (F:Forest S.ratio) → IsUnit (hessian F t p R 0 0).det → Shell S t p R (1:Config G c) (1:Joint G c f) →
        Capped c (fun i:Key F G=> S.ratio.parent i.1.val.1) (fun i:Key F G=> S.ratio.parent i.1.val.1) ((η/4)/2/2/2) (fee G (η/4) S.patch (royalty η (door A S.patch.L η))) (hessian F t p R 0 0)⁻¹ := by
  obtain ⟨μ,Z,hz,hL,hZ,hμ⟩:=amasses G; let x:=min σ μ; let X':ℝ:=Real.exp 4; have hp:0<x:= lt_min hσ hz;
  let v:= tribute2 G k X' Z; have hw:x≤μ:= min_le_right ..; have hx:x≤1 := by linarith
  obtain ⟨η,V,hη,he',hp',hQ⟩:= post_cert G k K ε x C |v| he hp hx hC (abs_nonneg _); refine ⟨η,V,hη,hp',fun f c S hsk hK t p R B u y w D hs hc hA hv ht hs' F h0 ho=>?_⟩;
  let P:= S.patch; have hg : P.Branches K G:=hK ▸ hs; let M := (CanonR (start G P) false).tab
  have hV:= conquer hg hp (start_pay G P hx) (hμ P.L x hw); have hb : B.metric.strip (inch S.patch.L*x) C:= fun i j=> (hv i j).mono (mul_le_mul_of_nonneg_left (min_le_left ..) (inch_pos _).le) le_rfl
  let L:=forceK G P M S.kernel.penalty B; have hT: Poster x M:=hV.covered.tab; have hN: Poster x L:= Poster.amounts (gift_lane B _ hb hp) (hT.reverse.forge hT)
  let m(i:ℕ):Side:= ⟨i+1,Nat.succ_pos _⟩; let n i:= m i * P.L; let wC:Armada m n P K:= ⟨fun i=>rfl⟩; let T(i):=(wC.boot i); let Q(i): (T i).Choices:= Classical.arbitrary _
  have hm : Tendsto (fun i=>(m i).val) atTop atTop:= tendsto_atTop_mono (f:=id) (fun _=> Nat.le_succ _) tendsto_id
  have hF : Freezer (slabW G S.patch.L).dual (slabW G S.patch.L) L η V:=by
    unfold L; rw [hK]; exact hQ P hsk hg B p D M m n wC hm hb ht hT (fun p hp => (hV.base hp).mono (show _ ≤ |v| from (by rw [show P.J=k from hsk]; exact le_abs_self _))) Q (fun i=> start_w (Q i) (by exact hg))
  exact Iron.earn F t hs hp' hη (inch S.patch.L) (inch_pos _) L (hN.skinny he') hF (ticket_own B hs hc hA hs' (ht f) (start_w t hs) hp hb) ho hc h0
end YM.AllOrder.Iron
