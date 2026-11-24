import YM.LocalLTE.Units.Sure
import YM.Work.G05.Taylor
/-! # Re-box in curved coordinates, maintaining ambient jets -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.FrameBox.Hall
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat SliceRows
open AbsoluteSums Animals PhysicalNext.Repeat Fare Lapis Lantern Shellac Token Sienna Boulevard Inset
open Analysis Slide
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c L : Side} {i p:ℕ} {o:Site c} (X:Grove o) (m:ℕ){κ a l : ℝ}
open Cabana Grove
local notation "O" => Chi.canonical
local notation "Z" => neighbors m o
local notation "ι" => Directions G c
lemma zeroSolo : (soloV (0:Directions G c):Config G c)=1:= funext fun _=> G.mat_lieExp_zero
lemma bare : increment (1:Config G c)= soloV:= by funext i j; unfold soloV increment; simp
lemma allTrip (k:Site c)(l:Walk) : travel (1:Config G c) k l=1 := by
   induction l generalizing k <;> simp_all [travel,Lattice.Step.read]
lemma quadrant (u:G.El)(x: Directions G c) : soloV (wheel u x) = gauge (fun _=>u) (soloV x):= by
   funext i; apply G.mat_injective; change G.mat (G.lieExp (G.adjoint u _)) = G.mat (u*G.lieExp _*u⁻¹); rw [G.mat_lieExp,G.mat_mul,G.mat_mul,G.mat_lieExp,G.mat_adjoint,G.exp_conjugate]; rfl

def bushes (i:ℕ)(f:Config G c→ℝ): Pkt (Directions G c) i:= fun j=> Tensor.coeff (f ∘ soloV) j 0

def shave (m:ℕ)(κ:ℝ)(i:ℕ)(f:Config G c→ℝ): Config G c→ℝ:= FrameBox.realise X m κ (colorP (bushes i f))
lemma bays (i:ℕ)(f:Config G c→ℝ): Cabana.actual (bushes i f)= stem i (f ∘ soloV):= Fin.sum_univ_eq_sum_range (fun i:ℕ=> Tensor.diagonal (Tensor.coeff (f ∘ soloV) i 0)) i
lemma clip_ok (X:Grove o){t κ:ℝ}(h: Reliable G κ t)(j:ℕ) (U:Config G c): ContDiffAt ℝ j (X.crook m Chi.canonical κ ∘ increment U) 0:= by
    refine ((X.shore m).contDiff.contDiffAt.comp 0 ?_)
    let D i x:= G.mat (X.fix (increment U x) i); have hg i: ContDiffAt ℝ ∞ (D i) 0 := by
      have hL i:ContDiffAt ℝ ∞ (fun x=> G.mat (increment U x i)) 0:= (by unfold increment; simp only [G.mat_mul]; exact (((G.exp_jet.comp (contDiff_apply ..)|>.contDiffAt).of_le (by exact le_top)).mul contDiffAt_const))
      have hh (l:Walk) (k:Site c): ContDiffAt ℝ ∞ (fun y=> G.mat (travel (increment U y) k l)) 0:= by
        induction l generalizing k with
        | nil=> simp only [travel]; exact contDiffAt_const
        | cons i l ih=>
          simp only [travel,G.mat_mul]; apply ContDiffAt.mul ?_ (ih _); rcases i with ⟨_,b|b⟩
          · exact hL _
          exact (starL' ℝ : G.Mat ≃L[ℝ] G.Mat).contDiff.contDiffAt.comp _ (hL _)
      unfold D Grove.fix Lattice.gauge; simp only [G.mat_mul,G.mat_inv]; exact ((hh _ _).mul (hL _)).mul ((starL' ℝ : G.Mat ≃L[ℝ] G.Mat).contDiff.contDiffAt.comp _ (hh _ _))
    exact contDiffAt_pi.mpr (fun i=> (h.smooth Chi.canonical (show _ from hg i)).of_le (show (j : WithTop ℕ∞) ≤ (∞:WithTop ℕ∞) from (show (↑(j:ℕ∞):WithTop ℕ∞)≤ ↑(⊤:ℕ∞) from WithTop.coe_le_coe.mpr le_top)))

variable {t:ℝ}{P:BudgetPoint}
lemma home (h:Reliable G κ t)(B: BudgetPoint): X.crook m Chi.canonical κ (1:Config G c) = 0:= by
    obtain ⟨R,hR,H⟩:= Grove.sound_ball G (χ:=Chi.canonical) h
    have hh:= H c B o X m 0 (norm_zero.trans_le (mul_pos hR B.threshold_pos).le)|>.1
    rwa [map_zero,zeroSolo] at hh
lemma roots (X:Grove o){κ t:ℝ}(h:Reliable G κ t)(j:ℕ)(B:BudgetPoint)(f:Config G c→ℝ)(hp: B.Regular (neighbors m o) f)(hf:ContDiffAt ℝ (↑ j) (f ∘ soloV) 0)(i:ℕ)(hx:i<j):
    iteratedFDeriv ℝ i (shave X m κ j f ∘ increment 1) 0 = iteratedFDeriv ℝ i (f ∘ increment 1) 0 := by
    rw [bare]; let u:=(X.crook (G:=G) m O κ) ∘ soloV; let v:= f ∘ soloV; let Q:= bushes j f; have hv:u 0=0:= by unfold u; rw [Function.comp_apply,zeroSolo]; exact home X m h B
    have hV : v=ᶠ[𝓝 0] v ∘ u:= by
        have hh: ∀ i:Bond c, ∀ᶠ y: Directions G c in 𝓝 0,G.chord (X.fix (soloV y) i)≤κ:= by
           intro i; let b (y: Directions G c):=G.chord (X.fix (soloV y) i)
           have h₀ : X.fix (1:Config G c)= 1:= funext fun l=>by unfold fix Grove.uplink Lattice.gauge; simp [allTrip]
           have he:b 0<κ:=by unfold b; rw [zeroSolo,h₀]; exact (G.chord_one).trans_lt h.down
           have hk:Continuous b:=by unfold b Grove.fix Lattice.gauge Grove.uplink soloV; fun_prop
           filter_upwards [hk.continuousAt.eventually (gt_mem_nhds he)] with y hy using (show b y<κ from hy).le
        filter_upwards [eventually_all.mpr hh] with i hi
        change f (soloV i)=f (soloV _)
        dsimp only [u,Function.comp_apply]; rw [hp.sites _ _ (X.repairs O h _ (fun j _=> hi j))]; exact (hp.symmetry _ _).symm
    have hc:Cabana.actual (colorP Q)=stem j v:=by
       funext i; rw [sunwheel]; have hh j' (hj:j'<j) (u:G.El) (x: Directions G c): Tensor.diagonal (Tensor.coeff v j' 0) (wheel u x)=Tensor.diagonal (Tensor.coeff v j' 0) x:= by
          let S:=(wheel (c:=c) u); have ht:v ∘ S=v:= funext fun k=>by change f (soloV (wheel u k))=_; rw [quadrant]; exact hp.symmetry _ _
          unfold Tensor.diagonal Tensor.coeff; rw [← ht]
          conv_lhs=> rw [ht]
          rw [Blaze.linear_pull S (by rw [map_zero]; exact hf.of_le (show (↑j':WithTop ℕ∞)≤ j from by exact_mod_cast hj.le))]; rw [map_zero]; rfl
       have ht: ∀ u:G.El,Cabana.actual Q (FrameBox.wheel u i)=stem j v i:=by
          intro u; unfold Q; rw [bays]; unfold stem
          simp only [Finset.sum_apply]; exact Finset.sum_congr rfl (fun i' hL=> hh i' (mem_range.mp hL) u i)
       simp_rw [ht]; simp
    unfold shave realise; change iteratedFDeriv ℝ i (Cabana.actual (colorP Q) ∘ u) 0 = iteratedFDeriv ℝ i v 0
    rw [hc]; have h': ContDiffAt ℝ (↑ i) u 0:= by unfold u; rw [← bare]; exact clip_ok _ X h i _
    apply Eq.trans (b:=iteratedFDeriv ℝ i (v∘u) 0) _ (hV.iteratedFDeriv ℝ i|>.eq_of_nhds).symm; exact Work.G05.jets_comp h' h' (stem_contDiff _ _|>.contDiffAt) (hv.symm ▸ hf.of_le (by exact_mod_cast hx.le)) rfl (fun _ _=>rfl) (fun l hl => hv.symm ▸ firstJet hf (lt_of_le_of_lt hl hx) le_rfl) i le_rfl -- edit

end YM.LocalLTE.FrameBox.Hall
