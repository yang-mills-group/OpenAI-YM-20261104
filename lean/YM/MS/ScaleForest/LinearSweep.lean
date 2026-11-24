import YM.MS.ScaleForest.PinnedCut
/-!
# Linear sweeping of dimensionally continued momentum in a placed join

Prove actual integration properties needed for the oscillatory multi-pin
sector join. Remember factors independent of `r` and primary momentum can
be taken out of the measure: use this also to show the reference equality
before we put back in physical-chart momentum scales. See `WirePinned`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.ScaleForest
open Set Filter MeasureTheory Real Function
open Plane Koszul Heat Flux Landau Arts Arc Spin Pilot Wire Rock Path Oceans Plum Alps
open scoped Topology ContDiff
variable {G : Gauge} {s : ℂ} {m n : ℕ} {I E F J:Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

-- Here `F` can be the primary-mom test sector.
def Sweeping (u : (F×ℝ)×E→ℂ) : Prop := Ultra u ∧ mirror u

section
variable {u v : (F×ℝ)×E→ℂ}

theorem Sweep_sum (h : Sweeping u) (he : Sweeping v) : Sweeping (u+v) :=
  ⟨h.1.add he.1, fun f t p=> congr_arg₂ (·+·) (h.2 f t p) (he.2 f t p)⟩
theorem Sweep_neg (h : Sweeping u) : Sweeping (-u) := ⟨Rapid.neg h.1, fun f t p=> congr_arg (-(·)) (h.2 f t p)⟩
theorem Sweep_sub (h : Sweeping u) (he : Sweeping v) : Sweeping (u-v) := by rw [sub_eq_add_neg]; exact Sweep_sum h (Sweep_neg he)

theorem Sweep_scale (h : Sweeping u) (c : ℂ) : Sweeping (c • u) := ⟨h.1.L (ContinuousLinearMap.mul ℝ ℂ c), fun f t p=> congr_arg (c * ·) (h.2 f t p)⟩

variable (x : E→ℂ) (he : veg 0 (fun _:Unit=>x) 1)

def factors (x : E→ℂ) (u : (F×ℝ)×E→ℂ) := fun p=> u p * x p.2
include he in
theorem Sweep_mult (h : Sweeping u) : Sweeping (factors x u) := by
   refine ⟨ ?_,fun f t p=> congr_arg (·* x p) (h.2 f t p) ⟩
   convert! h.1.mul (Bound.linear (ContinuousLinearMap.snd ℝ (F×ℝ) E) he) using 1; ext; simp

section measure
variable [MeasurableSpace F][BorelSpace F] [FiniteDimensional ℝ F] (μ:Measure F) [μ.IsAddHaarMeasure]
   (hs : s∈Town)
include hs in
theorem Sweep_reads (h : Sweeping u)(he : Sweeping v) (n : ℕ) : swoop s μ n (u+v)=swoop s μ n u+swoop s μ n v := by
   unfold swoop
   rw [show carpet μ (u+v)=carpet μ u+carpet μ v from funext fun p=> integral_add ((Q.Gmajor μ h.1 ()).values p) ((Q.Gmajor μ he.1 ()).values p)]
   exact core_pl (Q.Gquiet μ h.1) (mirror_r μ h.2) (Q.Gquiet μ he.1) (mirror_r μ he.2) hs n

theorem Sweep_reads_scale (h : Sweeping u)(z : ℂ) (n : ℕ) (s : ℂ) : swoop s μ n (z • u)= z • swoop s μ n u := by
   unfold swoop
   rw [show carpet μ (z • u)=z • carpet μ u from funext (fun p=> by simp only [carpet, Pi.smul_apply, integral_smul])]
   exact core_m (Q.Gquiet μ h.1) z s n
include hs in
theorem Sweep_reads_sub (h : Sweeping u)(he : Sweeping v) (n : ℕ) : swoop s μ n (u-v)=swoop s μ n u-swoop s μ n v := by
   rw [sub_eq_add_neg,sub_eq_add_neg, ← neg_one_smul ℂ v,Sweep_reads μ hs h (Sweep_scale he (-1)) n,Sweep_reads_scale μ he]; simp

include he in
theorem Sweep_reads_factors (h : Sweeping u) (s : ℂ) (m : ℕ) : swoop s μ m (factors x u)= swoop s μ m u * x := by
   funext w
   have h_p : Ultra (carpet μ (factors x u)) := Q.Gquiet μ (Sweep_mult x he h).1
   have hu : Ultra (carpet μ u) := Q.Gquiet μ h.1
   let V:= x w • carpet μ u
   have hV : V=(fun p=>x w* carpet μ u p):= rfl
   have hz := Fiber.pruneC w w (h_p.smooth ()) (show ContDiff ℝ ∞ V from (hu.smooth ()).const_smul (x w)) (fun r=> show carpet μ (factors x u) (r,w)= V (r,w) from by
     unfold V factors carpet; dsimp only; rw [integral_mul_const]; exact mul_comm .. ) (m+1)
   change ∀ r, _= pruning (m+1) (x w • carpet μ u) (r,w) at hz
   rw [coill (hu.smooth ())] at hz
   unfold swoop coreC; simp only [fetching,fetchP,Pi.mul_apply,Pi.smul_apply]; rw [mul_comm _ (x w)]; simp only [hz,Pi.smul_apply, smul_eq_mul,Complex.real_smul]; -- factor
   simp_rw [mul_left_comm (cloud s _) (x w), integral_const_mul]; exact mul_left_comm ..

-- Evaluate on a fixed external momentum. May change coordinate chart/ray parameter.
theorem Sweep_eq {J : Type} [NormedAddCommGroup J] [NormedSpace ℝ J] (m : ℕ) (z : ℂ) (h : Sweeping u)
    {v:(F×ℝ)×J→ℂ} (hv : Sweeping v) (x : E) (y : J) (he : ∀ q, u (q,x)= v (q,y)) : swoop z μ m u x= swoop z μ m v y := by
   have h_u r : carpet μ u (r,x) = carpet μ v (r,y) := by unfold carpet; dsimp only; simp_rw [he]
   have hx:= Fiber.pruneC x y ((Q.Gquiet μ h.1).smooth ()) ((Q.Gquiet μ hv.1).smooth ()) h_u (m+1)
   change ∀ r, pruning (m+1) (carpet μ u) (r,x)=pruning (m+1) (carpet μ v) (r,y) at hx
   unfold swoop; simp only [coreC,Pi.smul_apply,fetching,fetchP,hx]
end measure
-- Koszul scatter commutes
variable (p:Sector J) (w : Legs J) (f : Legs J→Legs J→(F×ℝ)×E→ℂ)
   (ht : ∀ l r, Split l r w→ Sweeping (f l r))

def SweepScat (j:Sector J) (w:Legs J) (f : Shared J (F→ℂ)) : F→ℂ := fun x=> scatter j w (fun l r=> f l r x)


include ht
theorem Sweep_gathers : Sweeping (SweepScat p w f) := by
   induction w generalizing f with | nil=> exact ht _ _ .nil | cons i w ih=> exact ih (fun l r=> f (i::l) r+ (cross (p i) (degree p l):ℂ) • f l (i::r)) (fun l r he=> Sweep_sum (ht _ _ he.left) (Sweep_scale (ht _ _ he.right) _))

variable [MeasurableSpace F][BorelSpace F] [FiniteDimensional ℝ F] (μ:Measure F) [μ.IsAddHaarMeasure]
   (hs : s∈Town)
include hs

theorem Sweep_reads_splits (n : ℕ) : swoop s μ n (SweepScat p w f)= SweepScat p w (fun l r=> swoop s μ n (f l r)) := by
   induction w generalizing f with
   | nil=> rfl
   | cons i w ih=>
      -- linearity inside shuffle function
      let c (l : Legs J):ℂ := cross (p i) (degree p l)
      let g (l r : Legs J) := f (i::l) r+c l • f l (i::r)
      change swoop s μ n (SweepScat p w g)=_
      rw [ih g (fun l r he=> Sweep_sum (ht _ _ he.left) (Sweep_scale (ht _ _ he.right) _))];
      funext x; refine scatter_congr p w _ _ fun l r he=>?_
      unfold g
      dsimp only
      rw [Sweep_reads μ hs (ht _ _ he.left) (Sweep_scale (ht _ _ he.right) _), Sweep_reads_scale μ (ht _ _ he.right)]; rfl
end
end YM.MS.ScaleForest
