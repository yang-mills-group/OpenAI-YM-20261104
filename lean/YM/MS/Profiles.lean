import YM.MS.SineMomentum
import YM.MS.CompareSymbol
import YM.MS.Damping

/-!
# Heat profiles on reciprocal momentum, uniform difference bounds

The line bounds retain the exponential costs.
Use any finite dimensional A index, not fixed to a diagram degree.
Momentum in reciprocal zone uses sup norm radius π.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS
open Set Function Real Momentum Filter
open scoped Topology ContDiff
variable {ι A E F : Type*} [Fintype A]

def leaf (N : Scale ι) i (p : Momentum A) := N.length i • p

def spread (N : Scale ι) i (p : Momentum A) := N.length i • wave p

def phaseDiff (N : Scale ι) (i : ι):= (N.length i^2)⁻¹

def spreadCost (N : Scale ι) (i : ι) (p : Momentum A) := exp (-(min (Momentum.sq (leaf N i p)) (Momentum.sq (spread N i p))))

variable {S : Scale ι}
lemma pd_pos (i) : 0 < phaseDiff S i:= inv_pos.mpr (pow_pos (S.pos i) _)
lemma pd_small (i) (h:1 ≤ S.length i) : phaseDiff S i ≤ 1 := by unfold phaseDiff; exact inv_le_one_of_one_le₀ (one_le_pow₀ h)

/-- Simultaneous comparisons on the full reciprocal arguments, not just the zone.
   `spreadCost` retains an exponential min; so inside zone pays even `.Line`. -/

abbrev profileCost (S : Scale ι) (f : Momentum A → ℝ) (p : Kern ι (Momentum A) ℝ) :=
    Like S.full S (phaseDiff S) (fun i x=> f (spread S i x)) (fun i x=> f (leaf S i x)) p

lemma profile_const (S : Scale ι) (a : ℝ) : profileCost (A:=A) S (fun _=>a) fun _ _=>1 :=
    Like.same (fun i=>(pd_pos (S:=S) i).le) (Costs.scalar (p:=fun _=>a) ⟨1+‖a‖,by positivity,0,fun _ _ _=>by simp⟩)

section
variable (ht : ∀ i, 1≤S.length i)
include ht
lemma omega_check (k : A) : profileCost (A:=A) S (fun x=> x k) (fun _ _=>1) := by
   let N:= S.length
   let f i (x : Momentum A) := N i • wave x k; let g i (x:Momentum A) := N i • x k
   let h : Bound S g fun _=> 1 := S.rescaled (ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : A=>ℝ) k).hasTemperateGrowth
   let U : ι→ℝ:= phaseDiff S
   have he : Bound S (fun i p=> f i p-g i p) U := by
      have ha : Bound S (fun i (_: Momentum A)=> S.length i) S.length:= Costs.scalar (p:=S.length) (Cost.of_le fun i p _=> (Real.norm_of_nonneg (S.pos i).le).le)
      convert! ha.smul (defect ht k) using 1
      · ext i p; dsimp only [f,g,N]; rw [smul_sub]
      ext i; have hn:=S.pos i; dsimp only [U,phaseDiff]; field_simp
   refine ⟨?_,h,(by simp only [one_mul]; exact he)⟩
   have hf : Bound S f fun _=>1:= by
      convert! (he.raise (Cost.of_le (g:=fun _ _=>1) fun i p _=>pd_small i (ht i))).add h using 1
      ext; exact (sub_add_cancel ..).symm
   exact hf
end

lemma profile_mul {a b : Kern ι (Momentum A) ℝ} {f g : Momentum A→ℝ} (hx : profileCost S f a) (hh : profileCost S g b) : profileCost S (fun p=> f p*g p) (fun i p=>a i p*b i p):= hx.rmul hh
lemma profile_sq (h : ∀ i, 1≤S.length i) : profileCost S (Momentum.sq (A:=A)) fun _ _=>1:= by
   simp_rw [profileCost,Momentum.sq]; refine Like.sum (fun k _=>?_) (fun _ _ _=> zero_le_one) (fun i=> (pd_pos i).le)
   simpa [profileCost,pow_two] using (omega_check h k).rmul (omega_check h k)
lemma profile_exp (h : ∀ i, 1≤S.length i) : profileCost S (fun p:Momentum A=> exp (-Momentum.sq p)) (spreadCost S):= by
   have he := (profile_sq (A:=A) h).neg
   have hl (i : ι) (x : Momentum A) : spreadCost S i x = exp (max (-Momentum.sq (spread S i x)) (-Momentum.sq (leaf S i x))) :=by unfold spreadCost; congr 1; rw [min_def,max_def]; split <;> (split <;> linarith)
   refine ⟨he.lat.exp_full.raise (Cost.of_le fun i p _=> (exp_monotone (le_max_left ..)).trans_eq (hl i p).symm),he.std.exp_full.raise (Cost.of_le fun i p _=> (exp_monotone (le_max_right ..)).trans_eq (hl i p).symm),?_⟩
   simp_rw [hl]; simpa only [one_mul, mul_comm (phaseDiff S _)] using Costs.exp_delta he.lat he.std he.gain
lemma spread_limit (i) (p : Momentum A) : spreadCost S i p≤1 := Real.exp_le_one_iff.mpr (by exact neg_nonpos.mpr (le_min (sq_nonnegative ..) (sq_nonnegative ..)))

def firstZone (A : Type*) [Fintype A] : Set (Momentum A) := Metric.closedBall 0 π
lemma spread_damp (i) (p : Momentum A) (hp : p∈firstZone A) : spreadCost S i p ≤ exp 1*S.damp 1 i p := by
   let R:= S.length i; let w:= R*‖p‖
   have hR:=S.pos i; have he:0≤w:=mul_nonneg hR.le (norm_nonneg _)
   have hv : ‖leaf S i p‖ ≤ 2*‖spread S i p‖:= calc
       _ = w := norm_smul_of_nonneg hR.le _
       _ ≤ (S.length i)*(2*‖wave p‖) := mul_le_mul_of_nonneg_left (wave_large p (by simpa [firstZone] using hp)) hR.le
       _ = _ := by rw [spread,norm_smul_of_nonneg hR.le]; ring
   unfold Scale.damp spreadCost; rw [← exp_add,min_def] -- split
   split
   · rw [exp_le_exp]; have hh:=sup_square (leaf S i p); rw [leaf,norm_smul_of_nonneg hR.le] at hh; -- rw also goal? hv?
     simp only [leaf] at * 
     nlinarith
   rw [exp_le_exp]; have hh:=sup_square (spread S i p); rw [leaf,norm_smul_of_nonneg hR.le] at hv; have e : 0 ≤ S.length i*‖p‖:=he; have hl:=norm_nonneg (spread S i p); nlinarith [sq_nonneg (‖spread S i p‖-1)]
end YM.MS
