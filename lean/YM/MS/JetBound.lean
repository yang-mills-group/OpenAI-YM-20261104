import YM.MS.MomOrigin
import YM.MS.Symbol
import YM.MS.LogTime

/-!
# Agreement of Taylor jets at large heat length implies the symbol comparison

This is the high-scale integration argument in Prop add-high of the addendum.
We give versions admitting other uniform parameters (period, log subtraction
scale, positions when applied to joined terms). Intersect later for IR intervals.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.LogTime
open Real Function Filter Set
open scoped Topology ContDiff Interval
variable {ι E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

structure IntervalFamily (ι : Type*) where
  beg (i : ι) : ℝ
  window (i : ι) : Set ℝ
  beg_nn (i : ι) : 0 ≤ beg i
  ci (i : ι) : window i ⊆ Ici (beg i)
  used (i : ι) : beg i ∈ window i
  ord i : OrdConnected (window i)
  logPart (i : ι) : ℝ
  lg i : 1 ≤ logPart i

namespace IntervalFamily
variable (S : IntervalFamily ι)
def Inst := {p : ι × ℝ // p.2 ∈ S.window p.1}
variable {S}
def index (u : S.Inst) : ι := ((u : Subtype _).val : ι × ℝ).1
def t (u : S.Inst) : ℝ := ((u : Subtype _).val : ι × ℝ).2
lemma Inst.mem (u : S.Inst) : t u ∈ S.window (index u) := (u : Subtype _).property
lemma Inst.ge (u : S.Inst) : S.beg (index u) ≤ t u := S.ci (index u) u.mem
variable (S)
def start (i : ι) : S.Inst := Subtype.mk (i,S.beg i) (S.used i)
def choose (i : ι) (x : ℝ) (hx : x ∈ S.window i) : S.Inst := Subtype.mk (i,x) hx

abbrev primary : Scale S.Inst :=
  ⟨fun u => exp (t u), fun _ => exp_pos _, fun u=> S.logPart (index u)*(1+t u), fun u=>
     one_le_mul_of_one_le_of_one_le (S.lg _) (le_add_of_nonneg_right ((S.beg_nn _).trans u.ge))⟩
abbrev dawn : Scale ι :=
  ⟨fun i=> exp (S.beg i), fun _ => exp_pos _, fun i=> S.logPart i*(1+S.beg i), fun i=>
    one_le_mul_of_one_le_of_one_le (S.lg _) (le_add_of_nonneg_right (S.beg_nn i))⟩

variable {S}
def here (f : ι → ℝ → E → F) (u : S.Inst) := f (index u) (t u)
def pays (g : ι → ℝ) (α : ℝ) (u : S.Inst) := g (index u) * exp (α * t u)
variable (S)

variable [NormedSpace ℝ E] [NormedSpace ℝ F]
private lemma testPart {f : ι → ℝ → E → F} {g : ι → ℝ} {α : ℝ} {j : ℕ} :
    S.primary.full.Part S.primary (here f) (fun i _ => pays g α i) j ↔
      ∃ C : ℝ, 0<C ∧ ∃ b : ℕ, ∀ i x, x ∈ S.window i → ∀ p,
        ‖iteratedFDeriv ℝ j (f i x) p‖ ≤
          C * (S.logPart i * (1+x) * (1+exp x * ‖p‖))^b * (g i * exp ((α+j)*x)) := by
    unfold Cost.Part Cost.Le; dsimp only [Scale.full, Scale.weight, pays, primary, here]
    simp_rw [← Real.exp_nat_mul, mul_assoc (g (index _)), ← Real.exp_add, add_mul α]
    refine exists_congr fun C => and_congr_right fun h => exists_congr fun b => ?_
    exact ⟨fun h i x hx p => h (S.choose i x hx) p (mem_univ _), fun h i p _ => h (index i) (t i) i.mem p⟩

/-- Every momentum-derivative identity being used before integration in scale. -/
def Along (f H : ι → ℝ → E → F) (j : ℕ) := ∀ i r, r ∈ S.window i → ∀ p,
   HasDerivWithinAt (fun u => iteratedFDeriv ℝ j (f i u) p) (iteratedFDeriv ℝ j (H i r) p) (S.window i) r
section
variable {f H : ι → ℝ → E → F} {g : ι → ℝ} {α : ℝ} {j : ℕ}
   (hg : ∀ i, 0 ≤ g i) (hd : S.Along f H j) (hp : S.primary.full.Part S.primary (here H) (fun i _ => pays g α i) j)
include hg hd hp

/-- Irrelevant and strictly marginal derivatives integrate without a Taylor condition. -/
lemma forward (hi : S.dawn.full.Part S.dawn (fun i=> f i (S.beg i)) (fun i _ => g i * exp (α * S.beg i)) j)
     (hs : 0 ≤ α+j) : S.primary.full.Part S.primary (here f) (fun i _ => pays g α i) j := by
  obtain ⟨C,hC,b,Hb⟩:= (testPart S).1 hp
  obtain ⟨A,hA,a,h⟩:= hi
  refine (testPart S).2 ⟨A+C,by positivity, max a (b+1), fun i x hx p=>?_⟩
  let U (y : ℝ) := S.logPart i*(1+y)*(1+exp y * ‖p‖)
  let W (r : ℝ) := g i * exp ((α+j)*r)
  let P (r : ℝ) := iteratedFDeriv ℝ j (f i r) p
  have hG := hg i; have hb := S.lg i; have hv := S.beg_nn i
  have hW (r : ℝ) : 0 ≤ W r := by unfold W; positivity
  have hU {r : ℝ} (hr : 0 ≤ r) : 1+r ≤ U r := by
     unfold U
     trans 1*(1+r)*1
     · simp
     gcongr
     exact le_add_of_nonneg_right (by positivity)
  have hey {r s : ℝ} (hr : 0 ≤ r) (he : r ≤ s) : U r ≤ U s:= by have hss:=hr.trans he; unfold U; gcongr
  have hmono : Monotone W := fun _ _ h => mul_le_mul_of_nonneg_left (LogTime.mono _ hs h) hG
  have he' : S.beg i ≤ x := S.ci i hx
  have hx' := hv.trans he'
  have hl := (S.ord i).out (S.used i) hx
  let K := C* (U x)^b * W x
  have hD : ‖P x-P (S.beg i)‖ ≤ K*(x-S.beg i) := by
    refine norm_image_sub_le_of_norm_deriv_le_segment' (fun r hr => (hd i r (hl hr) p).mono hl) (fun r hr => (Hb i r (hl (Ico_subset_Icc_self hr)) p).trans ?_) x ⟨he',le_rfl⟩
    change C*(U r)^b * W r ≤ _
    have ht := hv.trans hr.1
    have ht' := (show 1+r ≤ U r from hU ht); have hu : 0 ≤ U r := by linarith
    have := hW x
    unfold K; gcongr
    exact hey ht hr.2.le
    exact hmono hr.2.le
  have h0 : ‖P (S.beg i)‖ ≤ A * (U (S.beg i))^a * W (S.beg i) := by
    unfold W; rw [add_mul,exp_add,exp_nat_mul,← mul_assoc (g i)]
    exact h i p (mem_univ _)
  have hz := hU hx'; have hpos : 1 ≤ U x:= by linarith
  have ht := hW x
  change ‖P x‖ ≤ (A+C)* _ * W x
  rw [add_mul A,add_mul]
  change _ ≤ A*(U x)^_ * W x + C*(U x)^_* W x
  apply (show ‖P x‖ ≤ ‖P (S.beg i)‖+‖P x-P (S.beg i)‖ from by
    simpa only [add_sub_cancel, add_sub_cancel_left, sub_add_cancel, add_comm] using norm_add_le (P x - P (S.beg i)) (P (S.beg i))).trans
  apply add_le_add (h0.trans ?_) (hD.trans ?_)
  · trans A*(U x)^a*W x
    · have hy : 0 ≤ U (S.beg i) := le_trans (by positivity) (hU hv)
      gcongr; exact hey hv he'; exact hmono he'
    gcongr
    exact le_max_left ..
  calc
    K* (x-S.beg i) ≤ K * U x := by apply mul_le_mul_of_nonneg_left (by linarith) (by unfold K; positivity)
    _ = C* (U x)^(b+1)*W x := by unfold K; ring
    _ ≤ _ := by gcongr; exact le_max_right ..

variable (hsmall : α+(j:ℝ)<0) (hi : ∀ i : ι, S.window i=Ici (S.beg i))
include hi hsmall

/-- The Taylor limit that will need adjusting (or must vanish by closure). -/
lemma needs_limit [CompleteSpace F] (i : ι) : ∃ l, Tendsto (fun t => iteratedFDeriv ℝ j (f i t) 0) atTop (𝓝 l) := by
  obtain ⟨C,hC,b,h⟩:= (testPart S).1 hp
  let K:= C*S.logPart i^b*g i
  have hG:= hg i; have hL:=S.lg i
  refine limits (b:=-(α+(j:ℝ))) (s:=S.beg i) (C:=K) (by linarith) (S.beg_nn i) (by unfold K; positivity) b _ (fun r=> iteratedFDeriv ℝ j (H i r) 0) ?_ ?_
  · intro t hx
    exact (hd i t (by rwa [hi]) 0).mono (by rw [hi])
  intro t hx; apply (h i t (by rwa [hi]) 0).trans
  simp only [polyExp,K, norm_zero,mul_zero, add_zero, mul_one, mul_pow, neg_neg]
  apply le_of_eq; ring

/-- Decay at zero momentum once matched, uniform in all approved parameters. -/
lemma jet_origin (ht : ∀ i, Tendsto (fun t => iteratedFDeriv ℝ j (f i t) 0) atTop (𝓝 0)) :
    S.primary.full.Le (fun i (_p : E) => ‖iteratedFDeriv ℝ j (here f i) 0‖) (fun i _ => pays g α i * S.primary.length i ^ j) := by
  obtain ⟨C,hC,b,h⟩ := (testPart S).1 hp
  obtain ⟨D,hD,hb⟩:= backward_cost (b:=-(α+j)) (E:=E [×j]→L[ℝ] F) (by linarith) b
  refine ⟨C*D,by positivity,b,fun i p _=>?_⟩
  let l:= index i
  let a:= t i
  have ha : 0≤ a := (S.beg_nn l).trans i.ge
  have hg:=hg l; have he:=S.lg l
  let K:= C*S.logPart l ^ b * g l; have hK : 0≤K := by unfold K; positivity
  let F (u : ℝ) := iteratedFDeriv ℝ j (f l u) 0
  have hE : Tendsto (fun b => dist (F a) (F b)) atTop (𝓝 (‖F a‖)) := by simpa [F] using tendsto_const_nhds (x:=F a)|>.dist (ht l)
  have hw : ∀ᶠ c : ℝ in atTop, dist (F a) (F c) ≤ K*D*polyExp (-(α+j)) b a := by
    filter_upwards [eventually_ge_atTop a] with c hc
    have hl : Icc a c ⊆ S.window l := subset_trans Icc_subset_Ici_self (by rw [hi]; exact Ici_subset_Ici.mpr i.ge)
    refine hb a c K ha hc hK F (fun r=>iteratedFDeriv ℝ j (H l r) 0) (fun r hr=>(hd l r (hl hr) 0).mono hl) (fun r hr=>?_)
    apply (h l r (hl (Ico_subset_Icc_self hr)) 0).trans
    apply le_of_eq; simp only [polyExp, K, norm_zero, mul_zero, add_zero, mul_one, mul_pow, neg_neg]; ring
  let x:= S.primary.weight i p
  have hz : 1≤x := S.primary.one_le_weight i p
  apply le_trans (le_of_tendsto hE hw)
  change _ ≤ C*D * (S.logPart l*(1+a)* x)^b*(g l * exp (α*a)*exp a^j)
  calc
    _ = C*D*(S.logPart l*(1+a))^b*(g l * exp (α*a)*exp a^j) := by
       unfold K polyExp; rw [neg_neg,add_mul α, exp_add, exp_nat_mul,mul_pow]; ring
    _ ≤ _ := by
       have hw: S.logPart l*(1+a) ≤ S.logPart l*(1+a)*x:= le_mul_of_one_le_right (by positivity) hz
       exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hw _) (by positivity)) (by positivity)
end

/-- Scalar momentum comparison. `α` includes the desired gain.
Every negative-rate jet must actually have been compared at zero momentum. -/
theorem comparison {f H : ι → ℝ → E → F} {g : ι → ℝ} {α : ℝ}
    (hg : ∀ i, 0 ≤ g i) (hi : ∀ i : ι, S.window i=Ici (S.beg i))
    (hd : ∀ j, S.Along f H j)
    (hS : ∀ u : S.Inst, ContDiff ℝ ∞ (here f u))
    (hp : Bound S.primary (here H) (pays g α))
    (h0 : Bound S.dawn (fun i=> f i (S.beg i)) (fun i=> pays g α (S.start i)))
    (ht : ∀ j : ℕ, α+j<0 → ∀ i, Tendsto (fun t => iteratedFDeriv ℝ j (f i t) 0) atTop (𝓝 0)) : Bound S.primary (here f) (pays g α) := by
  refine ⟨hS,fun j=>?_⟩; obtain ⟨M,hM⟩ := exists_nat_gt (-α)
  generalize hh : max M j = k; have hj : j≤k:= hh ▸ le_max_right ..
  have hk : 0 ≤ α + k:= by
     have : (M:ℝ)≤k:= by exact_mod_cast (hh ▸ le_max_left M j : M ≤ k)
     linarith
  clear hh
  induction hj using Nat.decreasingInduction with
  | self => exact forward S hg (hd k) (hp.quoted k) (h0.quoted k) hk
  | of_succ j hj IH =>
     rcases lt_or_ge (α+j) 0 with he|he
     · exact lower_jet S.primary hS (jet_origin S hg (hd j) (hp.quoted j) he hi (ht j he)) IH
     exact forward S hg (hd j) (hp.quoted j) (h0.quoted j) he
end IntervalFamily
end YM.MS.LogTime
