import YM.Comparison.RG02.Bare.Gap
/-!
# Real exponential cost to top

 A contour argument on the whole group is not available at g≠0. For top bare only, trace error
 of omitted *complement* at each fixed regulator/horizon by piling up Wilson energy+penalty
 with strictly positive gap on any such (punctured) slice. Constants here may be regulator-
 dependent, even in the core. Marked piece read with declared `Growth`, independent of density
 comparison. Extend to genuine period-by-period asymptotic of the pushed conditional. -/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Bare
open Function Filter Finset MeasureTheory Lattice Wilson Tree Pressure RG Integral Actual Precision Laplace
open PertExtension.Series PertExtension.Series.Tested
open YM.Push.SectorMeasure
open Marker Multi Exterior
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {n m : ℕ} {A : Type*}

-- polynomial growth (real positive rays only)
def Growth (F : ℝ→ A→ ℂ) (r : ℕ) := ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ t in along,∀ y, ‖F t y‖ ≤ C*(t⁻¹)^r
def Allows (F : ℝ→A→ℂ):= ∃ n,Growth F n
variable {F G : ℝ→A→ℂ}
lemma Growth.inc (h : Growth F n) (hm : n ≤ m) : Growth F m := by
   obtain ⟨C,hC,h⟩:=h
   refine ⟨C,hC,?_⟩; filter_upwards [eventually_small (t:=1) one_pos,h] with t ht hh a
   exact (hh a).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ((one_le_inv₀ ht.1).mpr ht.2.le) hm) hC)
lemma Allows.plus (h : Allows F) (H : Allows G) : Allows (F+G) := by
   obtain ⟨i,hi⟩:=h; obtain ⟨j,hj⟩:=H; let k:=max i j
   obtain ⟨C,hC,H⟩:= hi.inc (le_max_left i j); obtain ⟨D,hD,I⟩:= hj.inc (le_max_right i j)
   exact ⟨k,C+D,add_nonneg hC hD,(H.and I).mono fun t ⟨a,b⟩ x=> (norm_add_le (F t x) (G t x)).trans ((add_le_add (a x) (b x)).trans_eq (add_mul C D _).symm)⟩
lemma Allows.times (h : Allows F) (H : Allows G) : Allows (F*G) := by
   obtain ⟨i,C,hC,H'⟩:=h; obtain ⟨j,D,hD,I⟩:= H
   refine ⟨i+j,C*D,mul_nonneg hC hD,?_⟩; filter_upwards [H',I,eventually_pos] with t hi hj ht x
   simp only [Pi.mul_apply, norm_mul]; exact (mul_le_mul (hi _) (hj _) (norm_nonneg _) (by positivity)).trans_eq (by rw [pow_add]; ring)
lemma Allows.const (v : ℂ) : Allows (fun _ (_: A) => v) := ⟨0,‖v‖,norm_nonneg _,Eventually.of_forall fun t x=> by simp⟩ -- binder _:ℝ
lemma Allows.sum {I : Type*} (i : Finset I) (F : I → ℝ → A → ℂ) (h : ∀ j∈i,Allows (F j)) : Allows (∑ j∈i,F j):= by
   induction i using Finset.induction with
   | empty=>rw [sum_empty]; exact Allows.const _
   | insert x s hi ih=> rw [sum_insert hi]; exact (h x (mem_insert_self ..)).plus (ih fun x hx=> h x (mem_insert_of_mem hx))
lemma Allows.prod {I : Type*} (i : Finset I) (F : I→ℝ→A→ℂ) (h : ∀ j∈i,Allows (F j)): Allows (∏ j∈i,F j):= by
   induction i using Finset.induction with
   | empty => rw [prod_empty]; exact Allows.const _
   | insert x s hi ih=>rw [prod_insert hi]; exact (h x (mem_insert_self ..)).times (ih fun x hx=> h x (mem_insert_of_mem hx))
lemma Allows.divide (f : ℝ→ A→ ℂ) (h : Allows f) (n : ℕ) : Allows (fun g a=> (g^n)⁻¹ • f g a) := by
   simp_rw [Complex.real_smul]; let z:= (fun (g : ℝ) (_:A)=>Complex.ofReal (g^n)⁻¹)
   have he : Growth z n:=⟨1,zero_le_one,eventually_pos.mono fun g hg a=> by unfold z; rw [← inv_pow]; simp [abs_of_pos hg]⟩
   exact Allows.times (show Allows z from ⟨_,he⟩) h
section
variable {V : Type} [DecidableEq V] [Fintype V] {R : Census V} {c f : Side} {G : Gauge}
  {S : StepData c f} {O : ChartRatio G}
variable (W : Bulk.Colors R G f)
def Passes := fun u : ℝ => fun U : Config G f=> Poly.pass (markedLog u U W)
def Starts := ∀ i,Allows (W.mark i)
variable {W} (h : Starts W)
include h
lemma cost (s : R.Mode): Allows (fun t u=> (Passes W t u).part s):= by
   unfold Passes; simp_rw [fun t y=> Cumulants.pass_partition (markedLog t y W) (show (markedLog t y W).part R.quiet=0 from part_lit_quiet _)]; let F i t u:= (markedLog t u W).part (i:Hot R).val
   have he:= Allows.sum (shards R s) (fun j=> ∏ i∈j.val,F i) (fun j _=> Allows.prod j.val F (fun i _=> ?_))
   · convert he using 1; funext t u; simp only [Finset.prod_apply,Finset.sum_apply,F]
   unfold F markedLog; simp_rw [part_lit]; exact Allows.divide (W.mark i) (h i) _

variable (F : Forest S.ratio) (t : S.Choices) (A : Set (F.Slice G))
  (x : fieldDir G c 1)
  {p : Clip} {P : PathData G}
  (K : Bulk.Kernel S p P O)

local notation "d" => Fintype.card (Key F G)
local notation "ζ" g:max => YM.Next.Fluctuations.Sector.prefactor S G (temperature g)
/-- Top model's unnormalized full numerator. (At any step one can use bare and this kernel,
 same math result; only in later Top specialized to History true.) -/
def top (W : Bulk.Colors R G f) (g : ℝ) (U : Config G f) := Complex.ofReal (Wilson.bare (temperature g) U) • Passes W g U
local notation "Γ" g:max => Complex.ofReal (wage K F t g 0 x)
local notation "OUT" g:max y:max => Integral.outside F t g x A (top W g) y
omit h in
private lemma cost_identity (V : Config G c) (y : F.Slice G) (g : ℝ) :
    Actual.stack t V (temperature g) (top W g) (F.drape y) =
      (↑(ζ g*S.likelihood (F.drape y) t*Real.exp (-temperature g*pile F V y t)):ℂ) • Passes W g (F.drape y) := by
   unfold stack taggedKernel top Wilson.bare; rw [smul_smul,weight_formula,← Complex.ofReal_mul]; unfold pile; rw [mul_add, Real.exp_add]; ring_nf -- ring arguments inside Common exp? ok

omit h in
private lemma pay (δ : ℝ) (hδ : 0<δ) (k j : ℕ): ∃ C : ℝ, 0 ≤ C ∧ ∀ g : ℝ, 0<g → Real.exp (-temperature g * δ)*(g⁻¹)^k ≤ C*g^j := by
   obtain ⟨C,hC,h⟩:= Radial.bounded_exp hδ (k+j); refine ⟨C,hC,fun g hg=>?_⟩
   apply le_of_mul_le_mul_left (a:=(g⁻¹)^j) _ (by positivity)
   let I:=Real.exp (-δ * (g⁻¹)^2); have ht : Real.exp (-temperature g*δ)=I:=by unfold I temperature; rw [inv_pow]; ring_nf
   rw [ht]; calc
    _=(g⁻¹)^(k+j)*I:=by rw [pow_add];ring
    _ ≤ (1+g⁻¹)^(k+j)*I:= by apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le; gcongr; exact le_add_of_nonneg_left (by positivity)
    _ ≤ C:= h _ (by positivity)
    _ ≤ (g⁻¹)^j * (C*g^j):= by rw [mul_left_comm _ C,inv_pow, inv_mul_cancel₀ (pow_pos hg j).ne',mul_one]

lemma perpetual (s : R.Mode) (ha : IsOpen A) (hA : A∈𝓝 1) (k : ℕ) : Bill k (fun g=> ((Γ g)⁻¹ • charge (F.order G) (Integral.outside F t g x A (top W g))).part s):= by
    obtain ⟨δ,hp,H⟩:= chamber F t K.branches A hA ha
    have ht : Tendsto (fun t=> sample t x) along (𝓝 1):= by
       let f (t:ℝ):= represent (t • x)
       have hc:Continuous f:= by unfold f represent increment Exterior.collect; fun_prop
       have hx:= (hc.tendsto (0:ℝ)).mono_left (f:=f) (show along ≤ 𝓝 0 from nhdsWithin_le_nhds); rw [show f 0=1 by unfold f; rw [zero_smul,link_one]] at hx; exact hx
    obtain ⟨e,C,hC,hB⟩:= cost h s
    obtain ⟨b,hb,he⟩:= pay δ hp (e+d) k
    let T:=pad K F t 0 x
    have hT : 0<T:= pad_pos ..
    simp_rw [← Actual.smul_cost]; apply volume_bill k s (a:=fun _=>1) (fun _=> zero_le_one) (integrable_const (1:ℝ)) (C*T⁻¹*b) (by positivity)
    filter_upwards [eventually_pos,hB,ht.eventually H] with g hg hR hx y
    have hq : 0<ζ g:= YM.Next.Fluctuations.Sector.prefactor_pos _
    by_cases hi : y∈A; · simp [Integral.outside, Set.indicator_of_notMem (show y∉Aᶜ from by simp [hi])]; positivity
    let M := (ζ g : ℝ)
    let l:= S.likelihood (F.drape y) t
    let V' :=sample g x
    let hd := pile F V' y t
    let z:= Real.exp (-temperature g*hd)
    have hm : 0 ≤ temperature g:= by unfold temperature; positivity
    have hz : 0<z:= Real.exp_pos _
    have hl: 0 ≤ l:= S.likelihood_pos ..
    have hy:l≤1:= (single_le_sum (fun i (_:i∈Finset.univ)=> S.likelihood_pos (F.drape y) i) (Finset.mem_univ t)).trans_eq (S.chosen K.branches _)
    have hz': l*z ≤ Real.exp (-temperature g*δ):=(mul_le_of_le_one_left hz.le hy).trans (Real.exp_monotone (mul_le_mul_of_nonpos_left (hx y hi) (neg_nonpos.mpr hm)))
    simp only [Pi.smul_apply,Integral.outside, Set.indicator_of_mem ((show y∈Aᶜ from hi)),comp_apply, cost_identity ..,smul_smul, wages _ _ _ _ _ _ hg, ← Complex.ofReal_inv, ← Complex.ofReal_mul,Poly.part_smul]
    change ‖(↑((g^d*M*T)⁻¹*(M*l*z)):ℂ)* (Passes W g (F.drape y)).part s‖ ≤ _
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (by positivity : 0 ≤ (g^d*M*T)⁻¹*(M*l*z))]
    calc
      _ ≤ ((g^d*M*T)⁻¹*(M*l*z)) * (C*(g⁻¹)^e) := mul_le_mul_of_nonneg_left (hR _) (by positivity)
      _ = C*T⁻¹ * (l*z*(g⁻¹)^(e+d)) := by rw [pow_add,inv_pow,inv_pow]; have hv : M≠0:= hq.ne'; field_simp
      _ ≤ C*T⁻¹ * (b*g^k) := mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_right hz' (by positivity)).trans (he g hg)) (by positivity)
      _ = _ := by ring
end
end YM.Comparison.RG02.Bare
