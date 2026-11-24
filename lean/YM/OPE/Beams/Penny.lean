import YM.OPE.Beams.Lift
/-!
# Geometric contour costs. Does not require any of the common exterior
indices of multiple views to match during the argument. It does use full
polynomial extent along ALL the necessary simultaneous directions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Log.Reels
open Function Filter Finset MeasureTheory Lattice RG Wilson Metric Polar
open scoped Classical Topology ContDiff BigOperators
variable {G:Gauge}{C:Family G} {F:Extraction.Order}{S:Table C.book}(U:Spec.Final C F S)
variable {I J L Z:Type}[Fintype I][DecidableEq I][Fintype J][DecidableEq J]{f:Filter L}
    {x:L→ (I→ E4)→ J→ E4}{T:L→ℝ}{a b d:ℝ}{v:I}{j k:J}
    (p:J→ C.book.Token)
variable (ht:Tendsto T f atTop)
local notation "X'"=> (I→ E4)
def jacket (T:ℝ):= Real.exp (-(3*T))
include ht in
lemma jacket_price : RateIs f T (fun i=> jacket (T i)) (-3):= by
    apply (RateIs.exp _ ht).congr; filter_upwards with i; unfold jacket; rw [neg_mul]
lemma jacket_pos (x:ℝ):0 < jacket x:=Real.exp_pos _
include U ht in
lemma umbrella (P:Finset Ortho)(hp:0<a): ∀ᶠ i in f,∀ k∈ P,∀ (x:J→ E4) (q:J→ℝ), Reserve k x q (jacket (T i)) → ∃ F:ℂ→ℂ, (∀ z∈closedBall (0:ℂ) 1,DifferentiableAt ℂ F z)∧(∀ s:ℝ,|s| ≤ 1 → Injective (along x k q s) ∧ F (s:ℂ)=observe S (along x k q s) p) ∧∀ z∈closedBall (0:ℂ) 1, ‖F z‖ ≤ Real.exp (a*T i^2) :=by
    refine (eventually_all_finset P).2 (fun k _=>?_); obtain ⟨c,d,hc,h⟩:= reserve_price U p k; let x:= (d:ℝ)*3+1;
    have hx: 0+(d:ℝ)*(- (-3:ℝ)) < x:= by unfold x; linarith only
    filter_upwards [((RateLE.const c ht).mul (((jacket_price ht).inv.power d).pays ht)) x hx,ht.eventually_ge_atTop 0,ht.eventually_ge_atTop (x/a), ((jacket_price ht).tends (by norm_num) ht).eventually (ge_mem_nhds zero_lt_one)] with i hy hr hV hi u v hu; obtain ⟨F,hf,hh,hK⟩:=h u v (jacket (T i)) (jacket_pos _) hi hu
    refine ⟨F,hf,hh,fun z hz=> (hK z hz).trans (le_trans ((Real.le_norm_self _).trans hy) (Real.exp_monotone (?_ )))⟩; nlinarith only [mul_le_mul_of_nonneg_left ((div_le_iff₀ hp).mp hV) hr]
structure Film (f:Filter L)(T:L→ℝ)(x:L→ (I→ E4)→J→ E4)(v:L→ I→J→ℝ) : Prop where
    unfolds i : Differentiable ℝ (x i)
    constant (i:L)(z:I→ E4)(k:Ortho)(a:I)(t:ℝ): x i (z+t • ray a k)=along (x i z) k (v i a) t
    opens a j l: j≠l → ∀ y>0,∀ᶠ i in f,∀ z:I→ E4,‖z‖ ≤ 1 → |v i a j-v i a l|+jacket (T i) ≤ y*‖x i z j-x i z l‖
variable {y:L→ I→ J→ℝ}
namespace Film
variable (h:Film f T x y)
include h
lemma inject (a:I) : ∀ᶠ i in f,∀ z:I→E4,‖z‖ ≤ 1 → Injective (x i z):=by
    filter_upwards [eventually_all.mpr fun j:J=>eventually_all.mpr fun k:J=>eventually_all.mpr fun h':j≠k=> h.opens a j k h' 1 one_pos] with i hi z hz j k ht; by_contra he; have hp:= add_pos_of_nonneg_of_pos (abs_nonneg (y i a j-y i a k)) (jacket_pos (T i))|>.trans_le (hi j k he z hz); rw [ht,sub_self,norm_zero,mul_zero] at hp; exact lt_irrefl _ hp
include U ht in
lemma budgets (a:I) : Lent (f:=f) (T:=T) (F:=fun i z=> if Injective (x i z) then observe S (x i z) p else 0):=by
    let F i (z:I→ E4) : ℂ:=if Injective (x i z) then observe S (x i z) p else 0; let Y':Rear I L:= ⟨J,x⟩; refine ⟨Unit,inferInstance,(fun _=>Y'),?_,fun _=> h.inject a,fun K u a hu ha v=>?_⟩
    · filter_upwards [h.inject a] with i hi z hz; let f(z):= x i z; have hp:=hi z hz; have hx:= observeDiff S p U.room.kernel.smooth hp; have hf:F i=ᶠ[𝓝 z] fun z=> observe S (x i z) p:=( ((h.unfolds i).continuous.continuousAt (x:=z)).tendsto.eventually (open_inj.mem_nhds hp)).mono fun z hi=>if_pos hi
      exact (hx.comp z (h.unfolds i z)).congr_of_eventuallyEq hf
    filter_upwards [umbrella U p ht K ha,eventually_all.mpr fun j:J=>eventually_all.mpr fun k:J=>eventually_all.mpr fun h':j≠k=>h.opens v j k h' u hu] with i hx hv z hz k hk hh; obtain ⟨X,hX,hA,hB⟩:= hx k hk (x i z) (y i v) ⟨fun j k h=> (hv j k h z hz).trans (hh () j k)⟩; refine ⟨X,hX,fun t he=>?_,hB⟩; obtain ⟨hZ,hΩ⟩:=hA t he; change _ = F i _; unfold F; rw [h.constant i z k v t,if_pos hZ]; exact hΩ
end Film
end YM.OPE.Log.Reels
