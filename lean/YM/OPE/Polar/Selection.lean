import YM.OPE.Polar.Halo
/-!
# Captured tilted poles for a finite list
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Polar
open Function Set Filter MeasureTheory Metric Boundary
open scoped Topology BigOperators Classical
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(U:Spec.Final C f S) {I J : Type}[Fintype I][DecidableEq I][Fintype J] {K: J→ Type} [∀ i,Fintype (K i)]
local notation "P"=> {q:ℝ // 0<q}
private def differences (K : J→ Type) := (j:J) × {x:K j × K j// x.1≠ x.2}

variable (K) [∀ i,DecidableEq (K i)]
lemma chooseTilt (a:Axis)(ε:ℝ)(hε:0<ε): ∃ z:Finset Ortho, ∃ u>0, (∀ k∈z, ‖(forwards k).val-basis a‖<ε) ∧ ∀ (y:(j:J)→ K j→ E4), (∀ j,Injective (y j)) → ∃ k∈z,∀ (j:J)(x v:K j),
    u * ‖y j x-y j v‖ ≤ |time (Ortho.motion k (y j x))-time (Ortho.motion k (y j v))|:=by
    let F:= differences K; letI:Fintype F:= by unfold F differences; infer_instance
    obtain ⟨z,hz,he⟩:= watches (I:=F) a ε hε
    obtain ⟨u,hu,hv⟩:= ((show ∀ᶠ x in 𝓝[>] (0:ℝ),0 < x from self_mem_nhdsWithin).and ((eventually_all_finset z).2 (fun x hx=> (show ∀ᶠ t in 𝓝 (0:ℝ), t≤ x.2 from ge_mem_nhds (hz x hx|>.1)).filter_mono nhdsWithin_le_nhds))).exists
    refine ⟨z.image Prod.fst,u,hu,fun k hk=>by obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp hk; exact (hz _ hx).2,?_⟩
    intro y hy; let f : F→E4:= fun ⟨j,⟨(p,q),_⟩⟩=> y j p-y j q; obtain ⟨k,h,hK⟩:= he f (fun ⟨i,⟨(p,q),h⟩⟩=>sub_ne_zero.mpr ((hy i).ne h)); refine ⟨k.1,Finset.mem_image_of_mem _ h,fun j x v=>?_⟩
    by_cases hp:x=v; subst v; · simp
    apply le_trans (mul_le_mul_of_nonneg_right (hv k h) (norm_nonneg _)); rw [show time (Ortho.motion k.1 (y j x)) - time (Ortho.motion k.1 (y j v))= _ from (show _ =time (Ortho.motion k.1 (y j x-y j v)) from by rw [map_sub]; rfl)]; exact hK ⟨j,⟨(x,v),hp⟩⟩

variable {K}
local notation "K'"=> Ortho
variable (x:I→ E4)(q:I→ℝ) (p : I→ C.book.Token) {D t d:ℝ}
lemma sep_power (ht:0 < t)(hd:0<d)(hz:Apart d x)(k:K')(hh:∀ i j:I, t*‖x i-x j‖ ≤ |time (Ortho.motion k (x i))-time (Ortho.motion k (x j))|) (hp:∀ i, |q i| ≤ D) (hb:3*D ≤ t*d): Reserve k x q D:= by
    refine ⟨fun i j h=>?_⟩; have he : t*d ≤ t*‖x i-x j‖:= mul_le_mul_of_nonneg_left (hz i j h|>.le) ht.le; have hx' : |q i-q j| ≤ |q i|+|q j|:= abs_sub _ _ -- name
    linarith only [hx',hp i, hp j,he,hh i j,hb]

-- uniform on widths, under a rate and relative -a of definition.
variable {ι:Type*}{l:Filter ι}{T b:ι→ℝ}(z:Finset Ortho) {δ:ℝ}
include U
lemma tilted_radius (hT:Tendsto T l atTop) (hD:RateIs l T b (-δ))(hb:∀ᶠ i in l,b i ≤ 1) :
    ∀ᶠ i in l,∀ k∈z,∀ (x:I→E4) (q:I→ℝ), Reserve k x q (b i) → ∃ F:ℂ→ℂ, (∀ z∈closedBall (0:ℂ) 1,DifferentiableAt ℂ F z)∧(∀ s:ℝ,|s| ≤ 1 → Injective (along x k q s) ∧ F (s:ℂ)=observe S (along x k q s) p) ∧∀ z∈closedBall (0:ℂ) 1, ‖F z‖ ≤ Real.exp (T i^2/2) :=by
    refine (eventually_all_finset z).2 (fun k _=>?_); obtain ⟨c,d,hc,h⟩:= reserve_price U p k; let x:= (d:ℝ)*δ+1;
    have hp: 0+(d:ℝ)*(- - δ) < x:= by unfold x; linarith only
    filter_upwards [hb,hD.pos,((RateLE.const c hT).mul (hD.inv.power d|>.pays hT)) x hp,hT.eventually_ge_atTop 0,hT.eventually_ge_atTop (2*x)] with i hi hP hy hr hV u v hu; obtain ⟨F,hf,hh,hK⟩:=h u v (b i) hP hi hu
    refine ⟨F,hf,hh,fun z hz=> (hK z hz).trans (le_trans ((Real.le_norm_self _).trans hy) (Real.exp_monotone (?_ )))⟩; nlinarith only [mul_le_mul_of_nonneg_left hV hr]

end YM.OPE.Polar
