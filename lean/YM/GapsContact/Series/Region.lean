import YM.GapsContact.Series.Price
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-! # Currying two-scale prices inside ANY open connected region. -/
set_option autoImplicit false
noncomputable section
namespace YM.GapsContact.Pattern
open Function Filter Set Metric
open scoped Topology BigOperators ContDiff Classical
variable {ι Ω:Type*} {E H:Type} [NormedAddCommGroup E] [NormedAddCommGroup H]
variable {f:Filter Ω} {T:Filter ι} {A:ι→Ω→E→ H} {U R V K:Set E} {x:E} {p:Ω→ℝ} {r:ℝ}

lemma finite_tags {α J:Type*} {F:ι→Ω→J→H}{S:α→ Set J}(s:Finset α)(hw:∀ᶠ i in f,0≤p i)(h:∀ α∈s,∀ᶠ q in T,TagPrice f (F q) (S α) p):∀ᶠ q in T,TagPrice f (F q) (⋃ i∈s,S i) p:=by
   induction s using Finset.induction_on with
   | empty => exact Eventually.of_forall fun _=> ⟨1,zero_le_one,Eventually.of_forall fun _=>by simp⟩
   | insert a s _ ih => simp_rw [Finset.set_biUnion_insert]; exact ((ih fun i hi=> h i (Finset.mem_insert_of_mem hi)).and (h a (Finset.mem_insert_self ..))).mono fun _ h=>h.2.union h.1 hw
lemma local_compact (hk:IsCompact K) (hw:∀ᶠ i in f,0≤p i) (hK : ∀ x∈K, ∃ R:Set E, IsOpen R ∧ x∈ R ∧ ∀ᶠ q in T,TagPrice f (A q) R p) : ∀ᶠ q in T,TagPrice f (A q) K p:= by
   choose R hR hx ht using fun z:K=> hK z.val z.property
   obtain ⟨s,hs⟩:= hk.elim_finite_subcover R hR fun x hx'=> Set.mem_iUnion.mpr ⟨⟨x,hx'⟩, hx _⟩
   exact (finite_tags s hw (fun i _=> ht i)).mono fun _ h=> h.parent hs
lemma TagPrice.patch {F:Ω→ E→ H}(hk:IsCompact K)(hw:∀ᶠ i in f,0≤p i)(hK:∀ x∈K,∃ R:Set E,IsOpen R ∧ x∈R ∧ TagPrice f F R p) : TagPrice f F K p:=by
   obtain ⟨v,h⟩:= (local_compact hk (T:=atTop) hw (A:=fun _ : ℕ => F) (fun x hx=> by obtain ⟨R,hR,ha,hX⟩:= hK x hx; exact ⟨R,hR,ha,Eventually.of_forall fun _=>hX⟩)).exists; exact h

variable [NormedSpace ℂ E] [NormedSpace ℂ H]

-- Budget independent of `T`: compact prices at large q, exponent chosen before q
structure Support (A:ι→Ω→E→H)(T:Filter ι)(f:Filter Ω)(u:Ω→ℝ)(U:Set E) : Prop where
    hol : ∀ᶠ q in T,∀ᶠ i in f, AnalyticOnNhd ℂ (A q i) U
    high : ∀ K:Set E,IsCompact K→K⊆U→∃ b:ℕ,∀ᶠ q in T,TagPrice f (A q) K (fun i=> (u i)⁻¹^b)
    positive : ∀ᶠ i in f,0 < u i

def Ready (A:ι→Ω→E→H)(T:Filter ι)(f:Filter Ω)(u:Ω→ℝ)(K:Set E) := ∀ a:ℕ,∀ᶠ q in T,TagPrice f (A q) K (fun i=> u i^a)

def Live (A:ι→Ω→E→H)(T:Filter ι)(f:Filter Ω)(u:Ω→ℝ)(U:Set E) := {x| ∃ r:ℝ, 0<r ∧ closedBall x r⊆U ∧ Ready A T f u (closedBall x r)}
variable (h : Support A T f p U)
omit [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℂ H] in
lemma Ready.mono (h:Ready A T f p K)(hx:R⊆K):Ready A T f p R:= fun a=> (h a).mono fun _ H=> H.parent hx
include h in
lemma Support.carries (hC:IsCompact R)(hx: R ⊆ U)(hu: Covered K R V)(he:Ready A T f p K): Ready A T f p V:=by
   obtain ⟨b,hB⟩:= h.high _ hC hx; intro a; filter_upwards [he (2*a+b),h.hol,hB] with q hA hQ hB
   exact TagPrice.handle h.positive hu (hQ.mono fun i ht=>ht.mono hx) hA hB

omit [NormedSpace ℂ H] [NormedSpace ℂ E] in
lemma open_live (A:ι→Ω→E→H)(T:Filter ι)(f:Filter Ω)(p:Ω→ℝ)(U:Set E):IsOpen (Live A T f p U):=by
   apply isOpen_iff_mem_nhds.mpr; rintro x ⟨r,hr,hs,hK⟩; refine mem_of_superset (ball_mem_nhds x hr) ?_; intro y hy
   obtain ⟨R,hR,hx⟩:= Metric.mem_nhds_iff.mp (isOpen_ball.mem_nhds hy)
   have ht : closedBall y (R/2) ⊆ closedBall x r := (closedBall_subset_ball (half_lt_self hR)).trans (hx.trans ball_subset_closedBall)
   exact ⟨R/2,half_pos hR, ht.trans hs,hK.mono ht⟩
variable [ProperSpace E] -- finite dimensions in use
include h in
lemma Support.enlarge (hk:x∈ Live A T f p U)(hp:0<r)(hr:closedBall x (4*r) ⊆ U):Ready A T f p (closedBall x r):=by
   obtain ⟨d,hd,hU,hD⟩:=hk
   let a(n:ℕ):= r*(2:ℝ)⁻¹^n; have he(n):0<a n:=by unfold a; positivity
   have hs(n):a n≤r:= mul_le_of_le_one_right hp.le (pow_le_one₀ (by norm_num) (by norm_num))
   have ht(n)(hA:Ready A T f p (closedBall x (a (n+1)))): Ready A T f p (closedBall x (a n)):=by
       have hx:a n=2*a (n+1):=by unfold a; rw [pow_succ]; ring; -- rw occurrence avoids rewriting right
       nth_rw 1 [hx]; exact h.carries (isCompact_closedBall _ (4*a (n+1))) ((closedBall_subset_closedBall (mul_le_mul_of_nonneg_left (hs _) (by norm_num : (0:ℝ) ≤ 4))).trans hr) (dilate _ (he _) _) hA
   obtain ⟨n,hn⟩:= ((show Tendsto a atTop (𝓝 0) from by simpa [a] using (tendsto_pow_atTop_nhds_zero_of_lt_one (r:=(2:ℝ)⁻¹) (by norm_num) (by norm_num)).const_mul r).eventually_lt_const hd).exists
   have hy(n:ℕ)(hp:Ready A T f p (closedBall x (a n))) : Ready A T f p (closedBall x r):= by induction n with | zero=> simpa [a] using hp | succ n ih=> exact ih (ht n hp)
   exact hy n (hD.mono (closedBall_subset_closedBall hn.le))

include h in
lemma Support.live (hx:IsOpen U)(hc:IsPreconnected U)(hμ:(Live A T f p U).Nonempty): U⊆ Live A T f p U:=by
   obtain ⟨x,hx'⟩:= hμ
   refine hc.subset_of_closure_inter_subset (open_live ..) ⟨x,?_,hx'⟩ ?_
   · obtain ⟨r,hr,hR,-⟩:=hx'; exact hR (mem_closedBall_self hr.le)
   intro x ⟨hk,hx'⟩; obtain ⟨r,hr,hR⟩:= Metric.mem_nhds_iff.mp (hx.mem_nhds hx')
   let d:=r/16; have hd:0<d:=by unfold d; positivity
   obtain ⟨y,hy,hV⟩:= _root_.mem_closure_iff.mp hk _ isOpen_ball (mem_ball_self (x:=x) hd)
   have he:dist y x<d:=hy
   have hB: closedBall y (4*(2*d)) ⊆ U:= fun z hz=> by
      apply hR; apply mem_ball.mpr; apply lt_of_le_of_lt (dist_triangle z y x); unfold d at *; linarith [mem_closedBall.mp hz]
   have hT:closedBall x d ⊆ closedBall y (2*d):= fun z hz=> by
      rw [dist_comm y] at he; exact (dist_triangle z x y).trans (by linarith [mem_closedBall.mp hz])
   exact ⟨d,hd, hT.trans ((closedBall_subset_closedBall (by linarith : 2*d ≤ 4*(2*d))).trans hB), (h.enlarge hV (by positivity) hB).mono hT⟩
include h in
lemma Support.body (hx:IsOpen U)(hc:IsPreconnected U)(hm:(Live A T f p U).Nonempty)(hK:IsCompact K)(hu:K⊆U):Ready A T f p K:=by
   intro i; apply local_compact hK (h.positive.mono (fun x hx=>pow_nonneg hx.le i))
   intro y hy; obtain ⟨r,hr,hR,h⟩:= h.live hx hc hm (hu hy)
   exact ⟨ball y r,isOpen_ball,mem_ball_self hr,h.mono ball_subset_closedBall i⟩

-- generic derivative price helper. First order Cauchy, iterate inverse shrink loss.
variable {F:Ω→E→H}
omit [ProperSpace E] in
lemma fderiv_budget {f:E→H}{C r:ℝ}(hr:0<r)(hC:0≤C)(hf:AnalyticOnNhd ℂ f (closedBall x r))(he:∀ y∈closedBall x r,‖f y‖≤C): ‖fderiv ℂ f x‖≤C/r:=by
   let Y:= fderiv ℂ f x
   apply ContinuousLinearMap.opNorm_le_bound _ (by positivity); intro y
   by_cases h:y=0
   · simp [h]
   have ht:= norm_pos_iff.mpr h; let q:= r / ‖y‖; have hq:0<q:=by unfold q; positivity
   let g(t:ℂ):= x+t • y; have hg : Differentiable ℂ g:=by unfold g; fun_prop
   have hh : MapsTo g (closedBall 0 q) (closedBall x r):= fun z hz=> show dist _ _ ≤ _ from (by
      unfold g; rw [dist_eq_norm,add_sub_cancel_left,norm_smul]; exact ((le_div_iff₀ ht).mp (mem_closedBall_zero_iff.mp hz)))
   have hu := hf.differentiableOn.comp hg.differentiableOn hh
   have hg0:g 0=x:=by simp[g]
   have hp: Y y=deriv (f ∘ g) 0:=by
      symm; apply HasDerivAt.deriv
      exact ((hf x (mem_closedBall_self hr.le)).differentiableAt.hasFDerivAt.comp_hasDerivAt_of_eq (0:ℂ) (show HasDerivAt g y (0:ℂ) from (by simpa only [one_smul,zero_add,g] using! ((hasDerivAt_const (x:=(0:ℂ)) x).add ((hasDerivAt_id' (0:ℂ)).smul_const y)))) hg0.symm)
   have hY := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hq ⟨hu.mono ball_subset_closedBall,hu.continuousOn.mono closure_ball_subset_closedBall⟩ (fun z hz=> he _ (hh (sphere_subset_closedBall hz)))
   refine (le_of_eq (congr_arg norm hp)).trans (hY.trans_eq ?_); unfold q; field_simp

lemma Scoped.diff (h:Scoped f F U p)(hw:∀ᶠ i in f,0≤ p i)(hu:IsOpen U)(hh:∀ᶠ i in f,AnalyticOnNhd ℂ (F i) U): Scoped f (fun i=> fderiv ℂ (F i)) U p:=by
   intro K hK hs; apply TagPrice.patch hK hw; intro x hx
   obtain ⟨r,hr,hR⟩:= Metric.mem_nhds_iff.mp (hu.mem_nhds (hs hx))
   have hp: closedBall x (r/2) ⊆ U:= (closedBall_subset_ball (half_lt_self hr)).trans hR
   obtain ⟨C,hC,hB⟩:= h _ (isCompact_closedBall x (r/2)) hp
   refine ⟨ball x (r/4), isOpen_ball, mem_ball_self (by positivity), C/(r/4), by positivity,?_⟩
   filter_upwards [hB,hw,hh] with i hi hW hI y hy
   have hy' : closedBall y (r/4) ⊆ closedBall x (r/2):= fun z hz => by
      apply mem_closedBall.mpr; apply le_trans (dist_triangle z y x); linarith [mem_closedBall.mp hz, mem_ball.mp hy]
   exact (fderiv_budget (by positivity) (by positivity) (hI.mono (hy'.trans hp)) (fun z hz=> hi z (hy' hz))).trans_eq (by ring)
lemma Scoped.jet {J:Type}[NormedAddCommGroup J][NormedSpace ℂ J] [CompleteSpace J]{F:Ω→E→J} (h:Scoped f F U p)(hw:∀ᶠ i in f,0≤ p i)(hu:IsOpen U)(hh:∀ᶠ i in f,AnalyticOnNhd ℂ (F i) U)(j:ℕ): Scoped f (fun i=> iteratedFDeriv ℂ j (F i)) U p:=by
   induction j generalizing J with
   | zero => intro K hk he; simpa [TagPrice] using h K hk he
   | succ j ih =>
     intro K hk he; have hp:= ih (h.diff hw hu hh) (hh.mono fun i hi=> (fun x hx=> (hi x hx).fderiv)) K hk he
     simpa [TagPrice,norm_iteratedFDeriv_fderiv] using hp
end YM.GapsContact.Pattern
