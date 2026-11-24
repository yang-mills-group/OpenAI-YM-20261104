import YM.OPE.Compatible.Atlas.Traffic
/-!
# exponential budget (not poly here), all path values along one scanned variable
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal.Trace
open Function Set Filter MeasureTheory FrameRead Lattice RG Boundary EveryPhase
open scoped Topology BigOperators Classical
variable {X V:Type}[PartialOrder X][OrderBot X][Fintype X](D:Origin X)(Q:Finset X)
variable {G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}{U: Spec.Final C F S}
variable {ψ:Filter V}{T:V→ℝ} (s:V→X→ℝ)
structure ClearTime (D: Origin X)(Q: Finset X)(ψ:Filter V)(s:V→ X→ℝ): Prop where
   crown : Crown Q
   lit : ∀ᶠ i in ψ, Bright Q (s i)
-- reusable
lemma Shines.plus {R A B:ℝ}{f g:ℝ→ℂ}(h:Shines R A f)(hf:Shines R B g): Shines R (A+B) (fun x=>f x + g x):=by
    obtain ⟨x,ha,hx,he⟩:=h; obtain ⟨y,hb,hy,hf⟩:=hf; exact ⟨_, ha.fun_add hb, fun i hi=>congr_arg₂ _ (hx _ hi) (hy _ hi), fun z hz=> (norm_add_le ..).trans (add_le_add (he _ hz) (hf _ hz))⟩
lemma Shines.times {R A B:ℝ}{f g:ℝ→ℂ}(h:Shines R A f)(hf:Shines R B g): Shines R (A*B) (fun x=> f x * g x):=by
    obtain ⟨x,ha,hx,he⟩:=h; obtain ⟨y,hb,hy,hf⟩:=hf; refine ⟨fun x'=> x x'*y x', ha.mul hb, fun i hi=>congr_arg₂ _ (hx _ hi) (hy _ hi), fun z hz=> ?_⟩; rw [norm_mul]; exact mul_le_mul (he _ hz) (hf _ hz) (norm_nonneg _) ((norm_nonneg _).trans (he _ hz))
lemma Shines.lift {R A B:ℝ}{f:ℝ→ℂ}(h:Shines R A f)(hf:A ≤ B): Shines R B f:=by obtain ⟨x,hx,he,ha⟩:=h; exact ⟨x,hx,he,fun _ hb=>(ha _ hb).trans hf⟩
variable (A: Atom U X V)(g:Sight)(H:Tendsto T ψ atTop)(h: ClearTime D Q ψ s)
variable {c d η ρ M:ℝ}
set_option quotPrecheck false
local notation "x!"=>fun i (z:X→ E4) f (w:Wing D Q) t=> reload D Q (s i) g z (Function.update f w t)
include h H
lemma passes (hc: 0<c) (hd:0<d)(he:0<η)(hρ:0<ρ)(hM:∀ i, ‖FrameRead.trail (g.code i)‖ ≤ M)(h0:0 ≤ M)(hp:(Fintype.card (Wing D Q):ℝ)*(M*ρ) ≤ c/2*η) : ∃ v:ℝ, ∀ᶠ i in ψ, ∀ x:X→E4, A.Quota D Q (s i) i x η (Real.exp (-d*T i)) → A.Designed i x g c → ∀ f:Wing D Q →ℝ,(∀ i,|f i| ≤ ρ) → ∀ w, Shines ρ (Real.exp (v*T i)) (fun t=>A.read i (x! i x f w t)) :=by
    obtain ⟨L⟩:= almanac U; let k i:= c * Real.exp (-d*T i)/2; have hv(i):0< k i:=by unfold k; positivity
    have ht : ∀ᶠ i in ψ,k i ≤ 1:=by refine (show Tendsto k ψ (𝓝 0) from ?_).eventually (p:=fun i=> i≤1) (ge_mem_nhds zero_lt_one); simpa only [k,mul_zero,zero_div,Function.comp_apply] using (((Real.tendsto_exp_atBot.comp (Tendsto.const_mul_atTop_of_neg (neg_lt_zero.mpr hd) H)).const_mul c).div_const 2)
    let W:= Axis × Equiv.Perm (Fin A.n); choose m b hb hz using fun j:W=> shining_path L A.p (g.code j.fst) j.snd; let a(j:W)(i:V):= b j* (k i)⁻¹^(m j)
    have hh(j:W): ∃ c:ℝ, RateLE ψ T (a j) c:=by
       have hf :∀ i,(k i)⁻¹=2/c * Real.exp (d*T i) :=by intro i; unfold k; rw [neg_mul,Real.exp_neg]; field_simp
       have hx:RateLE ψ T (fun i=>2/c * Real.exp (d*T i)) (0+d):=(RateLE.const (2/c) H).mul (RateLE.exp d H); exact ⟨_, (RateLE.const (b j) H).mul ((hx.congr (Eventually.of_forall fun i=>(hf i).symm)).pow (m j) H)⟩
    choose c' hC using hh; haveI : Nonempty W:=⟨0,Equiv.refl _⟩; let v:ℝ:=Finset.univ.sup' Finset.univ_nonempty c' + 1; have hE : ∀ j:W,c' j < v:=fun j=> lt_of_le_of_lt (Finset.le_sup' c' (Finset.mem_univ j)) (lt_add_one _)
    refine ⟨v,?_⟩; filter_upwards [eventually_all.mpr fun j=> hC j v (hE j),ht,h.lit] with i hi hp' hφ x hA hZ f hf w
    obtain ⟨e,hei⟩:=Atom.toned D Q (s i) i x h.crown hφ A g hA hZ he hρ.le hc (Real.exp_pos _) hM h0 hp w.snd
    let j:W:= (w.snd,e); let t(z:ℝ)(l:Fin A.n):= A.pose i (x! i x f w z) l; let u (l:Fin A.n) := if inMotion D Q w (A.hang l) then s i (par D w.1.1) else 0
    refine Shines.lift (B:=Real.exp _) (hz j (A.r i) t u ?_ (k i) ρ ⟨hv _,hp'⟩ ?_) ((Real.le_norm_self _).trans (hi j))
    · intro t' l; change reload D Q (s i) g x (Function.update f w t') (A.hang l) +_= _; rw [differential]; change _+_+_=_+_+_; rw [add_right_comm]; -- same
    intro t' ht; exact hei _ (fun u=> by
       by_cases h:w=u; subst u; · rwa [update_self]
       rw [Function.update_of_ne (Ne.symm h)]; exact hf _)
end YM.OPE.Arboreal.Trace
