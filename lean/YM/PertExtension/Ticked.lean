import YM.PertExtension.PolyFlow
import YM.PertExtension.BarePrescription
import YM.PertExtension.HueDepth

/-! Weighted lifting of a slot polynomial. A bound after multiplying by
its entire engineering power because the chosen projection is on tested
jets, not an identity of the original lattice polynomials. -/
set_option autoImplicit false
set_option maxHeartbeats 1250000
noncomputable section
namespace YM.PertExtension.Ticked
open Function Set Filter Finset RG Wilson Lattice Labels Source Drops Hue MvPolynomial Heat Heat.Top
open Next.Rank Next.Rank.Beamer Next.Rank.Configuration Bid Next.Rank.Perch Next.Rank.LiftMark Next.Rank.Normal Next.Rank PolyFlow
open scoped Topology ContDiff BigOperators
variable {G : Gauge}{d e:ℕ} {q : Label G d} {V:Type*}{f:V→Address G}{p:poly V}{ι:Type*}{r:ι→ℝ}{l:Filter ι}

lemma falling_cost {w k : ℕ}(hk:w<k)(hr : Tendsto r l atTop)(c:ℂ) : Tendsto (fun i=>(↑(r i):ℂ)^w* (((r i:ℂ)⁻¹)^k * c)) l (𝓝 0) := by
   let t(i):ℂ:=↑(r i)
   have h₀:Tendsto (fun i=>(t i)^w*((t i)⁻¹)^k) l (𝓝 0):=by
      have hv : Tendsto (fun i=> ((t i)⁻¹)^(k-w)) l (𝓝 ((0:ℂ)^(k-w))) :=by simpa only [Complex.ofReal_inv, Function.comp_apply,Pi.inv_apply,Complex.ofReal_zero] using! (Complex.continuous_ofReal.continuousAt.tendsto.comp hr.inv_tendsto_atTop).pow (k-w)
      rw [show (0:ℂ)^(k-w)=0 from by simp [show k-w≠0 by omega]] at hv
      apply hv.congr' <| (hr.eventually_gt_atTop 0).mono fun i hi=>?_; have hti : t i≠0:=Complex.ofReal_ne_zero.mpr hi.ne'
      nth_rw 2 [show k=w+(k-w) from by omega]; rw [pow_add,← mul_assoc,←mul_pow,mul_inv_cancel₀ hti,one_pow,one_mul]
   simp_rw [← mul_assoc]; simpa only [zero_mul] using! h₀.mul_const c

abbrev edge (he : d≤e)(q : Labels.Label G d) :poly (KeyIn G e ⊕ V):=rename Sum.inl (thawKey (raiseLabel G he q))

theorem peel_pure (he : d≤e){q : Labels.Label G d}{n:ℕ}(hq:pureDegree q.val d n)(a : ℂ):
    jets Configuration.bear a (edge (V:=V) he q)=(a^d) • edge (V:=V) he q := by
  unfold edge thawKey;rw [peel]
  have h : jets Labels.generation a q.val=a^d • q.val:= by
     ext i; classical
     rw [jets_coeff,coeff_smul]
     by_cases hi : coeff i q.val=0 <;> first | simp [hi] | skip
     have hy:= hq hi -- application fix
     rw [weight_slot] at hy
     exact congr_arg (fun k:ℕ×ℕ=> a^k.1) hy
  change rename Sum.inl (boundKey G e (jets _ a q.val))= a^d • rename _ (boundKey G e _)
  rw [h,map_smul,map_smul]; rfl

theorem earns {ι:Type*}{R:ι→ℝ}{l:Filter ι} (hR:Tendsto R l atTop)(he : d≤e)
    {q : Label G d}{n:ℕ}(hv:pureDegree q.val d n) {f:V → Address G}{p : poly V}
    (hq:Rise.trim (exchange (features e f 1) p) Configuration.bear d=(rename Sum.inl) (thawKey (raiseLabel G he q))) :
      Limit (fun k:ι=>(R k)^d • (exchange (features e f (R k)) p)) (edge he q) l:=by
  let Z:=KeyIn G e⊕V
  let w := Configuration.bear (G:=G) (d:=e) (Z:=V)
  let B : poly Z := edge he q
  let A := exchange (features e f 1) p
  let t(k):=(↑(R k):ℂ)
  classical
  have hs k: (R k)^d • (exchange (features e f (R k)) p)=(t k)^d • Perch.jets w ((t k)⁻¹) A:= by rw [Perch.spaced,RCLike.real_smul_eq_coe_smul (K:=ℂ)]; congr 1;exact Complex.ofReal_pow ..
  have hc (k)(i:Z→₀ℕ): coeff i ((t k)^d • Perch.jets w ((t k)⁻¹) A)= (t k)^d * (((t k)⁻¹)^Finsupp.weight w i * coeff i A) := by rw [coeff_smul,jets_coeff];rfl
  simp_rw [hs]
  refine ⟨⟨A.support∪B.support, subset_union_right,Eventually.of_forall fun k i hi=>subset_union_left (mem_support_iff.mpr ?_)⟩,fun i=>?_⟩
  · exact fun hx=> mem_support_iff.mp hi (by simp [hc,hx])
  simp_rw [hc]
  by_cases hh: Finsupp.weight w i ≤d
  · have hx: coeff i A = coeff i B:= by
      change coeff i A= coeff i (rename Sum.inl (thawKey _)); rw [← hq];change coeff i A=coeff i (Rise.trim A w d)
      rw [Rise.trim_coeff,if_pos hh]
    have hab (a:ℂ)(h:a≠0):(a^d • Perch.jets w (a⁻¹) B)=B:=by unfold B; rw [peel_pure he hv _,smul_smul,←mul_pow,mul_inv_cancel₀ h,one_pow,one_smul]
    apply tendsto_const_nhds.congr' ((hR.eventually_gt_atTop 0).mono fun k hk=>?_)
    rw [hx, ←jets_coeff,show ∀ z:ℂ,(t k)^d*z=(t k)^d • z from fun z=>rfl,←coeff_smul,hab (t k) (Complex.ofReal_ne_zero.mpr hk.ne')]
  have hz := falling_cost (lt_of_not_ge hh) hR (coeff i A)
  unfold edge; rw [← hq]
  rw [Rise.trim_coeff,if_neg hh];exact hz
end YM.PertExtension.Ticked
