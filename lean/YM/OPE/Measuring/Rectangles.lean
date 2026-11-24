import YM.OPE.Measuring.Axes

/-!
# Transversal zero jets to mixed polynomial bounds on rectangles

Auxiliary analytic lemma. No Taylor expansion is taken jointly in the
perturbation coupling. All rates deciding zero jets in this use are individual
*spatial* corner tests on the actual coefficient prescription.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Measuring.Axes
open Filter Set Function Asymptotics
open scoped ContDiff Topology
variable {E B:Type*}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup B][NormedSpace ℝ B]
variable {f:E→B}{s:Set E}{p v w:E}

lemma one_bound (n:ℕ)(x₀ v:E){r C:ℝ}(hr:0 ≤ r)(h:∀ t∈Icc (0:ℝ) r, ContDiffAt ℝ ∞ f (x₀+t•v))
    (hZ:∀ i<n,path v f i x₀=0)(hf:∀ t∈Icc (0:ℝ) r, ‖path v f n (x₀ + t•v)‖ ≤ C): ‖f (x₀+r•v)‖ ≤ C*r^n:=by
    induction n generalizing r f with
    | zero=> simpa only [pow_zero,mul_one, path,iterate_zero_apply] using hf r ⟨hr,le_rfl⟩
    | succ n ih=>
       let g:=leaf v f; have he i : path v g i=path v f (i+1):=rfl
       have ht(t:ℝ)(hh:t∈Icc (0:ℝ) r): ‖g (x₀ + t•v)‖ ≤ C*r^n := by
          have h':=show ‖g (x₀+t•v)‖ ≤ C*t^n from ih hh.1 (fun u hu=> leaf_live v (h u ⟨hu.1,(hu.2.trans hh.2)⟩)) (by intro i hi; rw [he]; exact hZ _ (Nat.succ_lt_succ hi)) (fun u hu=> by rw [he]; exact hf u ⟨hu.1,hu.2.trans hh.2⟩)
          exact h'.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hh.1 hh.2 _) ((norm_nonneg _).trans (hf r ⟨hr,le_rfl⟩)))
       have hd := (convex_Icc (0:ℝ) r).norm_image_sub_le_of_norm_hasDerivWithin_le (f:=fun t:ℝ=>f (x₀+t•v)) (f':=fun t:ℝ=>g (x₀+t•v)) (fun u hu=> (affine_deriv v ((h u hu).differentiableAt (by simp))).hasDerivWithinAt) ht ⟨le_rfl,hr⟩ ⟨hr,le_rfl⟩
       have hf0:f x₀=0:=hZ 0 (by omega)
       simpa only [sub_zero,Real.norm_of_nonneg hr,zero_smul,add_zero,hf0,mul_assoc,pow_succ, path,iterate_zero_apply] using hd

-- mixed derivative at a point on the (v=0) face, using zeros all along the open face.
-- Need positive width in w direction, not elsewhere for this calculation.
def cross (p v w:E)(x y:ℝ):=p+x•v+y•w
private lemma run_sw {o:E} (n l : ℕ) (hs:s∈𝓝 o) (hf:∀z∈s, ContDiffAt ℝ ∞ f z): path v (path w f l) n o = path w (path v f n) l o:=by
    induction l generalizing o with
    | zero=>rfl
    | succ l ih=> rw [longer (n:=l),longer (n:=l),← inversePath (f:=path w f l) w v n ((eventually_of_mem hs fun _ hh=>path_live w l (hf _ hh)))]
                  refine congr_arg (fun M:E→L[ℝ]B=>M w) (EventuallyEq.fderiv_eq (𝕜:=ℝ) ?_)
                  filter_upwards [eventually_mem_nhds_iff.mpr hs] with i hi using ih hi -- name check
private lemma along_zero {g:E→B}{a b y:ℝ}(hy:y∈Ioo a b)(h:∀z∈Ioo a b, g (p+z•w)=0)(hm:DifferentiableAt ℝ g (p+y•w)): leaf w g (p+y•w)=0:=by
    exact (affine_deriv w hm).unique ((hasDerivAt_const y (0:B)).congr_of_eventuallyEq ((Ioo_mem_nhds hy.1 hy.2)|> (fun hq=>eventually_of_mem hq h))) -- exact?
lemma plane_zero {v w:E}(n:ℕ){e:ℕ}{R p':ℝ}(hR:0<R)(hf:∀ x∈Icc (0:ℝ) p',∀ y∈Icc (0:ℝ) R,∀ᶠ i in 𝓝 (cross p v w x y),ContDiffAt ℝ ∞ f i) (hz:0≤p')
     (h₀:∀ i<n,∀ y∈Ioo (0:ℝ) R,path v f i (p+y•w)=0): ∀ (y:ℝ), y∈Ioo 0 R→∀ i<n,path v (path w f e) i (p+y•w)=0 :=by
   intro y hy i hi
   let s:={x:E|ContDiffAt ℝ ∞ f x}; have he(y:ℝ)(hy:y∈Ioo 0 R): s∈𝓝 (p+y•w):=by simpa only [Filter.Eventually, cross, zero_smul,add_zero] using hf (0:ℝ) ⟨le_rfl,hz⟩ y ⟨hy.1.le,hy.2.le⟩
   rw [run_sw i e (he y hy) (fun _ h=>by exact h)]
   induction e generalizing y with
   | zero=>exact h₀ i hi y hy
   | succ e ih => rw [longer]; exact along_zero hy (fun y' hy=>by apply ih _ hy) ((path_live _ _ (path_live _ _ (mem_of_mem_nhds (he y hy)))).differentiableAt (by simp))

lemma mixed {x y A C:ℝ}(hx:x∈Ioo (0:ℝ) A)(hy: y∈Ioo (0:ℝ) 1)(n e:ℕ) (h:∀ r∈Icc (0:ℝ) A,∀ s∈Icc (0:ℝ) 1, ∀ᶠ i in 𝓝 (cross p v w r s), ContDiffAt ℝ ∞ f i)
    (h₀:∀ i<n,∀ y∈Ioo (0:ℝ) 1,path v f i (p+y•w)=0)(h₁:∀ j<e, ∀ x∈Ioo (0:ℝ) A,path w f j (p+x•v)=0)
    (hC:∀ r∈Icc (0:ℝ) A,∀ s∈Icc (0:ℝ) 1, ‖path v (path w f e) n (cross p v w r s)‖ ≤ C): ‖f (cross p v w x y)‖ ≤ C*x^n*y^e := by
       have hA:0≤A:= le_of_lt (hx.1.trans hx.2); have ht:=plane_zero (p:=p) (e:=e) (p':=A) (v:=v) (w:=w) n zero_lt_one h hA h₀
       -- bound w-jet uniformly for positive y'∈(0,y]
       have hF(z:ℝ)(hz:z∈Ioo (0:ℝ) 1): ‖path w f e (cross p v w x z)‖ ≤ C*x^n:=by
           have he(r s:ℝ):cross p v w r s=(p+s•w)+r•v:=add_right_comm ..
           rw [he]; exact one_bound (n:=n) _ _ hx.1.le (by intro t h'; rw [← he]; exact path_live w e (mem_of_mem_nhds (h t ⟨h'.1,h'.2.trans hx.2.le⟩ _ ⟨hz.1.le,hz.2.le⟩))) (ht _ hz) (by intro t h'; rw [← he]; exact hC t ⟨h'.1,h'.2.trans hx.2.le⟩ _ ⟨hz.1.le,hz.2.le⟩)
       have hz : ‖path w f e (p+x•v)‖ ≤ C*x^n := by
           have : ContinuousAt (fun z=> path w f e (cross p v w x z)) (0:ℝ):=(path_live w e ((h x ⟨hx.1.le,hx.2.le⟩ 0 (by simp)).self_of_nhds)).continuousAt.comp (continuous_const.add (continuous_id.smul continuous_const)).continuousAt
           have ht:=this.norm.tendsto.mono_left (show 𝓝[>] (0:ℝ) ≤ _ from nhdsWithin_le_nhds)
           change Tendsto _ (𝓝[>] (0:ℝ)) (𝓝 (‖path w f e (cross p v w x 0)‖)) at ht
           rw [show cross p v w x 0=p+x•v from add_eq_left.mpr (zero_smul _ _)] at ht
           refine le_of_tendsto ht ?_
           filter_upwards [eventually_nhdsWithin_of_eventually_nhds (gt_mem_nhds (zero_lt_one' ℝ)),self_mem_nhdsWithin (s:=Ioi (0:ℝ))] with t ht he; exact hF _ ⟨he,ht⟩
       change ‖f ((p+x•v)+y•w)‖ ≤ _; apply one_bound e _ _ hy.1.le (by intro r hr; exact mem_of_mem_nhds <| h x ⟨hx.1.le,hx.2.le⟩ r ⟨hr.1,hr.2.trans hy.2.le⟩) (fun j hj=>h₁ j hj x hx)
       intro z h; rcases eq_or_lt_of_le h.1 with H|h₀
       · rw [← H,zero_smul,add_zero]; exact hz
       exact hF _ ⟨h₀,h.2.trans_lt hy.2⟩
end YM.OPE.Measuring.Axes
