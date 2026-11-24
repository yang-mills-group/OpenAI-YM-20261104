import YM.OPE.Compatible.Ash.Null
/-! # Lowest shelf, elliptic singular deleted -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Balsam
open Function MeasureTheory Set Topology Metric Filter Lattice Pert.Band Pert.Full
open scoped BigOperators Classical ContDiff
variable {U:Gloam}{s:ℝ}{D:List Axis}{a:Cover}{g:ℝ→E4→ℂ}{z:(i:ℕ)→ Site (U.M i)}
def low (n:Side)(c:ℝ):=Finset.univ.filter (fun p:Site n=>‖stretch (dew n*c) p‖≤1)
lemma low_eq {i:ℕ} (hh:U.h i*s≤1)(hs:0<s):low (U.M (i+1)) s= (low (U.M i) s).image (smaller (U.ratio i)):=by -- autoImplicit false
   ext p; constructor
   · intro hp; have he:‖stretch (dew _*s) p‖ ≤ 1:= (Finset.mem_filter.mp hp).2; have hx:p∈range (smaller (U.ratio i)):=by
       by_contra hw; have hk:=bigger_far (U.ratio i) p hw s hs hh; linarith only [hk,he]
     obtain ⟨x,rfl⟩:=hx; apply Finset.mem_image_of_mem; rw [stretch_same (U.ratio i) x s hs] at he; rw [low,Finset.mem_filter]
     exact ⟨Finset.mem_univ _,he⟩
   intro hp; obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp hp; rw [low,Finset.mem_filter,stretch_same _ _ _ hs]; exact ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩ -- first mem
lemma hotstroke (D:List Axis)(a:Cover)(j:ℕ) (x:E4) (hh:‖x‖≤1): ∃ c≥0,∀ t∈Icc (0:ℝ) 1, ‖vet U.q' j (hotband D a) t x‖ ≤ t^j*c:=by
   by_cases hx:x=0
   · refine ⟨0,le_rfl,fun t _=>?_⟩; subst x; rw [vet_nop j (fun u=> by simp [hotband,symbol,latticeD]),norm_zero,mul_zero]
   let g:ℝ→ℝ→ℂ:=fun t _=> hotband D a t x; have hv:∀ p∈ Icc (0:ℝ) 1 ×ˢ ({(0:ℝ)}: Set ℝ),ContDiffAt ℝ ∞ (Function.uncurry g) p:=by
      rintro ⟨p,y⟩ hp; have hh':|p| ≤ 1:=by rw [abs_of_nonneg hp.1.1]; exact hp.1.2
      have he:0< latticeD p x := latticeD_pos hx (fun i=>by grw [abs_mul, hh',one_mul,coordinate_le x i,hh]; linarith only [Real.pi_gt_three]); have ho:= symbol_diff D _ _ he.ne'
      have ht:= contDiffAt_fst (n:=∞) (𝕜:=ℝ) (p:=(p,y)); refine (ContDiffAt.mul (f:=fun _ : ℝ×ℝ=> (disk x:ℂ)) contDiffAt_const (ho.comp (f:=fun w:ℝ×ℝ=>(w.1,x)) (p,y) (ht.prodMk contDiffAt_const))).mul (g:=fun m:ℝ×ℝ=> Complex.exp ((corner a (m.1 • x):ℝ)*Complex.I)) ?_
      apply ContDiffAt.cexp; refine ContDiffAt.mul (g:=fun _:ℝ×ℝ=> Complex.I) ?_ contDiffAt_const; apply Complex.ofRealCLM.contDiff.contDiffAt.comp (f:=fun w:ℝ×ℝ=> corner a (w.1 • x)); unfold Pert.Full.corner; fun_prop
   obtain ⟨c,hc,L⟩:= snow (k:=j) U.qsub.le isCompact_singleton hv; exact ⟨c,hc,fun t ht=> L _ rfl _ ht⟩
lemma band_low (z:(i:ℕ)→ Site (U.M i))(hs:0<s)(a:Cover)(D:List Axis)(r:ℕ): ∃ C≥0, ∀ᶠ i in atTop, ‖bandread (hotband D a) s r z i‖ ≤ C*(U.h i)^r :=by
   obtain ⟨K,hK⟩:= eventually_atTop.mp (show ∀ᶠ i in atTop,U.h i*s ≤ 1 from (U.h_null.mul_const s).eventually (ge_mem_nhds (by simp))); let A(i):= low (U.M i) s
   let L(i j:ℕ):=∑ q∈(A j),‖vet U.q' r (hotband D a) (U.h i*s) (stretch (U.h j*s) q)‖ -- p remove
   let G:=hotband D a; obtain ⟨c,hc,hh⟩:∃ c:Site (U.M K)→ℝ, (∀ x,0 ≤ c x) ∧∀ p∈A K,∀ t∈Icc (0:ℝ) 1, ‖vet U.q' r (hotband D a) t (stretch (U.h K*s) p)‖ ≤ t^r*c p:=by
      have hv(p:Site (U.M K)):∃ c≥0, p∈ A K → ∀ t∈Icc (0:ℝ) 1, ‖vet U.q' r G t (stretch (U.h K*s) p)‖≤ t^r*c:=by
          by_cases ht:p∈ A K; obtain ⟨c,hc,he⟩:= hotstroke (U:=U) D a r _ (show ‖stretch (U.h K*s) p‖ ≤ 1 from (Finset.mem_filter.mp ht).2); exact ⟨c,hc,fun _=> he⟩; exact ⟨0,le_rfl,fun hx=>(ht hx).elim⟩
      choose c hc he using hv; exact ⟨c,hc,he⟩
   refine ⟨(∑ p∈ A K,c p)*s^r,mul_nonneg (Finset.sum_nonneg (fun i _=> hc _)) (by positivity),?_⟩; filter_upwards [eventually_ge_atTop K] with i hi
   change ‖∑ p:Site _, char p _*vet U.q' r G _ (stretch _ p)‖ ≤ _
   grw [norm_sum_le]; simp_rw [norm_mul, norm_char, one_mul]
   have he j (hj:K≤ j): L i j=L i K:=by
       induction j,hj using Nat.le_induction with
       | base=> rfl
       | succ j hj ih=>
         rw [←ih]; unfold L; rw [show A (j+1)=(A j).image (smaller (U.ratio j)) from low_eq (hK j hj) hs, Finset.sum_image (by intro x _ y _ hx; exact nearer (U.ratio j) hx)]; apply Finset.sum_congr rfl; intro p _; rw [show stretch (U.h (j+1)*s) (smaller (U.ratio j) p)=stretch (U.h j*s) p from stretch_same _ _ _ hs]
   rw [show (∑ p:Site (U.M i), ‖vet U.q' r G (U.h i*s) (stretch (U.h i*s) p)‖) = L i i from Eq.symm (Finset.sum_subset (Finset.subset_univ (A i)) ?_ ), he i hi]
   · unfold L; apply (Finset.sum_le_sum (g:=fun p=>(U.h i*s)^r*c p) (fun p hp=> hh p hp _ ⟨(mul_pos (U.h_pos _) hs).le,hK i hi⟩)).trans; rw [← Finset.mul_sum,mul_pow]; exact le_of_eq (by ring)
   intro p _ hp
   have hv: vet U.q' r G (U.h i*s) (stretch (U.h i*s) p)=0:= by apply vet_nop; intro u; apply trim_hot; exact le_of_not_ge fun hx=>hp (Finset.mem_filter.mpr ⟨Finset.mem_univ p,hx⟩)
   rw [hv,norm_zero]
end YM.OPE.Balsam
