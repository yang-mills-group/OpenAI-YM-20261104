import YangMills.WilsonProof.NativeSupport.YM.MS.Mach.Land
/-!
# External polynomial degrees. Finite value tests.
Linear constraints can be tested at any stage of Laurent/ODE construction. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Awning
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color
open _root_.YM.MS.Shine Hem Mell Logarithm Pearl Train Signal Book Convolve
open scoped Topology ContDiff Interval
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{X:Type}{p h:ℤ}
variable {f g:ℝ→ℂ}{s:Finset ℝ}
def ig (h:ℤ): Finset ℕ:= range (h+1).toNat
lemma is_ig (h:ℤ)(i:ℕ): i∈ ig h↔ (i:ℤ)≤h:= by rw [ig,Finset.mem_range]; omega
-- univariates on labeled lines
def poseX (j:ℕ)(p:ℝ):ℂ:= (p:ℂ)^j
def Bowl (h:ℤ): Submodule ℂ (ℝ→ℂ):= Submodule.span ℂ (poseX '' ( ↑(ig h) ))
lemma bowl_in {j:ℕ}(hv:(j:ℤ)≤h): poseX j ∈ Bowl h:= Submodule.subset_span (Set.mem_image_of_mem poseX ((is_ig h j).mpr hv))
instance (h:ℤ): FiniteDimensional ℂ (Bowl h):= FiniteDimensional.span_of_finite _ ((ig h).finite_toSet.image _)
lemma bowl_more (hm:h≤p) : Bowl h ≤ Bowl p:= Submodule.span_le.mpr (by rintro g ⟨i,hi,rfl⟩; exact bowl_in (((is_ig h i).mp hi).trans hm) )
-- finite value tests
def bill (s:Finset X)(μ:X→ℂ) : (X→ℂ)→ₗ[ℂ]ℂ := ∑ i∈s,μ i • LinearMap.proj i
lemma billed (s:Finset X)(μ:X→ℂ)(F:X→ℂ): bill s μ F= ∑ i∈ s,μ i* F i:= by simp [bill,LinearMap.sum_apply]
lemma bowl_iff (h:ℤ): f∈ Bowl h ↔ ∀ s (μ:ℝ→ℂ),(∀ g,g∈ Bowl h→ ∑ i∈ s, μ i*g i=0)→ ∑ i∈ s,μ i*f i=0:= by
   constructor; exact fun hv _ _ h=> h _ hv
   intro H; rw [← Subspace.dualAnnihilator_dualCoannihilator_eq (W:=Bowl h),Submodule.mem_dualCoannihilator]; intro F hF; let Q:= Bowl h ⊔ Submodule.span ℂ {f}; haveI : FiniteDimensional ℂ Q:= inferInstanceAs (FiniteDimensional ℂ ↥( Bowl h ⊔ Submodule.span ℂ {f} )) ; obtain ⟨s,μ,hμ⟩:= Local.point_recovery Q ( F ∘ₗ Q.subtype ); have he{w:ℝ→ℂ}(hv:w∈Q): F w= ∑ i∈s,μ i*w i:= hμ ⟨w,hv⟩; refine Eq.trans (he (  (show Submodule.span ℂ {f} ≤ Q from le_sup_right) (Submodule.subset_span (Set.mem_singleton _)))) ( H s μ (fun g hg=> ?_) ); rw [ ← he ( le_sup_left (a:=Bowl h) hg ) ]; exact (Submodule.mem_dualAnnihilator _).mp hF g hg
abbrev beat (f:ℝ→ℂ)(j:ℕ): ℝ→ℂ:= fun p=> poseX j p*f p
lemma pair_s (hp:f∈ Bowl h)(j:ℕ): beat f j∈ Bowl (h+j):= by
   refine Submodule.span_induction (p:=fun f _=>beat f j∈ Bowl (h+j)) ?_ ?_ ?_ ?_ hp
   · rintro g ⟨i,hi,rfl⟩; rw [show beat (poseX i) j=poseX (j+i) from funext fun _=> (pow_add ..).symm ]; have hp:=(is_ig _ i).mp hi; exact bowl_in (by omega)
   · rw [show beat 0 j= 0 from funext fun i=> mul_zero _]; exact Submodule.zero_mem _
   · intro f g _ _ hf hg; rw [show beat (f+g) j=beat f j+beat g j from funext fun p=> mul_add (poseX j p) ( f p ) ( g p ) ]; exact Submodule.add_mem _ hf hg
   intro c f _ hf; rw [show beat ( c • f ) j=c • beat f j from funext fun p=> mul_left_comm (poseX j p) c (f p) ]; exact Submodule.smul_mem _ _ hf
lemma traced (j:ℕ)(T:Tensor.T E ℂ j)(x v:E): (fun p:ℝ=>Tensor.diagonal T (x+p • v))∈ Bowl j:= by
   induction j generalizing x v with
   | zero=>
      rw [show (fun p:ℝ=> _)=Tensor.diagonal T x • poseX 0 from funext fun p=>?_]; exact ( Bowl ( (0:ℕ):ℤ ) ).smul_mem _ (bowl_in le_rfl); change _= Tensor.diagonal T x*(p:ℂ)^0; rw [pow_zero,mul_one]; exact congr_arg T (Subsingleton.elim ..)
   | succ j ih=>
      let U(v:E)(w:E)(p:ℝ):= Tensor.diagonal ( T.curryLeft v ) (x+p • w); have hi (a p:E):= ih ( T.curryLeft a ) x p; rw [show (fun p:ℝ=>_)=U x v+beat (U v v) 1 from ?_,Nat.cast_add,Nat.cast_one]; exact Submodule.add_mem _ (bowl_more ( le_add_of_nonneg_right zero_le_one ) (hi x v)) (pair_s (hi v v) 1)
      funext p; let y:= x+p • v; unfold beat poseX U; simp only [Pi.add_apply,pow_one]; change Tensor.diagonal T y=_; rw [ show Tensor.diagonal T y=Tensor.diagonal ( T.curryLeft y ) y from ?_, Tensor.diagonal, show y=x+p • v from rfl,map_add,map_smul,_root_.add_apply,smul_apply]; exact congr_arg (_+·) (Complex.real_smul ..)
      unfold Tensor.diagonal; rw [ ContinuousMultilinearMap.curryLeft_apply ]; congr 1; exact (Fin.cons_self_tail ..)|>.symm
-- shape on origin iff inside span each affine
lemma crossed {A:E→ℂ}(hp: Shape A h)(x v:E): (fun p:ℝ=>A (x+p • v))∈ Bowl h:= by
    rcases lt_or_ge h 0 with he|he; · rw [hp.charge he]; exact Submodule.zero_mem _
    lift h to ℕ using he; rw [hp.form]; exact traced h _ x v
end YM.MS.Awning
