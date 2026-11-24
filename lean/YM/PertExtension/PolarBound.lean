import YM.Next.RANK.Radian.Root
import Mathlib.Analysis.Complex.RemovableSingularity

/-! Resolved angular symbols and $C^n$ polar derivative bounds. Applies separately to
frequency multipliers for curl endpoints; this is a free estimate. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
namespace YM.PertExtension.LatticePT
namespace Angular
open MeasureTheory Measure Filter Maxwell Next Next.Rank Next.Rank.Radian Topology Analysis Asymptotics Set Real Metric  Lattice Beamer Atlas Normal Perch Wall CellsInt Prayer RG
open Function Finset
open scoped ContDiff Topology BigOperators Classical NNReal FourierTransform RealInnerProductSpace

abbrev opened : Set E4 := {x | x ≠ 0}
abbrev region : Set (ℝ×E4) := (univ : Set ℝ) ×ˢ opened

def Smooth (g : ℝ×E4→ℂ) : Prop := ∀ v∈ region, ContDiffAt ℝ ∞ g v
lemma isOpen_opened : IsOpen opened := (isClosed_singleton (x:=0)).isOpen_compl
lemma region_open : IsOpen region := isOpen_univ.prod isOpen_opened
lemma in_region (r : ℝ) {x:E4} (h : x≠0) : (r,x)∈region:= ⟨mem_univ _,h⟩
lemma Smooth.on {g : ℝ × E4 → ℂ} (h:Smooth g) : ContDiffOn ℝ ∞ g region := fun v hv => (h v hv).contDiffWithinAt

structure Model (f : E4→ℂ)(d : ℕ) where
  drawing : ℝ×E4→ℂ
  nice : Smooth drawing
  sees r x (hr:0 < r)(hx:x≠0) : f (r • x)=r^d • drawing (r,x)

lemma axis (g : E4→ℂ) (h : ContDiffOn ℝ ∞ g opened) (x:E4) (hx:x≠0) (r : ℝ)(hr:0<r)(n : ℕ) :
    let A : E4 →L[ℝ] E4 := r • ContinuousLinearMap.id ..
    iteratedFDeriv ℝ n (g ∘ A) x= r^n • iteratedFDeriv ℝ n g (r • x) :=by
    intro A
    have hx' : A x∈opened:= smul_ne_zero hr.ne' hx
    let W:=A ⁻¹' opened
    have hh:= isOpen_opened.uniqueDiffOn (𝕜:=ℝ)
    have he:= (isOpen_opened.preimage A.continuous).uniqueDiffOn (𝕜:=ℝ)
    have hv := A.iteratedFDerivWithin_comp_right h hh he hx' (show (↑n : WithTop ℕ∞)≤ ∞ from by exact WithTop.coe_le_coe.mpr le_top)
    rw [iteratedFDerivWithin_eq_iteratedFDeriv he (by exact (((h.comp_continuousLinearMap A) x hx'|>.contDiffAt ((isOpen_opened.preimage A.continuous).mem_nhds hx')).of_le (WithTop.coe_le_coe.mpr le_top))) hx',iteratedFDerivWithin_eq_iteratedFDeriv hh (((h (A x) hx').contDiffAt (isOpen_opened.mem_nhds hx')).of_le (WithTop.coe_le_coe.mpr le_top)) hx'] at hv
    rw [hv];ext q;change iteratedFDeriv ℝ n g (A x) (fun i=>r • q i) =_
    rw [ContinuousMultilinearMap.map_smul_univ]
    simp only [univ.prod_const, Finset.card_fin, Finset.card_univ, Fintype.card_fin, ContinuousMultilinearMap.smul_apply] -- fix
    rfl

-- derivatives only along the vector space part of the rotated/zoomed coordinates

def traced (i : ℕ) (g : ℝ×E4→ℂ) : ℝ×E4→ContinuousMultilinearMap ℝ (fun _:Fin i=> E4) ℂ :=
    fun v=>(iteratedFDeriv ℝ i g v).compContinuousLinearMap (fun j=> ContinuousLinearMap.inr ..)

private lemma iterated_smooth {D : Type*}[NormedAddCommGroup D][NormedSpace ℝ D]{g : D→ℂ}{v : D}
  (h : ContDiffAt ℝ ∞ g v)(i : ℕ) : ContDiffAt ℝ ∞ (iteratedFDeriv ℝ i g) v:=by
  induction i with
  | zero=>
    rw [iteratedFDeriv_zero_eq_comp]
    exact (LinearIsometryEquiv.contDiff _).contDiffAt.comp _ h -- fix
  | succ k ih=>
    rw [iteratedFDeriv_succ_eq_comp_left]
    exact (LinearIsometryEquiv.contDiff _).contDiffAt.comp _ (ih.fderiv_right (by simp))
lemma traced_smooth {g : ℝ×E4→ℂ} (h :Smooth g)(i : ℕ)(v : ℝ×E4)(hv:v∈region) : ContDiffAt ℝ ∞ (traced i g) v:=by
    change ContDiffAt ℝ ∞ ((ContinuousMultilinearMap.compContinuousLinearMapL (fun j=>ContinuousLinearMap.inr ..))∘iteratedFDeriv ℝ i g) v
    exact (ContinuousLinearMap.contDiff _).contDiffAt.comp v (iterated_smooth (h v hv) i)

lemma traced_partial {g : ℝ×E4→ℂ} (h : Smooth g) (r : ℝ)(x:E4)(hx:x≠0)(i : ℕ) :
    traced i g (r,x)=iteratedFDeriv ℝ i (fun z=> g (r,z)) x := by
    let F : ℝ×E4→ℂ := (fun y=>g ((r,0)+y))
    have H : ContDiffOn ℝ ∞ F region := by
        rintro ⟨a,b⟩ hb
        exact ((h _ (by have : b≠0:= hb.2;simpa using in_region (r+a) this)).comp _ (contDiffAt_const.add (𝕜:=ℝ) contDiffAt_id)).contDiffWithinAt
    let P : E4 →L[ℝ] ℝ×E4:=ContinuousLinearMap.inr ..
    have he := region_open.preimage P.continuous
    have hx':P x∈region:=in_region _ hx
    have hj: ↑i≤(∞:WithTop ℕ∞):=WithTop.coe_le_coe.mpr le_top
    have hv:= P.iteratedFDerivWithin_comp_right H region_open.uniqueDiffOn he.uniqueDiffOn hx' hj
    rw [iteratedFDerivWithin_eq_iteratedFDeriv he.uniqueDiffOn (((H.comp_continuousLinearMap P x hx').contDiffAt (he.mem_nhds hx')).of_le hj) hx', iteratedFDerivWithin_eq_iteratedFDeriv region_open.uniqueDiffOn (((H (P x) hx').contDiffAt (region_open.mem_nhds hx')).of_le hj) hx'] at hv
    rw [show iteratedFDeriv ℝ i F (P x)=iteratedFDeriv ℝ i g (r,x) from (iteratedFDeriv_comp_add_left ..).trans (congr_arg _ (by simp [P]))] at hv
    change _=iteratedFDeriv ..; rw [← show F ∘ (P:E4→ℝ×E4) = fun z=>g (r,z) by ext1 z;unfold F P;simp [Function.comp_def]]
    exact hv.symm

lemma Model.smooth {f d}(M : Model f d) (r : ℝ) : ContDiffOn ℝ ∞ (fun z => r^d • (M.drawing (1,z))) opened := by
    intro v hv
    exact ((ContDiffAt.const_smul _ ((M.nice (1,v) (in_region 1 hv)).comp v (contDiffAt_const.prodMk contDiffAt_id))).contDiffWithinAt)

lemma Model.on {f d} (M : Model f d) : ContDiffOn ℝ ∞ f opened := by
    apply (M.smooth 1).congr;intro x hx -- syntax
    simpa using (M.sees 1 x zero_lt_one hx)

open ContinuousLinearMap in
lemma scale_out {g : ℝ×E4→ℂ} (h : Smooth g)(r : ℝ)(x : E4)(hx:x≠0)(s : ℝ)(i : ℕ) :
    s • traced i g (r,x) = iteratedFDeriv ℝ i (fun z=>s • g (r,z)) x := by
    rw [traced_partial h r x hx]
    let a : ℂ→L[ℝ] ℂ := s • ContinuousLinearMap.id ..
    have ht := a.iteratedFDeriv_comp_left ((show ContDiffAt ℝ ∞ (fun z=>g (r,z)) x from (h (r,x) (in_region r hx)).comp _ (contDiffAt_const.prodMk contDiffAt_id)).of_le (n:=_) (m:=(i:ℕ∞)) (WithTop.coe_le_coe.mpr le_top)) le_rfl
    change _ = iteratedFDeriv ℝ i (a ∘ fun z=>g (r,z)) _ -- fix
    rw [ht]; ext; rfl

lemma Model.order {f d} (M : Model f d) (z : E4)(hz:z∈opened) (r : ℝ) (hr:0<r)(i : ℕ) :
    ‖iteratedFDeriv ℝ i f (r • z)‖*r^i = ‖traced i M.drawing (r,z)‖*r^d := by
    have he: iteratedFDeriv ℝ i (f ∘ (r • ContinuousLinearMap.id ℝ E4)) z=r^d • traced i M.drawing (r,z):=by
      rw [scale_out M.nice _ _ hz]
      exact (show f ∘ (r • ContinuousLinearMap.id ℝ E4) =ᶠ[𝓝 z] (fun v=> r^d • M.drawing (r,v)) from Filter.mem_of_superset (isOpen_opened.mem_nhds hz) (fun x hx=>M.sees r x hr hx)).iteratedFDeriv ℝ i |>.eq_of_nhds
    have hm : r^i • iteratedFDeriv ℝ i f (r • z)=r^d • traced .. := Eq.trans (Eq.symm (axis f M.on z hz r hr i)) he
    have hr (p : ℕ) : ‖r^p‖=r^p:= Real.norm_of_nonneg (pow_nonneg hr.le p)
    calc
      _ = ‖r^i • iteratedFDeriv ℝ i f (r • z)‖ := by rw [norm_smul,hr];apply mul_comm
      _ = _:= by rw [hm,norm_smul,hr]; apply mul_comm

private def angular (z : E4) := ‖z‖⁻¹ • z
lemma angular_props {z : E4} (h : z≠0) : angular z∈sphere 0 (1:ℝ) ∧ ‖z‖ • angular z=z := ⟨by
      rw [mem_sphere_zero_iff_norm,angular,norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr h)), inv_mul_cancel₀ (norm_ne_zero_iff.mpr h)],by rw [angular,smul_smul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr h),one_smul]⟩
private def hull (R : ℝ) := Icc 0 R ×ˢ sphere (0:E4) (1:ℝ)
private lemma hull_compact R : IsCompact (hull R):= isCompact_Icc.prod (isCompact_sphere ..)
private lemma hull_away R : hull R⊆region:= fun ⟨r,z⟩ h => in_region r (ne_zero_of_norm_ne_zero ((mem_sphere_zero_iff_norm.mp h.2).symm ▸ one_ne_zero))

lemma traced_bound i (f : ℝ×E4 → ℂ)(h : Smooth f) (R : ℝ) : ∃ C≥(0:ℝ),∀ v∈ hull R, ‖traced i f v‖≤ C:= by
  obtain ⟨C,hC⟩:= (hull_compact R).exists_bound_of_continuousOn (f:= traced i f) (fun v hv=> (traced_smooth h i v (hull_away R hv)).continuousAt.continuousWithinAt)
  exact ⟨max C 0, le_max_right C 0,fun v hv=>(hC v hv).trans (le_max_left ..)⟩

-- interpolation only in radial parameter at each fixed angle
lemma radial_bound {f : ℝ×E4→ℂ} (h : Smooth f) (R) i : ∃ C≥(0:ℝ),∀ v∈hull R, ‖traced i f v- traced i f (0,(v.2:E4))‖ ≤ C*v.1:= by
    let T:= traced i f
    obtain ⟨C,hC⟩:= (hull_compact R).exists_bound_of_continuousOn (f:= fderiv ℝ T) (fun v hv=> ((traced_smooth h i v (hull_away R hv)).fderiv_right (m:=∞) (by simp)).continuousAt.continuousWithinAt)
    let c:= max C 0
    refine ⟨c,le_max_right ..,?_⟩; rintro ⟨r,z⟩ hr
    have hz :z≠0:= (hull_away R hr).2
    let q : ℝ→_:= fun a=> T (a,z)
    have comp (a:ℝ) : HasDerivAt q ((fderiv ℝ T (a,z)) (1,0)) a:= by
       have he : HasDerivAt (fun a:ℝ=> (a,z)) ((1,0):ℝ×E4) a:= by exact (hasDerivAt_id a).prodMk (hasDerivAt_const a z)
       have hf:= ((traced_smooth h i (a,z) (in_region a hz)).differentiableAt (by simp)).hasFDerivAt
       exact hf.comp_hasDerivAt a he
    suffices h : ∀ a∈ Set.Ico 0 R, ‖(fderiv ℝ T (a,z)) (1,0)‖ ≤ c by
      have hh := norm_image_sub_le_of_norm_deriv_le_segment' (fun a _=> (comp a).hasDerivWithinAt) h r hr.1
      simpa [q,T] using hh
    intro a ha; have he:= hC (a,z) (show (a,z)∈hull R from ⟨mem_Icc.mpr ⟨ha.1,le_of_lt ha.2⟩,hr.2⟩)
    have ht:= (fderiv ℝ T (a,z)).le_opNorm (1,0)
    have hz : ‖((1:ℝ),(0:E4))‖=1:= by change max ‖(1:ℝ)‖ ‖(0:E4)‖ =_;norm_num
    calc
       _ ≤ ‖fderiv ℝ T (a,z)‖*1:= ht.trans_eq (by rw [hz])
       -- 
       _ ≤ _:=by rw [mul_one];exact he.trans (le_max_left ..)

private lemma combine {f d}(M : Model f d) (n k : ℕ) (R) (h : ∀ i,∃ c ≥ (0:ℝ),∀ v∈hull R,‖traced i M.drawing v‖ ≤ c*v.1^k) :∃ c,Cast f n (d+k) R c := by
    choose c H hp using h
    let B := ∑ i∈Finset.range (n+1),c i
    have hB i (hi:i≤n) : c i≤B:=Finset.single_le_sum (fun j _=> H j) (Finset.mem_range.mpr (Nat.lt_add_one_iff.mpr hi))
    refine ⟨B, (H 0).trans (hB 0 (Nat.zero_le _)),M.on.of_le (WithTop.coe_le_coe.mpr le_top),?_⟩
    intro i hi x hx hZ
    let r:= ‖x‖;let z:= angular x;have ht:=angular_props hx; have hv : (r,z)∈hull R:=⟨⟨norm_nonneg _,hZ⟩,ht.1⟩
    have hf : 0<r:= norm_pos_iff.mpr (show x≠0 from hx)
    have he:= M.order z (hull_away R hv).2 r hf i
    calc
      ‖iteratedFDeriv ℝ i f x‖ * r ^ i = ‖traced i M.drawing (r,z)‖*r^d:= by rw [← he, ht.2]
      _ ≤ c i*r^k*r^d:=mul_le_mul_of_nonneg_right (hp i (r,z) hv) (by positivity)
      _ ≤ B*r^(d+k):= by rw [pow_add]; rw [show c i*r^k*r^d=c i*(r^d*r^k) by ring]; exact mul_le_mul_of_nonneg_right (hB i hi) (by positivity)
lemma Model.cast {f d}(M:Model f d) (n : ℕ) (R : ℝ): ∃ c,Cast f n d R c := by
  simpa using combine M n 0 R (show ∀ i, ∃ c≥(0:ℝ),∀ v∈hull R, ‖traced i M.drawing v‖ ≤ c*v.1^0 from fun i=>by simpa using traced_bound i M.drawing M.nice R)
lemma Model.cast_vanishing {f d}(M:Model f d)(h : ∀ z∈opened,M.drawing (0,z)=0) (n : ℕ) (R : ℝ): ∃ c,Cast f n (d+1) R c := by
   exact combine M n 1 R fun i=>by
      obtain ⟨c,hc,H⟩:= radial_bound M.nice R i
      refine ⟨c,hc,?_⟩
      intro v hv; have hp:=hull_away R hv
      have he :traced i M.drawing (0,v.2) =0:= by
        rw [traced_partial M.nice 0 v.2 hp.2]
        rw [( (show (fun z=> M.drawing (0,z)) =ᶠ[𝓝 v.2] 0 from Filter.mem_of_superset (isOpen_opened.mem_nhds hp.2) h).iteratedFDeriv ℝ i |>.eq_of_nhds )]
        by_cases hx:i=0; subst i
        · ext; simp
        exact congr_fun (iteratedFDeriv_const_of_ne hx (0:ℂ)) v.2 -- fix
      simpa only [pow_one,he,sub_zero] using H v hv
end Angular
end YM.PertExtension.LatticePT
