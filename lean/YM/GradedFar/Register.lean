import YM.GradedFar.Paid
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
/-! # Derivative expansion accounting & its uniqueness -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar
open FVA2.GradedFar FVA2.GradedFar.Cart Function Filter Set PowerSeries
open scoped Topology BigOperators Classical Matrix
variable {I : Type*} {X : Type*} {L : Filter X} {J : Type*} {t : X → ℝ} {f h : X→I→ℂ} {F H : I→PowerSeries ℂ}

lemma Receives.lead (hr:Receives t L f F) (ht:Tendsto t L (𝓝 0))(i:I) : Tendsto (fun x=> f x i) L (𝓝 (constantCoeff (F i))) := by
 obtain ⟨C,hC,h⟩:= (hr.good 0).cost
 have H:Tendsto (fun x=> C*|t x|) L (𝓝 0):=by simpa using (ht.abs.const_mul C)
 refine tendsto_iff_norm_sub_tendsto_zero.mpr (squeeze_zero' (Eventually.of_forall (fun _=> norm_nonneg _)) ?_ H)
 exact h.mono (fun x hx=> by simpa [crop_eq] using hx i)

abbrev Expansion (t:X→ℝ)(L:Filter X)(f:X→ℂ)(F:PowerSeries ℂ):= Receives t L (fun i (_:Unit)=> f i) (fun _=>F)
section
variable (ht:Tendsto t L (𝓝 0))
include ht
lemma Receives.same [L.NeBot] (he:∀ᶠ x in L,t x≠0)(hf:Receives t L f F)(hv:Receives t L f H)(i:I): F i=H i:= by
 obtain hr:=hf.sub hv; simp_rw [sub_self] at hr; rw [← sub_eq_zero]; apply PowerSeries.ext; simp_rw [map_zero (coeff _)]; intro n; induction n using Nat.strong_induction_on with
 | _ n ih =>
   obtain ⟨C,hC,h⟩:= (hr.good n).cost
   let p:= F i-H i
   have H0: ∀ᶠ x in L, ‖coeff n p‖ ≤ C*|t x|:= by
     filter_upwards [h,he] with x hx hp; specialize hx i; have hpx:0 < |t x|:=abs_pos.mpr hp; refine le_of_mul_le_mul_left ?_ (pow_pos hpx n)
     rw [zero_sub,norm_neg,crop_eq,Finset.sum_eq_single n,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs] at hx
     · exact hx.trans_eq (by ring)
     exacts [fun b hb H=> by rw [ih b (by simp at hb; omega),mul_zero],by simp]
   have ha:= (ge_of_tendsto (show Tendsto (fun x=> C*|t x|) L (𝓝 0) from by simpa using ht.abs.const_mul C) H0)
   exact norm_le_zero_iff.mp ha
lemma ExpInv {f:X→ℂ}{F:PowerSeries ℂ}(h:Expansion t L f F) (hu: IsUnit F): Expansion t L (fun i=> (f i)⁻¹) (↑(hu.unit⁻¹)) := by
 let P:PowerSeries ℂ:= ↑(hu.unit⁻¹)
 have hp: F*P=1:= by
   nth_rw 1 [← hu.unit_spec]; simp only [P, Units.mul_inv]
 have ht':Tendsto f L (𝓝 (constantCoeff F)):= Receives.lead h ht ()
 let x:= constantCoeff F; have hx: x≠0:= isUnit_iff_ne_zero.mp (PowerSeries.isUnit_iff_constantCoeff.mp hu)
 have he:= ht'.eventually (isOpen_compl_singleton.mem_nhds (by exact hx))
 have hb:Pays (fun _=>1) L (fun i (_:Unit)=> (f i)⁻¹):=by
   refine ⟨‖x⁻¹‖+1,by positivity,?_⟩; filter_upwards [(ht'.inv₀ hx).norm.eventually_le_const (by exact lt_add_one ‖x⁻¹‖)] with r hr i
   rw [mul_one]; exact hr
 have hi: Feasible (fun (_:Unit)=> ofPS P) (fun _=>0) := fun i=> Charge.const _
 refine ⟨hi,fun i=>?_⟩
 obtain hv:= (h.good i).mul (justified ht i (F:=fun (_:Unit)=>P) hi); obtain hz:= omissions ht i h.cost hi; simp_rw [mul_one] at hv
 obtain hh:= hb.mul (hv.add hz).neg; simp_rw [one_mul] at hh; refine hh.tran ?_; filter_upwards [he] with x hx; funext j
 change (f x)⁻¹ * (-((f x - crop i (t x) F)*crop i (t x) P + (crop i (t x) F*crop i (t x) P-crop i (t x) (F*P)))) = (f x)⁻¹-crop i (t x) P
 rw [hp,show crop i (t x) 1=1 from by simpa only [map_one] using constant_crop i (t x) 1]; have h': f x≠0:=hx; field_simp; ring

open Matrix
lemma ExpDet [Fintype I] [DecidableEq I] {A:X→Matrix I I ℂ}{F:Matrix I I (PowerSeries ℂ)}
    (H:∀ i j, Expansion t L (fun x=> A x i j) (F i j)): Expansion t L (fun x=> det (A x)) F.det := by
 unfold Expansion; simp_rw [det_apply']; refine Receives.sum _ fun q _=>?_ ; obtain hv:= (Receives.fix (I:=Unit) (t:=t) (L:=L) ((q.sign:ℤ):ℂ)).mul
   (Receives.prod Finset.univ (fun i _=> H (q i) i) ht) ht; simpa only [map_intCast] using hv
lemma ExpSolve [Fintype I] [DecidableEq I] {A:X→Matrix I I ℂ}{F:Matrix I I (PowerSeries ℂ)}
    {f h:X→I→ℂ}{Z:I→PowerSeries ℂ} (HA:∀ i j,Expansion t L (fun x=> A x i j) (F i j))
    (H:∀ᶠ x in L,A x *ᵥ (f x)=h x)(HF:IsUnit (F.map constantCoeff))(hh:∀ i,Expansion t L (fun x=> h x i) (Z i))(i:I):
    ∃ P,Expansion t L (fun x=> f x i) P:=by
 have hu:= (isUnit_iff_isUnit_det _).1 HF; change IsUnit ((RingHom.mapMatrix constantCoeff) F).det at hu; rw [← RingHom.map_det] at hu
 obtain hp:=PowerSeries.isUnit_iff_constantCoeff.mpr hu; obtain hD:=ExpDet ht HA; obtain hq:= ExpInv ht hD hp
 have Hv: Expansion t L (fun x=> ((A x).updateCol i (h x)).det) (F.updateCol i Z).det := by
   apply ExpDet ht; intro j k; by_cases h:k=i
   · subst k; simp_rw [updateCol_self]; exact hh j
   simp_rw [updateCol_ne h]; exact HA j k
 have hb:= Receives.mul Hv hq ht; refine ⟨ _,hb.congr ?_ fun _=>rfl⟩; filter_upwards [H,(hD.lead ht ()).eventually
   (isOpen_compl_singleton.mem_nhds (isUnit_iff_ne_zero.mp hu))] with x hx hv; funext u
 have hh:(A x).det ≠ 0:=hv; rw [← hx,show A x *ᵥ f x = (fun i=> ∑ j, f x j • A x i j) from by
    ext k; simp [Matrix.mulVec, dotProduct,mul_comm], det_updateCol_sum, smul_eq_mul]; field_simp
end
end YM.Integration.GradedFar
