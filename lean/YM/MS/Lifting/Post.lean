import YM.MS.Lifting.Primitive
import YM.MS.High.Sphere
/-!
# Dimensional lead after lattice Q

Use Q full tree with quadratic bulk. Nonhomogeneous waves do not affect
 leading fit. Lower ranks self-contractions ignore at this stage.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Lifting
open Function Filter Set Finset Plane Koszul Color Real Momentum Wire Tensor Book
open Landau Detect Detect.Mark Cylinder Lab Taylor Native Draft Paint Sew Native.Chart Orient Wilsonian Studio
open Tone Tone.Frame Lattice Local Local.BV Submodule
open Complex (I)
open scoped Topology ContDiff
variable {G:Gauge}{F S:Dot G Cover}{v u:ℤ}{H K:Law G}{n q:ℕ}{p:Sector (Branch G Axis)} {b:Bool}
lemma rest_visit (w:List (Lane4 G)) (f:ℝ→Slash (Branch G Axis) FourP ℂ)(g:Slash (Branch G Axis) FourP ℂ)(H:∀ l i r,l++i::r=w→ Rest (fun t=> f t l i r) v (g l i r)): Rest (fun t=> visit b p w (f t)) v (visit b p w g):= by
   induction w generalizing f g with
   | nil=> exact Rest.zero _
   | cons i w ih=> exact (H [] i w rfl).add ((ih (fun t l j r=> f t (i::l) j r) (fun l j r=> g (i::l) j r) (fun l j r h=> H _ _ _ (by simp [h]))).smul _)
open High
lemma table (i j:Branch G Axis)(q:QP): Rest (fun t:ℝ=>(send wave).table i j (t • q)) (1+wfield j-wfield i) ((send id).table i j q):= by
   let r := criterion (C:=G.ColorIndex) (A:=Axis) (R:=meet) (primary_large s_gain.le); have hv := r.cost i j
   refine ⟨(hv.lat.smooth (meet.start 0)).comp (by fun_prop : ContDiff ℝ ∞ (fun t:ℝ=>t • q)),fun v=> ?_, fun k hk=>?_⟩
   · exact congr_fun ((r.shape i j).charge v) q
   rw [r.read meet_start hk p_gain q]; split <;> split <;> first| rfl| omega

def scoreV (t:ℝ) (H:Law G) (Z:Charge p FourP ℂ): Slash (Branch G Axis) FourP ℂ:= fun l i r=> ∑ j:Branch G Axis,Z.table i.1 j (t • i.2)* fieldVal H (ray (l++(j,i.2)::r)) t
lemma owns (t:ℝ)(H:Law G)(Z:Charge p FourP ℂ)(w:List (Lane4 G)): fieldVal (Z.raise H) (ray w) t=visit true p w (scoreV t H Z):= by
    unfold fieldVal; rw [visit_Z,ray_go,Charge.mark_visit true p (z:=fun i:Lane4 G=> (i.1,t • i.2)) (hz:=fun i=>rfl)]; unfold scoreV; simp [fieldVal]
lemma table_fit (h:Face wfield H K v b): Face wfield ((send wave).raise H) (natQ K) (v+1) b:= by
    intro w hw; rw [funext (fun t=>owns t H (send wave) w), show natQ K w=fieldVal ((send id).raise K) (ray w) 1 from by simp [fieldVal], owns]; refine rest_visit _ _ _ (fun l i r ht=> ?_); unfold scoreV; refine Rest.sum _ (fun j _=>?_)
    have hL := h (l++(j,i.2)::r) (visit_course _ l r i (ht ▸ hw) j)
    simp only [one_smul, show fieldVal K (ray _) 1 = K (l++(j,i.2)::r) from by unfold fieldVal; rw [ray_sail]]; rw [show v+1-fieldDim wfield w= (1+wfield j-wfield i.1) + (v-fieldDim wfield (l++(j,i.2)::r)) by rw [visit_field,ht]; omega]; -- test simp too much
    exact (table i.1 j i.2).mul hL

lemma mask_raises (f:FourP→FourP) (H:Law G) (u:ℤ): Book.mask u ((send f).raise H)= (send f).raise (Book.mask u H):= by
    funext l; by_cases h:(l.length:ℤ)=u; rw [enough _ h,visit_Z,visit_Z]; apply visit_agree; intro l i r he; apply Finset.sum_congr rfl; intro j _; rw [enough _ (by rw [← he] at h; simpa using h)]
    rw [strange _ h,visit_Z, ← visit_zero (R:=ℂ) (p:=Landau.parity) (b:=true) l]; -- rw visits all zero caution
    refine visit_agree _ _ (fun x i r he=>?_); rw [Finset.sum_eq_zero]; intro j _; rw [strange _ (by rw [← he] at h; simpa using h),mul_zero]

-- roof estimate in position.
lemma shiftLimit (F:Dot G Cover) (hF: Book.Limit F.val v)(x:Cover): Limit (Lab.Shift x F).val v:= Limit.shades F hF _
lemma rootLimit (H: Limit F.val u) (K: Limit S.val v): Limit ((Spectrum G).touch F S).val (u+v-2):= by
    have he (i x)(F:Dot G Cover)(H:Limit F.val u): Limit (force i x F).val (u-1):= by obtain ⟨s,hs⟩:=obliges F; rw [force_at F hs,sum_stack]; exact Limit.sum _ (fun j _=> shiftLimit _ (H.tip _) _)
    obtain ⟨s,hs⟩:=obliges S; rw [Bonded.touching,sum_stack]; refine Limit.sum _ (fun j _=> Limit.smul _ ?_); simp_rw [root_at F S _ _ hs,sum_stack]; -- `simp_rw` may lost ∆ sign and LinearMap
    apply Limit.sum; intro k _; rw [show u+v-2=u-1+(v-1) by omega,spot_eq]; exact ((((he _ _ F H).signs _).pair (K.tip _))).add ((he _ _ (twisted DotFlip _ F) (H.signs _)).pair (K.tip _))
lemma lapLimit (H: Limit F.val v) : Limit ((Spectrum G).Lap F).val (v-2):= by
   rw [show v-2=(v-1)-1 by omega, Bonded.lap_at,sum_stack]; refine Limit.sum _ (fun i _=> Limit.smul _ ?_); obtain ⟨s,hs⟩:= obliges F; rw [heart_by _ _ F hs,sum_stack]; exact Limit.sum _ fun j _=> ((H.tip _).tip _)
lemma just_Q (h: Fits F H n v false)(ht:Tuned F u): Fits ((Spectrum G).touch (core G 0) F) (natQ H) n (v+1) false:= by unfold Fits; rw [show run _=Flux.tree Landau.parity (Kzone G) (s₀ G) (run F) from funext (touching (core G 0) F),Vin,mask_raises]; exact table_fit h; exact tied.sym F ht.symm
-- includes rank caps. exact bare term δ
lemma early_δ (h: Fits F H n v false)(ht:Tuned F u)(he:Limit F.val n) : Fits (((Spectrum G).Lap F)+(Spectrum G).touch (core G 0) F) (natQ H) n (v+1) false:= by
   suffices he : Fits ((Spectrum G).Lap F) 0 n (v+1) false from zero_add (natQ H) ▸ he.add (just_Q h ht)
   unfold Fits; rw [show Book.mask n (run ((Spectrum G).Lap F))=0 from ?_]; exact face_zero _
   let hw:= oneRank (lapLimit he); ext i; by_cases hx:(i.length:ℤ)=n; exact (enough _ hx).trans (hw i (by omega)); exact strange _ hx
end YM.MS.Lifting
