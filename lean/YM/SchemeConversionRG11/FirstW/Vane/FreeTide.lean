import YM.SchemeConversionRG11.FirstW.Vane.Tone
/-! Exact use of exterior Taylor tensors on nonwrapping stencils. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.FirstW
open Function Set Metric Lattice Pert Align Topology Maxwell Filter
open scoped BigOperators Classical
variable {G : Gauge} {X : Type*} [AddCommGroup X] [One X] {n : Side}
def terms (x : Site n) : FullT G n→ₗ[ℝ] Wind G ℤ := LinearMap.pi fun i=> LinearMap.proj (wrap n i.1+x,i.2)
def tracing (x : Four X) : Wind G X→ₗ[ℝ] Wind G X:= LinearMap.pi fun i=> LinearMap.proj (i.1+x,i.2)
lemma rail_site (A : FullT G n) (x : Site n) (v : Cover) (i : Step) : boardAt v i (terms x A)=boardAt (wrap n v+x) i A := by
  cases i with | mk t h=> cases h <;> simp [boardAt,terms,Step.used,sub_add_eq_add_sub]
lemma rail_wrap (A : FullT G n) (x : Site n) (v : Cover) (p : Walk): rail v p (terms x A)=rail (wrap n v+x) p A := by induction p generalizing v with
  | nil=> simp [rail]
  | cons i p ih=>rw [rail,rail,LinearMap.add_apply,LinearMap.add_apply,rail_site,ih,map_add,wrap_vec,add_right_comm _ _ x]
lemma swerve_wrap (A B : FullT G n) (x : Site n) (v : Cover) (p:Walk): swerve v p (terms x A) (terms x B)=swerve (wrap n v+x) p A B := by induction p generalizing v with
  | nil=>simp [swerve]
  | cons i p ih=> rw [swerve_eq,swerve_eq, ih, rail_wrap, rail_site, map_add,wrap_vec,add_right_comm _ _ x]
lemma terms_pull (s : Signed) (A : FullT G n) (v : Site n): Bare.wideLink G s (terms v A)= terms (s⁻¹.act v) (Bare.wideLink G s A) := by
  funext i; simp only [terms,Bare.wideLink_apply,LinearMap.pi_apply,LinearMap.proj_apply,Step.used]; split_ifs <;> simp [wrap_signed, add_sub_right_comm]
lemma stop_owned (x : Site n) (v : Cover) (p : Walk):wrap n (stop v p)+x= stop (wrap n v+x) p := by induction p generalizing v with
  | nil=>rfl
  | cons i p ih=> rw [stop, ih, stop,map_add,wrap_vec,add_right_comm _ _ x]
lemma glint_wrap (A B : FullT G n) (x : Site n) (v : Cover) (j) : glint v j (terms x A) (terms x B)=glint (wrap n v+x) j A B := by
  have hv (A B: FullT G n) : sheer _ _ v (terms x A) (terms x B)=sheer G j (wrap n v+x) A B := by
    simp_rw [sheer_eq]; refine congrArg _ (Finset.sum_congr rfl (fun s _=>?_)); rw [terms_pull,terms_pull]; apply congrArg _; apply congrArg _; funext i a p; simp [rush,swerve_wrap,affine]
  simp_rw [glint_once,hv]
lemma spin_wrap (A : FullT G n) (x : Site n) (v : Cover) (h : ℝ) (j) : Bare.wideLinear G j h v (terms x A)=Bare.wideLinear G j h (wrap n v+x) A := by
  have he (A : FullT G n) (x : Site n) (v : Cover) (i a:Axis): Bare.wideCurl (terms x A) v i a=Bare.wideCurl A (wrap n v+x) i a := by rw [←frontRail,←frontRail,rail_wrap]
  have hr (A: FullT G n) (x : Site n) (v : Cover) : Bare.wideCore G j v (terms x A)=Bare.wideCore G j (wrap n v+x) A := by
    funext i b p; simp_rw [Bare.wideCore_apply,he]; apply congrArg _; apply Finset.sum_congr rfl; intro z _; simp [add_right_comm (wrap n v)]
  simp only [Bare.wideLinear,LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, terms_pull,hr]; simp [affine]
lemma native_wrap (A : FullT G n) (x : Site n) (v : Cover) (k : Labels.Key G) : native k v (terms x A)=native k (wrap n v+x) A := by simp only [native,tape,LinearMap.comp_apply, spin_wrap]
lemma echo_wrap (A B : FullT G n) (x : Site n) (v : Cover) (k : Labels.Key G) : echoAt v k (terms x A) (terms x B)= echoAt (wrap n v+x) k A B := by simp only [echoAt, LinearMap.compr₂_apply,glint_wrap]
lemma rail_translate (A : FullT G n) (x v:Site n) (p:Walk) : rail x p (tracing v A)=rail (x+v) p A := by
  have he : terms x (tracing v A)=terms (x+v) A := funext (fun b=>by simp [terms,tracing,add_assoc]); simpa only [map_zero,zero_add, rail_wrap] using congrArg (fun B:Wind G ℤ=>rail 0 p B) he
lemma tower_wrap (A B C : FullT G n) (x : Site n) (v : Cover) (s:Walk): tower _ v s (terms x A) (terms x B) (terms x C)=tower G (wrap n v+x) s A B C := by simp only [tower_eq,rail_wrap,spire, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.flip_apply,swerve_wrap]
lemma tower_translate (A B C : FullT G n) (x y : Site n) (w:Walk) : tower G x w (tracing y A) (tracing y B) (tracing y C)= tower G (x+y) w A B C := by
  have h (A:FullT G n): terms x (tracing y A)=terms (x+y) A := funext (fun b=>by simp [terms,tracing,add_assoc]); have H:=tower_wrap (tracing y A) (tracing y B) (tracing y C) x 0 w; simpa only [h,tower_wrap,map_zero,zero_add] using H.symm
lemma letter_translate (A : FullT G n) (x y : Site n) (k : Labels.Key G) : native k x (tracing y A)=native k (x+y) A := by
  have h (A:FullT G n): terms x (tracing y A)=terms (x+y) A := funext (fun b=>by simp [terms,tracing,add_assoc]); have H := native_wrap (tracing y A) x 0 k; simpa only [h,native_wrap,map_zero,zero_add] using H.symm
lemma echo_translate (A B : FullT G n) (x y : Site n) (k : Labels.Key G) : echoAt x k (tracing y A) (tracing y B)=echoAt (x+y) k A B := by
  have h (A:FullT G n): terms x (tracing y A)=terms (x+y) A := funext (fun b=>by simp [terms,tracing,add_assoc]); have H := echo_wrap (tracing y A) (tracing y B) x 0 k; simpa only [h,echo_wrap,map_zero,zero_add] using H.symm
lemma consumes (x y : Site n) (k : Labels.Key G) : tracing y (canal k x)=canal k (x-y) := by
  funext i; simp only [tracing,LinearMap.pi_apply,LinearMap.proj_apply]; rcases i with ⟨v,i⟩; dsimp only
  rw [carried,carried (o:=x-y)]; rw [show v+y-x=v-(x-y) by abel]
end YM.RG11.FirstW
