import YM.RG11Scheme.Stencil.Belt

/-! Convert finite monomials of planar-link Fourier into arbitrary native root differences. Verified on all functions (not only zero-mode Laplace line). -/
set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
namespace YM.RG11Scheme.Stencil.Point
open Filter Set Function Lattice Mesh Maxwell Pert Pert.Full Align Align.Atom
open scoped Matrix.Norms.Frobenius BigOperators Classical Topology ContDiff
variable {G:Gauge} {n:Side} {j:ℕ}
-- funext local derivatives
variable {E: Type} [AddCommGroup E]
lemma plus_go (f g:Cover→E) (D) (x): go D (f+g) x=go D f x+go D g x := by induction D generalizing x with|nil=>rfl|cons i D ih => simp only [onwards,ih]; abel
lemma go_map {Y:Type}[AddCommGroup Y](L:E →+ Y)(f : Cover → E) (D x) : go D (fun k=> L (f k)) x = L (go D f x) := by induction D generalizing x with|nil=>rfl|cons i D ih=>simp only [onwards, ih,map_sub]
lemma go_brief (D) (x): brief fun f:Cover→E=>go D f x := by induction D generalizing x with|nil=>exact brief.one x|cons i D ih=>exact (ih (x+step i)).combine (ih x) (· - ·)
lemma specs (D) (p x : Site n) : go D (char p) x=char p x * Band.claw D p := by
   induction D generalizing x with
   | nil => simp [Band.claw]
   | cons i D IH => rw [onwards, IH,IH,char_add]; unfold Band.claw; simp only [List.map_cons,List.prod_cons];ring
lemma convolution (f:Site n→ℂ) : ∃ F:Site n→ℂ, f = ∑ p:Site n,F p • char p := by
    
    let F (p:Site n):=(n.val:ℂ)^(-4:ℤ) * ∑ x:Site n, f x * char p (-x)
    refine ⟨F,?_⟩; funext x
    have he (t : Site n) : ∑ p:Site n, f t*char p (-t)*char p x=f t*(if t=x then (n.val:ℂ)^4 else 0) := by
       simp only [mul_assoc,←char_add];rw [←Finset.mul_sum]; simp only [show -t+x=x-t by abel, show ∀ p:Site n,char p (x-t)=char (x-t) p from fun p => Full.swap _ _,scan,sub_eq_zero, eq_comm (a:=x) (b:=t)]
    rw [Finset.sum_apply]; simp_rw [Pi.smul_apply, smul_eq_mul,F,mul_assoc _ (∑ i, _) (char _ _),Finset.sum_mul]
    rw [←Finset.mul_sum (s:=Finset.univ)]; conv_rhs => arg 2; rw [Finset.sum_comm]; simp only [he,mul_ite, mul_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true]
    field_simp
def go_side : List Axis→Site n→ (Site n→ℂ)→ₗ[ℂ]ℂ
 | [],x => LinearMap.proj x
 | i::D,x=> go_side D (x+step i)-go_side D x
lemma go_side_apply (D) (x:Site n)(f:Site n→ℂ) : go_side D x f=go D f x := by induction D generalizing x with|nil=>rfl|cons i D ih=> unfold go_side; rw [LinearMap.sub_apply,onwards,ih,ih]
def enters (p : Atom j) (b:Bool) (n:Side) : (Site n→ℂ)→ₗ[ℂ]ℂ := ∑ q:Kind j, (p.degree q:ℂ) • LinearMap.proj (wrap n (coverMul b (p.offset q)))
lemma engages (p : Atom j)(b:Bool)(f:Site n→ℂ) : ((p.orientation b:ℂ) * go p.dirs f (wrap n (p.foot b))) = ∑ k,(p.degree k:ℂ)*f (wrap n (coverMul b (p.offset k))) := by
   let X : (Site n→ℂ)→ₗ[ℂ]ℂ := (p.orientation b:ℂ) • go_side p.dirs (wrap n (p.foot b))
   have H (t:Site n) : X (char t)= enters p b n (char t) := by
      unfold X enters; simp only [LinearMap.smul_apply,LinearMap.sum_apply,LinearMap.proj_apply,smul_eq_mul]
      rw [go_side_apply,specs,p.phaseA];ring
   obtain ⟨K,h⟩:= convolution f
   calc _ = X f := by unfold X; rw [LinearMap.smul_apply,go_side_apply];exact rfl
        _ = enters p b n f := by rw [h,map_sum,map_sum];simp_rw [map_smul,H]
        _ = _ := by unfold enters; simp [LinearMap.sum_apply]

private def C := itinerary 2 (by simp)
lemma covers (p:Atom j)(b:Bool)(f:Cover→ℂ) : (p.orientation b:ℂ)*go p.dirs f (p.foot b)=∑ k,(p.degree k:ℂ)*f (coverMul b (p.offset k)) := by
    let n i := C.period i
    let g (i:ℕ):= f ∘ (lift (n:=n i))
    let Z := (go_brief p.dirs (p.foot b) (E:=ℂ)).choose
    have hp (i : ℕ) (u : Cover) (hu : lift (wrap (n i) u)=u) : g i (wrap (n i) u)=f u := congrArg f hu
    obtain ⟨i,h,H⟩ := ((eventually_all_finset Z).mpr (fun k _=>placement k C) |>.and (show ∀ᶠ i in atTop, ∀ k:Kind j, lift (wrap (n i) (coverMul b (p.offset k)))=coverMul b (p.offset k) from eventually_all.mpr fun k : Kind j=> placement (coverMul b (p.offset k)) C)).exists
    have hv : go p.dirs f (p.foot b)= go p.dirs (g i) (wrap (n i) (p.foot b)) := by
       rw [←periodic]; exact (go_brief p.dirs (p.foot b) (E:=ℂ)).choose_spec _ _ (fun a ha=> Eq.symm (hp i a (h a ha)))
    rw [hv,engages]; exact Finset.sum_congr rfl (fun k _=> by rw [hp i _ (H k)])
lemma detection (p:Atom j)(b:Bool)(f:Cover→ℝ) : p.orientation b * go p.dirs f (p.foot b)=∑ k,p.degree k*f (coverMul b (p.offset k)) := by
   apply Complex.ofReal_injective
   have h:=covers p b (fun k=> (↑(f k):ℂ)); rw [show go p.dirs (fun k=> (↑(f k):ℂ)) _ = _ from go_map Complex.ofRealHom.toAddMonoidHom f p.dirs (p.foot b)] at h
   push_cast; exact h
lemma onto (p:Atom j)(b:Bool)(U:Cover→ G.Color) : p.orientation b • go p.dirs U (p.foot b) = ∑ k,p.degree k • U (coverMul b (p.offset k)) := by
   ext c; simp only [WithLp.ofLp_sum,Finset.sum_apply, PiLp.smul_apply,smul_eq_mul]; rw [← detection p b (fun v=> U v c)];exact congrArg _ (go_map ((PiLp.proj (𝕜:=ℝ) 2 (fun _:G.ColorIndex=>ℝ) c).toLinearMap.toAddMonoidHom) U _ _).symm
lemma tuned (p:Atom j)(A : Bond G): p.readK A 0=p.factor • go p.dirs (fun x=> A (x,p.rotated)) (p.foot true) := by
   rw [read_cover]; exact (onto p true (fun x=>A (x,p.rotated))).symm
end YM.RG11Scheme.Stencil.Point
