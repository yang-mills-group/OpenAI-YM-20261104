import YM.RG11Scheme.Stencil.Reading

/-! Compact-column integration by parts for the discrete horizontal covariance. -/
set_option autoImplicit false
set_option maxHeartbeats 180000
noncomputable section
namespace YM.RG11Scheme.Stencil
open Filter Function Lattice Set Mesh
open scoped BigOperators Classical
variable {E : Type} {I : Type*} {J : Type*}[Fintype J]
lemma product_finite [Zero E] (B : I×J → E) (h : ∀ j:J, HasFiniteSupport fun i:I=> B (i,j)) : B.HasFiniteSupport := by
   classical
   have ht : (⋃ j:J,(fun i => (i,j)) '' support (fun i=>B (i,j))).Finite := Set.finite_iUnion (fun j=>(h j).image _)
   exact ht.subset (fun ⟨i,j⟩ hij=>mem_iUnion.mpr ⟨j,i,hij,rfl⟩)
lemma plus_compact [Zero E] {a:Cover} {U:Cover → E} (h:U.HasFiniteSupport) : HasFiniteSupport fun x => U (x+a) := (HasFiniteSupport.fun_comp_of_injective (Equiv.addRight a).injective h)
lemma minus_compact [Zero E]{a:Cover} {U:Cover → E} (h:U.HasFiniteSupport) : HasFiniteSupport fun x => U (x-a) := by simp only [sub_eq_add_neg]; exact plus_compact h
lemma lump [Zero E] {B:link→E} (h:B.HasFiniteSupport) (i:Axis) : HasFiniteSupport fun x:Cover=> B (x,i) := HasFiniteSupport.fun_comp_of_injective (g:=fun x:Cover => (x,i)) (fun _ _ e=>congrArg Prod.fst e) h
lemma grad_compact [AddCommGroup E] {U:Cover→E} (h:U.HasFiniteSupport) : HasFiniteSupport (gradient U) := product_finite _ (fun i=> h.sub (plus_compact (a:=step i) h))
lemma curl_compact [AddCommGroup E] {B:link→ E} (h:B.HasFiniteSupport) (i j:Axis) : HasFiniteSupport fun x:Cover=>curl B x i j :=
   (((lump h i).add (plus_compact (a:=step i) (lump h j))).sub (lump h j)).sub (plus_compact (a:=step j) (lump h i))
lemma opposite_face [AddCommGroup E] (B:link→ E) (x i j) : curl B x j i = - curl B x i j := by unfold curl;abel
lemma charge_grad {G:Gauge} {ε:Cover→G.Color} (h:ε.HasFiniteSupport) : Summable fun p:link => ‖gradient ε p‖ := by apply summable_of_hasFiniteSupport; exact (grad_compact h).comp norm_zero
lemma interchange [NormedAddCommGroup E] [CompleteSpace E] (f : J→I→E) (h:∀ j:J,Summable (f j)) : (∑' i:I,∑ j:J, f j i)=∑ j:J,∑' i:I, f j i := by exact Summable.tsum_finsetSum (fun j _=>h j)
variable {G:Gauge}
lemma pay_dot {U V:I→G.Color} (h:V.HasFiniteSupport) : HasFiniteSupport fun i=> inner ℝ (U i) (V i) := (show (support V).Finite from h).subset (fun i hi=>by contrapose! hi; simp at hi; simp [hi])
def hit (A B:Bond G)(x i j) := inner ℝ (curl A x i j) (B (x,i)-B (x+step j,i))
def fee (A B:Bond G) (x i j) := if i<j then inner ℝ (curl A x i j) (curl B x i j) else 0
def variational (A B:Bond G) x := ∑ i:Axis,∑ j:Axis, fee A B x i j
lemma hit_finite {A B:Bond G}(h:B.HasFiniteSupport) (i j) : HasFiniteSupport fun x:Cover=> hit A B x i j := pay_dot (V:=fun x=>B (x,i)-B (x+step j,i)) ((lump h i).sub (plus_compact (a:=step j) (lump h i)))
lemma fee_finite {A B:Bond G}(h:B.HasFiniteSupport) (i j) : HasFiniteSupport fun x=> fee A B x i j := by
    unfold fee; split
    · exact pay_dot (curl_compact h i j)
    exact hasFiniteSupport_zero
lemma variational_finite {A B:Bond G} (h:B.HasFiniteSupport) : HasFiniteSupport (variational A B) := HasFiniteSupport.sum (fun i=> HasFiniteSupport.sum (fun j=> fee_finite (A:=A) h i j) _) _
lemma hitting (A B:Bond G) (x i j) : fee A B x i j = if i<j then hit A B x i j + hit A B x j i else 0 := by
   unfold fee; split_ifs; swap; · rfl
   unfold hit; rw [opposite_face A x i j]; unfold curl; simp only [inner_neg_left,inner_add_left,inner_add_right,inner_sub_left,inner_sub_right]; abel
theorem booking (A B:Bond G) (x:Cover) : variational A B x=∑ i:Axis,∑ j:Axis,hit A B x i j := by
   simp_rw [variational,hitting]
   have hw (i j : Axis) : hit A B x i j=(if i<j then hit A B x i j else 0)+(if j < i then hit A B x i j else 0) := by
       split_ifs with hp he
       · exact (lt_asymm hp he).elim
       · simp
       · simp
       have he':i=j:=le_antisymm (le_of_not_gt (by assumption)) (le_of_not_gt hp)
       subst j; unfold hit; rw [show curl A x i i=0 from by unfold curl; abel]; simp
   conv_rhs => enter [2,i,2,j]; rw [hw i j]
   simp_rw [ite_add_zero,Finset.sum_add_distrib]
   congr 1
   exact Finset.sum_comm
lemma entry_post (A B:Bond G) (i j:Axis) (_h:B.HasFiniteSupport) : (∑' x:Cover,inner ℝ (curl A (x-step j) i j) (B (x,i)))=∑' x:Cover,inner ℝ (curl A x i j) (B (x+step j,i)) := by
   let R : Cover ≃ Cover := Equiv.addRight (step j)
   let f := fun x:Cover => inner ℝ (curl A (x-step j) i j) (B (x,i))
   change tsum f=_
   apply (R.tsum_eq f).symm.trans
   apply congrArg (tsum (L:=SummationFilter.unconditional Cover)); funext x
   have he : R x=x+step j:=rfl
   simp only [he]
   change inner ℝ (curl A (x+step j-step j) i j) (B (x+step j,i))=_; rw [add_sub_cancel_right]
lemma sums (A B:Bond G) (i j : Axis) (h:B.HasFiniteSupport) : (∑' x:Cover, hit A B x i j) = ∑' x:Cover, inner ℝ (curl A x i j-curl A (x-step j) i j) (B (x,i)) := by
   have hu (f:Cover→G.Color) (v:Cover→G.Color) (hv:v.HasFiniteSupport) : Summable fun x => inner ℝ (f x) (v x) := summable_of_hasFiniteSupport (pay_dot hv)
   simp_rw [hit,inner_sub_left,inner_sub_right]
   rw [Summable.tsum_sub (hu _ _ (lump h i)) (hu _ _ (plus_compact (a:=step j) (lump h i))), Summable.tsum_sub (hu _ _ (lump h i)) (hu _ _ (lump h i)), entry_post _ _ _ _ h]
lemma bounty (A B:Bond G) (h:B.HasFiniteSupport) : (∑' x:Cover,variational A B x)=∑' p:link,inner ℝ (starCurl A p.1 p.2) (B p) := by
   rw [(summable_of_hasFiniteSupport (pay_dot (U:=fun p=> starCurl A p.1 p.2) h)).tsum_prod']
   rotate_left
   · intro a; exact (hasSum_fintype ..).summable
   simp_rw [tsum_fintype, booking]
   have H (i j :Axis) : Summable (fun x:Cover=> hit A B x i j) := summable_of_hasFiniteSupport (hit_finite h i j)
   have K (i j :Axis) : Summable (fun x:Cover=> inner ℝ (curl A x i j - curl A (x-step j) i j) (B (x,i))) := summable_of_hasFiniteSupport (pay_dot (lump h i))
   calc _ = ∑ i:Axis,∑ j:Axis,∑' x:Cover,hit A B x i j := (interchange (fun i (x:Cover)=>∑ j:Axis,hit A B x i j) (fun i=> summable_sum (fun j (_:j∈Finset.univ)=> H i j))).trans (Finset.sum_congr rfl fun i _=> interchange (fun j x=> hit A B x i j) (H i))
        _ = _ := by
           simp_rw [sums _ _ _ _ h,starCurl,sum_inner]
           let eq₂ : (∑ i:Axis,∑ j:Axis,∑' x:Cover,inner ℝ (curl A x i j-curl A (x-step j) i j) (B (x,i))) = ∑ i:Axis,∑' x:Cover,∑ j:Axis,inner ℝ (curl A x i j-curl A (x-step j) i j) (B (x,i)) := (Finset.sum_congr rfl (fun i _=> (interchange (fun j x=> inner ℝ (curl A x i j-curl A (x-step j) i j) (B (x,i))) (K i)).symm))
           exact eq₂.trans ((interchange (fun i (x:Cover)=>∑ j:Axis, inner ℝ (curl A x i j - curl A (x-step j) i j) (B (x,i))) (fun i=> summable_sum (fun j (_:j∈Finset.univ)=> K i j))).symm)
theorem collects {A:Dual G} (hA:horizontal A) (hp:brief A) {B:Bond G} (h:B.HasFiniteSupport) : (∑' x:Cover, variational (ray A) B x)=A B := by
   rw [bounty _ _ h,cupboard hp]
   exact tsum_congr (fun p=> by rw [ray_rest hA, real_inner_comm])
end YM.RG11Scheme.Stencil
