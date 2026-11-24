import YangMills.WilsonProof.NativeSupport.YM.MS.Lifting.Span
/-!
# Fitting graded symbols at birth

Along rays for later high-momentum master. Total grade includes dim. `Frame`
 for one rank after slicing in either mark or bulk sectors. No test support implicitly.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Lifting
open Function Filter Set Finset Plane Koszul Color Real Momentum Wire Tensor Book
open Local Local.BV Landau Detect Detect.Mark
open Complex (I)
open scoped Topology ContDiff BigOperators
variable {A P: Type}{p:Sector A}{b:Bool}
structure Rest (f:ℝ→ℂ)(v:ℤ)(c:ℂ): Prop where
    smooth : ContDiff ℝ ∞ f
    bottom : v < 0 → c=0
    home (j:ℕ): (j:ℤ)≤v→ reading j f= if (j:ℤ)=v then c else 0
namespace Rest
variable {f g:ℝ→ℂ}{v b:ℤ}{c d:ℂ}
lemma level (H: ContDiff ℝ ∞ f) (h:f 0=c): Rest f 0 c:= ⟨H,fun i=>by omega,fun i hi=>by obtain rfl:i=0:=(by omega); simpa [reading] using h⟩
lemma one (H: ContDiff ℝ ∞ f)(h:f 0=0)(h':HasDerivAt f c 0): Rest f 1 c:= by
   refine ⟨H,fun i=>by omega,fun j hj=>?_⟩; have hh:j≤1:= (by omega); interval_cases j <;> simp [reading,h,h'.deriv]
lemma zero (v:ℤ): Rest (fun _=>0) v 0:= ⟨contDiff_const,fun h=>rfl,fun j h=>by simp [reading]⟩
lemma smul (a:ℂ)(H:Rest f v c): Rest (fun t=>a * f t) v (a*c):= ⟨contDiff_const.mul H.smooth,fun h=>by rw [H.bottom h,mul_zero],fun j h=> by rw [read_const,H.home j h]; split <;> simp⟩
lemma add (H:Rest f v c)(h:Rest g v d): Rest (fun t=>f t + g t) v (c+d):= ⟨H.smooth.add h.smooth,fun v=>by rw [H.bottom v,h.bottom v,zero_add],fun j ht=> by rw [read_add H.smooth h.smooth,H.home j ht,h.home j ht]; split <;> simp⟩
lemma sub (H:Rest f v c)(h:Rest g v d): Rest (fun t=>f t-g t) v (c-d):= by simpa only [neg_one_mul,sub_eq_add_neg] using H.add (h.smul (-1))
lemma sum {f:A→ℝ→ℂ}{x:A→ℂ} (s:Finset A)(h:∀ i∈s,Rest (f i) v (x i)): Rest (fun t=> ∑ i∈s,f i t) v (∑ i∈s,x i):= by
    classical
    induction s using Finset.induction with
    | empty=> simpa using zero v
    | insert a s ha ih=> simp_rw [Finset.sum_insert ha]; exact (h a (Finset.mem_insert_self ..)).add (ih (fun i hi=> h i (mem_insert_of_mem hi)))
lemma mul (H:Rest f v c)(h:Rest g b d): Rest (fun t=>f t*g t) (v+b) (c*d):= by
   refine ⟨H.smooth.mul h.smooth,fun i=>?_ ,fun j hj=>?_⟩; · by_cases he:v<0; rw [H.bottom he,zero_mul]; rw [h.bottom (by omega),mul_zero]
   rw [read_mul H.smooth h.smooth]; let T k:= reading k f * reading (j-k) g; change ∑ k∈ Finset.range (j+1), T k= _
   have hx k (he: k∈ Finset.range (j+1)) (hv : (k:ℤ)≠v ∨ ↑(j-k)≠ b): T k=0:= by
       have hw := Finset.mem_range.mp he; by_cases hk:(k:ℤ)<v; unfold T; rw [H.home k hk.le,if_neg hk.ne,zero_mul]; have hz:(↑(j-k):ℤ)<b:= (by omega); unfold T; rw [h.home (j-k) hz.le,if_neg hz.ne,mul_zero]
   split
   next ht=>
       rcases lt_or_ge v 0 with hi|hi; rw [H.bottom hi,zero_mul]; exact Finset.sum_eq_zero (fun x he=> hx x he (by omega))
       rcases lt_or_ge b 0 with hv|hv; rw [h.bottom hv,mul_zero]; exact Finset.sum_eq_zero (fun x he=> hx x he (by omega))
       rw [Finset.sum_eq_single v.toNat (fun x he hh=> hx x he (by omega)) (fun he=>by simp only [Finset.mem_range] at he; omega)]; unfold T; rw [H.home v.toNat (by omega),h.home (j-v.toNat) (by omega),if_pos (by omega),if_pos (by omega)]
   next ht=> exact Finset.sum_eq_zero fun x he=> hx x he (by obtain he:= Finset.mem_range.mp he; omega)
lemma scattered (s:Legs A) (p:Sector A) (S:ℝ→ Shared A ℂ)(C:Shared A ℂ)(H:∀ i j, Split i j s→ Rest (fun t=> S t i j) v (C i j)): Rest (fun t=> scatter p s (S t)) v (scatter p s C):= by
   induction s generalizing S C with
   | nil=> exact H _ _ .nil
   | cons a l ih=> exact ih _ _ (fun i j h=> (H _ _ h.left).add ((H _ _ h.right).smul _))
end Rest
variable [NormedAddCommGroup P][NormedSpace ℝ P]{m:A→ℤ}{v u:ℤ}{F K H S:Row A P ℂ}
def Face (m:A→ℤ)(H F: Row A P ℂ)(v:ℤ)(b:Bool): Prop:= ∀ w, Course b w→ Rest (fieldVal H (ray w)) (v-fieldDim m w) (F w)
lemma faces (h:Face m F K v false)(w): Rest (fieldVal F (ray w)) (v-fieldDim m w) (K w):= h w (fun u=> Bool.noConfusion u)
lemma face_here (h:Face m F K v b) {w:Legs (Mode A P)} (he:Course b w)(j:ℕ) (hv:fieldDim m w+j≤v) : torch j F w=if fieldDim m w+j=v then K w else 0:= by
   rw [torch_at,show reading j (fun t=>F (sail (ray w) t))=_ from (h w he).home j (by omega)]; split <;> split <;> first| rfl| omega
lemma faceAt {n:ℕ}(h:Face m (Book.mask n F) K v false){w:Legs (Mode A P)}(he:w.length=n)(j:ℕ)(hv:fieldDim m w + j ≤v): torch j F w= if fieldDim m w+j=v then K w else 0 := by
    rw [← face_here h (w:=w) (fun v=>Bool.noConfusion v) j hv]; unfold torch; rw [show fieldVal (Book.mask _ _) (ray w)= fieldVal F (ray w) from funext fun t=> enough _ (by simp [he])]
omit [NormedSpace ℝ P] [NormedAddCommGroup P] in
lemma scatter_move (F:Shared (Mode A P) ℂ)(f:Mode A P→ Mode A P) (h:∀ i, (f i).1=i.1) (w:List (Mode A P)) : scatter (field p) (w.map f) F = scatter (field p) w (fun l k=> F (l.map f) (k.map f)):= by
    induction w generalizing F with
    | nil=> rfl
    | cons a l ih=>
       rw [List.map_cons,scatter_cons,ih,scatter_cons]; congr! 2; simp only [List.map_cons,field,h]; have he (x:List (Mode A P)): degree (field p) (x.map f)=degree (field p) x:= by induction x with| nil=>rfl| cons a l ih=> simp only [List.map_cons,degree_cons,ih,field,h]
       rw [he]
lemma face_add (h:Face m H F v b)(hs:Face m S K v b): Face m (H+S) (F+K) v b:= fun i hi=> (h i hi).add (hs i hi)
lemma face_mul (r:ℂ)(h:Face m H F v b): Face m (r • H) (r • F) v b:= fun i hi=> (h i hi).smul r
lemma face_zero (v:ℤ): Face m (P:=P) 0 0 v b:= fun _ _=> Rest.zero _
lemma face_sum {J:Type}{F H:J→Row A P ℂ}{u:Finset J}(h:∀ i∈u, Face m (H i) (F i) v b): Face m (∑ i∈u,H i) (∑ i∈u,F i) v b:= by
    intro w hw; unfold fieldVal; simp_rw [Finset.sum_apply]; exact Rest.sum u (fun i hi=> h i hi w hw)
lemma face_product (h:Face m H F v false)(ht:Face m S K u false): Face m (product (field p) H S) (product (field p) F K) (v+u) false:= by
    intro w hw; have he (t:ℝ): fieldVal (product (field p) H S) (ray w) t=scatter (field p) w (fun l r=> fieldVal H (ray l) t * fieldVal S (ray r) t):= by simp_rw [fieldVal,scattered,ray_go]; exact scatter_move _ (fun i:Mode A P=> (i.1,t • i.2)) (fun _=>rfl) _
    rw [funext he,scattered]; refine Rest.scattered w _ ((fun t l k=> fieldVal H (ray l) t*fieldVal S (ray k) t)) (fun l k=> F l*K k) ?_ 
    intro l r he; have hv := split_perm he; have hz := (hv.map (fun i=>m i.1)).sum_eq
    rw [show v+u-fieldDim m w=(v-fieldDim m l)+(u-fieldDim m r) by
        have hx : fieldDim m l+fieldDim m r=fieldDim m w:=by simpa [fieldDim,Function.comp_def] using hz
        omega]
    exact (faces h l).mul (faces ht r)
end YM.MS.Lifting
