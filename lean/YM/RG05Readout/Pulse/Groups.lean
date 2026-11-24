import YM.RG05Readout.Pulse.Learn
/-! Mixed jet engines using only REAL multilinear smooth variation.
 Price or representation equality on exact discrete sample locations.D
 -/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Pulse
open Tensor Analysis Function Filter Set MeasureTheory Native
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {V:Type*}[Fintype V][DecidableEq V]{n m d k:ℕ} {E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E]
noncomputable def lat (k:Letter d)(i:E4→E): Complexion E→ₗ[ℂ] Complexion E := ∑ u∈paint k,ink k u • tires (i u) (depth k)
lemma values (k:Letter d)(i:E4→E)(x:Complexion E)(z:E): (lat k i x).val z = ∑ u∈paint k, ink k u* Tensor.diagonal (iteratedFDeriv ℝ (depth k) x.val z) (i u):=by
   simp only [lat,LinearMap.sum_apply,LinearMap.smul_apply,AddSubmonoidClass.coe_finsetSum,SetLike.val_smul,Finset.sum_apply]; refine Finset.sum_congr rfl fun s _=> ?_; rw [Pi.smul_apply,rim_flat]; rfl
lemma lat_horiz (k:Letter d)(i:E4→E)(f g:Complexion E){x:E}(h:pie f g (depth k+n) x): pie (lat k i f) (lat k i g) n x:=by
    let A(p:Complexion E):=fun u:E4=>ink k u • tires (i u) (depth k) p
    have ht(p:Complexion E):iteratedFDeriv ℝ n (lat k i p).val x=∑ u∈paint k, ink k u • iteratedFDeriv ℝ n (tires (i u) (depth k) p).val x:=by
       rw [show lat k i p=∑ u∈ paint k, A p u from by simp only [lat,A,LinearMap.sum_apply,LinearMap.smul_apply]]; rw [AddSubmonoidClass.coe_finsetSum,iteratedFDeriv_sum_apply]; exact Finset.sum_congr rfl (fun _ _=> iteratedFDeriv_const_smul_apply (lit _ _|>.contDiffAt)); intro i _; exact (lit _ _).contDiffAt
    unfold pie; rw [ht,ht]; exact Finset.sum_congr rfl (fun i _=>congr_arg (ink k i • ·) (pie_tires _ h))
lemma lat_fork (k:Letter d) (i:E4→E)(v:Complexion E)(x:E)(r:ℝ): lat k i (fork r x v)=(↑r:ℂ)^(depth k) • fork r x (lat k i v):=by
    simp only [lat,LinearMap.sum_apply,LinearMap.smul_apply,map_sum,tire_fork, Finset.smul_sum,map_smul]; exact Finset.sum_congr rfl fun _ _=> smul_comm ..

abbrev Cloud (V:Type*):= V→E4
abbrev Wave (V:Type*)[Fintype V]:=Complexion (Cloud V)
local notation "W!"=> Wave V
local notation "X!"=> Cloud V

def joint (s:Finset V)(f:V→Body): W!:= ⟨fun x=>∏ i∈s,(f i).val (x i), show ContDiff ℝ ∞ _ from contDiff_prod (f:=fun i (x:Cloud V)=>(f i).val (x i)) (fun i _=> (show ContDiff ℝ ∞ (f i).val from (f i).property).comp (contDiff_apply _ _ _))⟩
lemma single_print (f:V→Body){s:Finset V}{i:V}(h:i∈s)(u:E4): one (Pi.single i u) (joint s f) = joint s (Function.update f i (one u (f i))) :=by
    apply Subtype.ext; funext x; let D:X! := Pi.single i u
    let w(j:V)(t:X!) := (f j).val (t j)
    let a(j:V) := ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _=>E4) j
    have he(j:V): fderiv ℝ (w j) x=(fderiv ℝ (f j).val (x j)).comp (a j):= (((body_smooth (f j) 1).differentiable (by norm_num) (x j)).hasFDerivAt.comp x (a j).hasFDerivAt).fderiv
    have hx(j): DifferentiableAt ℝ (w j) x:= (((body_smooth (f j) 1).differentiable (by norm_num) (x j)).comp x (a j).differentiableAt)
    change fderiv ℝ (fun z=> ∏ j∈s, w j z) x D=∏ j∈s, (Function.update f i (one u (f i)) j).val (x j)
    rw [fderiv_finsetProd (fun i _=>hx i)]; simp_rw [sum_apply]; rw [Finset.sum_eq_single i]; rotate_left
    · intro j hj hj'; rw [smul_apply,he]; have ht:D j=0:=Pi.single_eq_of_ne hj' _; rw [show ((fderiv ℝ _ _).comp _) D=(fderiv ℝ (f j).val (x j)) (D j) from rfl,ht,map_zero,smul_zero]
    · simp [h]
    rw [← Finset.prod_erase_mul s _ h,Function.update_self,smul_apply,he,ContinuousLinearMap.comp_apply,show a i D=u from Pi.single_eq_same ..]
    apply congr_arg (· * _); exact Finset.prod_congr rfl fun j hj=> congr_fun (congr_arg (fun x:Body=>x.val) (Function.update_of_ne (Finset.ne_of_mem_erase hj) _ _).symm) _
lemma wheel_print (f:V→Body){s:Finset V}{i:V}(h:i∈s)(u:E4)(k:ℕ): tires (Pi.single i u) k (joint s f)=joint s (Function.update f i (tires u k (f i))):=by
    induction k generalizing f with
    | zero=> simp only [tires,LinearMap.id_apply, Function.update_eq_self]
    | succ k ih=> rw [tires,tires,LinearMap.comp_apply,LinearMap.comp_apply,single_print f h,ih,Function.update_self,Function.update_idem] -- edit
lemma lat_print (f:V→Body){s:Finset V}{i:V}(h:i∈s)(k:Letter d) : lat k (fun u=> (Pi.single i u:X!)) (joint s f)=joint s (Function.update f i (lat k id (f i))):=by
    apply Subtype.ext; funext x; unfold lat; simp_rw [LinearMap.sum_apply,LinearMap.smul_apply,wheel_print f h]; let r:= ∏ j∈s.erase i,(f j).val (x j)
    have ht(v:Body):(joint s (Function.update f i v)).val x=r*v.val (x i):=by
       unfold r joint; change (∏ j∈s,(Function.update f i v j).val (x j))=_; rw [← Finset.prod_erase_mul s _ h,Function.update_self]; congr 1; exact Finset.prod_congr rfl (fun j hj=>by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)])
    rw [ht]; simp only [AddSubmonoidClass.coe_finsetSum,SetLike.val_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,ht,id_eq,Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _=>by rw [mul_left_comm])
variable (p:V→ℕ)(k:∀ i:V,Letter (p i))
noncomputable def machine : List V→ W! →ₗ[ℂ] W!
    | []=> LinearMap.id
    | (i::L) => machine L ∘ₗ lat (k i) (fun u=> (Pi.single i u:X!))
abbrev pegs (L:List V):ℕ := (L.map fun i=>depth (k i)).sum
lemma machine_print (L: List V)(h:L.Nodup)(s:Finset V) (hs:∀ i∈L,i∈s)(f:V→Body):
    let g:=fun i=> if i∈L then lat (k i) id (f i) else f i
    machine p k L (joint s f)=joint s g:=by
    intro g; induction L generalizing f with
    | nil=> simp [g,machine]
    | cons i L ih =>
       have h₀ := hs i (by simp); obtain ⟨hr,ht⟩:= List.nodup_cons.mp h
       rw [machine,LinearMap.comp_apply,lat_print f h₀,ih ht (fun i hi=>hs i (List.mem_cons_of_mem _ hi))]; congr 1; funext j; by_cases he:j=i
       · subst j; simp [g,hr]
       simp [g,he]
omit [Fintype V] in
lemma pegs_inc {s:Finset V}{L:List V}(h:L.Nodup)(hs:∀ i∈L,i∈s): pegs p k L ≤ ∑ i∈s,p i:=by induction L generalizing s with
    | nil => exact Nat.zero_le _
    | cons i L ih=> obtain ⟨hr,ht⟩:=List.nodup_cons.mp h; have hx:= ih (s:=s.erase i) ht (fun j hj=>Finset.mem_erase.mpr ⟨fun h=>hr (h ▸ hj),hs j (List.mem_cons_of_mem _ hj)⟩); rw [← Finset.add_sum_erase s p (hs i (by simp))]; exact add_le_add (Nat.le_of_lt_succ (k i).1.isLt) hx
omit [Fintype V][DecidableEq V] in
lemma pegs_step (i:V)(L:List V):pegs p k (i::L)=depth (k i)+pegs p k L:=rfl
lemma machine_flat (L:List V){f g:W!}{n:ℕ}{x:X!}(h:pie f g (pegs p k L+n) x): pie (machine p k L f) (machine p k L g) n x:=by
    induction L generalizing f g with
    | nil=> rw [show pegs p k []=0 from rfl, zero_add] at h; exact h
    | cons i L ih=> rw [pegs_step,add_assoc] at h; exact ih (lat_horiz _ _ _ _ h)
lemma machine_roll (L:List V)(r:ℝ)(x:X!)(p':W!): machine p k L (fork r x p')= (↑r:ℂ)^ pegs p k L • fork r x (machine p k L p'):=by
    induction L generalizing p' with
    | nil=> rw [show pegs p k []=0 from rfl,pow_zero,one_smul]; rfl
    | cons i L ih=> rw [machine,LinearMap.comp_apply,LinearMap.comp_apply,lat_fork,map_smul,ih, pegs_step,pow_add,smul_smul]
set_option quotPrecheck false
local notation "L!"=> (Finset.univ (α:=V)).toList
abbrev perform : W!→ₗ[ℂ] W!:=machine p k L!
lemma pegs_cost : pegs p k L! ≤ ∑ i:V,p i:=pegs_inc _ _ (Finset.nodup_toList _) (fun _ h=> Finset.mem_toList.mp h)
lemma finale (f: V →Body)(x:X!) : (perform p k (joint Finset.univ f)).val x=∏ i:V,readJ (k i) (x i) (f i):=by
    rw [perform,machine_print _ _ _ (Finset.nodup_toList ..) _ (fun i _=> Finset.mem_univ i)]; unfold joint; dsimp only; refine Finset.prod_congr rfl (fun i _=>?_); rw [if_pos (by simp),values,sample];rfl
lemma performance {f g:W!}{x:X!}(h:pie f g (pegs p k L!) x): (perform p k f).val x=(perform p k g).val x:=by
    have hx: pie f g (pegs p k L!+0) x:= h; simpa only [iteratedFDeriv_zero_apply] using (congr_arg (fun A: Tensor.T X! ℂ 0=> A (fun _=>x)) (machine_flat p k L! hx))
end YM.RG05Readout.Pulse
