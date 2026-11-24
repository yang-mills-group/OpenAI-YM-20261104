import YangMills.WilsonProof.NativeSupport.YM.XSpace.Influence

/-!
# From point tests of the infinitesimal group to nearby changed frames
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Normalize
open Function Set Filter Maxwell Maxwell.Free Maxwell.Wick NormedSpace
open scoped BigOperators Topology Classical ContDiff
variable {G : Gauge} {d n : ℕ}
abbrev FieldEnd (G:Gauge) (d:ℕ):= Module.End ℂ (Sec G d)
abbrev RSpace (G:Gauge) (d:ℕ):= Fin (Module.finrank ℝ (Sec G d))→ ℝ

def tableD (G:Gauge) (d:ℕ): Sec G d≃ₗ[ℝ] RSpace G d:= (Module.finBasis ℝ _).equivFun

def err (T:Module.End ℝ (Sec G d)): RSpace G d→L[ℝ] RSpace G d:= LinearMap.toContinuousLinearMap
  ((tableD G d).toLinearMap ∘ₗ T ∘ₗ (tableD G d).symm.toLinearMap)
lemma err_apply (T:Module.End ℝ (Sec G d)) (p:Sec G d): err T (tableD G d p)= tableD _ _ (T p):= by unfold err; simp

variable (T:FieldEnd G d)
def going (t:ℝ):= exp (t • err (T.restrictScalars ℝ))
def forward (t:ℝ) (p:Sec G d):Sec G d:= (tableD G d).symm (going T t (tableD G d p))
lemma forward_eq (p:Sec G d) (t:ℝ): tableD _ _ (forward T t p)=going T t (tableD _ _ p):= LinearEquiv.apply_symm_apply ..
@[simp] lemma going0: going T 0=1:=by simp [going]; --
@[simp] lemma forward0 (p):forward T 0 p=p:= by simp [forward]
lemma forwards (v:Sec G d) (t:ℝ): HasDerivAt (fun t=> tableD _ _ (forward T t v)) (tableD G d (T (forward T t v))) t:= by
  simp_rw [forward_eq];
  let V:= err (T.restrictScalars ℝ); have he:V (tableD G d (forward T t v))=_ := err_apply (T.restrictScalars ℝ) (forward T t v)
  have ht (p):V (tableD G d p)=tableD G d (T p):= err_apply (T.restrictScalars ℝ) p
  rw [← ht,forward_eq T]; exact (ContinuousLinearMap.apply ℝ (RSpace G d) (tableD G d v)).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_exp_smul_const' V _)
lemma frozen (v:Sec G d) (hp:T v=0) (t:ℝ): forward T t v=v:=by
  let f:= fun t=> going T t (tableD G d v); let L:= err (T.restrictScalars ℝ)
  have hs:= show L (tableD G d v)=0 from (err_apply (T.restrictScalars ℝ) v).trans (by change tableD G d (T v)=0; rw [hp,map_zero])
  have he (t:ℝ): HasDerivAt f 0 t:=by
    have h: HasDerivAt f (going T t (L (tableD G d v))) t:= (ContinuousLinearMap.apply ℝ (RSpace G d) (tableD G d v)).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_exp_smul_const L _)
    rwa [hs,map_zero] at h
  have hh:=is_const_of_deriv_eq_zero (fun s=>(he s).differentiableAt) (fun s=>(he s).deriv) t 0
  apply (tableD G d).injective; unfold f at hh; rw [forward_eq T,hh,going0]; rfl

variable {T}
lemma real_forward (T:Change G d) (t:ℝ) (p:Sec G d): reel d (forward T.val t p)= forward T.val t (reel d p) :=by
  let U:=reelR (G:=G) d; let V:= T.val.restrictScalars ℝ; have h:Commute (err U) (t • err V):=by
    apply ContinuousLinearMap.ext; intro x; obtain ⟨p,rfl⟩:= (tableD G d).surjective x
    change err U (t • err V (tableD _ _ p))= t • err V (err U (tableD _ _ p)); simp_rw [map_smul,err_apply]; exact congr_arg (fun p:Sec G d=> t • tableD G d p) (T.property.2.2.1 p).symm
  have he : ∀ x, err U (going T.val t x)= going T.val t (err U x):=fun x=>congr_arg (fun f:RSpace G d→L[ℝ] RSpace G d=> f x) h.exp_right.eq
  apply (tableD G d).injective; change tableD G d (U (forward T.val t p))=_; rw [← err_apply,forward_eq, he,err_apply,forward_eq]; rfl

def paintR (T:FieldEnd G d) (t:ℝ) (p:WickPol G): WickPol G:= (forward T t (project d p)).val
lemma painted (p:Sec G d) (t:ℝ): paintR T t p.val=(forward T t p).val:=by unfold paintR; rw [seated]
lemma realizes_real (T:Change G d) (t:ℝ): Sample.RealMove (paintR T.val t) d:=by
  intro p h hp; let P:Sec G d:=⟨p,h⟩; have ht : reel d P=P:=Subtype.ext hp
  rw [show paintR T.val t p=(forward T.val t P).val from painted P t,← real_proj, real_forward,ht]

section analytic
variable {M F: Type*} [NormedAddCommGroup M] [NormedSpace ℝ M] [FiniteDimensional ℝ M] [NormedAddCommGroup F] [NormedSpace ℝ F]
lemma cont_land (P : MultilinearMap ℝ (fun _ : Fin n => M) F) : Continuous P := by
  let b:=Module.finBasis ℝ M; let e:= LinearEquiv.toContinuousLinearEquiv b.equivFun
  have hw (w : Fin n→M) : P w= ∑ v: Fin n→Fin (Module.finrank ℝ M), (∏ i,e (w i) (v i)) • P (fun i=>b (v i)):=by
    rw [Multilabel.expansion (fun _=>b) P w]; change (∑ z∈Fintype.piFinset _,_) = ∑ z:Fin n → Fin (Module.finrank ℝ M),(∏ i,b.repr (w i) (z i)) • P (fun i=>b (z i))
    apply Finset.sum_subset (Finset.subset_univ _); intro a _ ha; obtain ⟨i,hi⟩: ∃ i,b.repr (w i) (a i)=0:=by simpa using ha
    rw [Finset.prod_eq_zero (Finset.mem_univ i) hi,zero_smul]
  rw [funext hw]; refine continuous_finsetSum _ fun v _=> (continuous_finsetProd _ fun i _=>?_) |>.smul (continuous_const (y:=P (fun i=> b (v i))))
  exact (continuous_apply (v i)).comp (e.continuous.comp (continuous_apply i))
end analytic
lemma points_moves (T:Change G d) (H:silence G d (spill T.val)) (g:G.Simple) (hd:4≤d) (t:ℝ): Sample.Moves (paintR T.val t) d where
  fits p _:= (forward T.val t (project d p)).property
  quad p:= by
    let u : Sec G d:= ⟨team G p p, team_label p p hd⟩; change paintR _ _ u.val=u.val; rw [painted,frozen]
    apply Subtype.ext; rw [← swept]; exact kills_four g (Change_oriented T) H hd (Change_unit T) (Change_in T hd) u.val (team_label _ _ le_rfl)
  arrays n x p hx hp:= by
    let v (t:ℝ) i := forward T.val t (⟨p i,hp i⟩)
    let f (t:ℝ) (i : Fin n):= tableD G d (v t i); let A:= ((scene (G:=G) x d).restrictScalars ℝ).compLinearMap fun i:Fin n=> (tableD G d).symm.toLinearMap; let L:ContinuousMultilinearMap ℝ (fun _ : Fin n=> RSpace G d) ℂ:=⟨A,cont_land A⟩
    let D (t:ℝ) := scene x d (v t)
    have he' (t:ℝ) (i : Fin n): HasDerivAt (fun s=> f s i) (tableD G d (T.val (v t i))) t:= forwards _ _ _
    have hL (p): L (fun i=>tableD G d (p i))=scene x d p:=by change scene x d (fun i => (tableD G d).symm (tableD G d (p i)))=_; simp
    have he : D=L ∘ f:=funext fun i=>(hL (v i)).symm
    have hz (t:ℝ): HasDerivAt D 0 t := by
      let F (i : Fin n):= tableD G d (T.val (v t i))
      have hf : HasDerivAt f F t:= hasDerivAt_pi.mpr (he' t)
      rw [he]; apply ((L.hasFDerivAt (f t)).comp_hasDerivAt t hf).congr_deriv; rw [ContinuousMultilinearMap.linearDeriv_apply];
      have ha (i:Fin n): update (f t) i (F i)=fun j=> tableD G d (update (v t) i (T.val (v t i)) j):=by funext j; by_cases h:j=i <;> simp [h,f,F]
      simp_rw [ha,hL]; exact genre T |>.mp H n x hx _
    have hs:= is_const_of_deriv_eq_zero (fun s=>(hz s).differentiableAt) (fun s=>(hz s).deriv) t 0
    apply Eq.trans _ (hs.trans ?_)
    · unfold D; rw [screen]; apply congr_arg; funext i; exact painted (⟨p i,hp i⟩:Sec G d) _
    unfold D v; simp [forward0,screen]
end YM.XSpace.Normalize
