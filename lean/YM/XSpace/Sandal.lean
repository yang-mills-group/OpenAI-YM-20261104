import YM.XSpace.Trials

/-!
# Interpolation with umbral letter jets

Proof works for any offset used for the letter. No derivative API hidden on
the approximate side. Stamps match exactly all forward differences at root.
Reconciliation with scaling of stamps and rounding/convergence separately.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Litter
open Lattice Maxwell Maxwell.Free Tensor Sail Further.FreeCovariance.KP Set Filter Function
open scoped Topology ContDiff BigOperators
variable {F:Type*}[NormedAddCommGroup F][NormedSpace ℝ F]{d n:ℕ}

private lemma sticker_sym {A:(Fin n→Axis)→F}(h:∀ x (s:Equiv.Perm (Fin n)), A (x ∘ s)=A x): Sym (sticker A):=by
  intro x s; exact congr_arg (fun f:piece n F=> f x) (show (sticker A).domDomCongr s=sticker A by apply piece_ext; intro t; change sticker A (basis ∘ (t ∘ s))=_; rw [sticker_on, h, sticker_on])
def talent (n:ℕ)(A:Cover→F): Stamp n F:=
  ⟨sticker (fun s=> ((n.factorial:ℝ)⁻¹) • peak (List.ofFn s) A 0), sticker_sym (by intro t s; simp_rw [peaked,cracks_perm (s.ofFn_comp_perm t)])⟩
lemma talent_ap (n:ℕ)(A:Cover→F)(t: Fin n→Axis): ((talent n A).val : piece n F) (basis ∘ t)= (n.factorial:ℝ)⁻¹ • peak (List.ofFn t) A 0 := sticker_on ..
def grasp (n:ℕ): (Cover→F) →ₗ[ℝ] Stamp n F where
  toFun:=talent n
  map_add' a b:= Subtype.ext (piece_ext fun t=>by rw [talent_ap,map_add]; simp only [Pi.add_apply,smul_add]; rw [← talent_ap,← talent_ap];rfl )
  map_smul' a b := Subtype.ext (piece_ext fun t=>by rw [talent_ap,map_smul]; simp only [Pi.smul_apply]; rw [smul_comm _ a, ← talent_ap];rfl )
lemma grasp_ap (n:ℕ)(u: Cover→F):grasp n u=talent n u:=rfl
lemma poured (v:E4)(A:Stamp n F): grasp n (feed v A)= A:=Subtype.ext (piece_ext fun t=>by rw [grasp_ap,talent_ap,peaked]; change ((n.factorial:ℝ)⁻¹) • felt v A (List.ofFn t) 0=_; rw [sent, inv_smul_smul₀ (by positivity : (n.factorial:ℝ)≠0)])
lemma flunked (v:E4)(A:Stamp d F)(h:d<n):grasp n (feed v A)=0:=Subtype.ext (piece_ext fun t=>by rw [grasp_ap,talent_ap,peaked]; change _ • felt v A (List.ofFn t) 0 = (0:F); simp [late v A (by simpa using h : d<(List.ofFn t).length)])

abbrev Series (d:ℕ)(F:Type*)[NormedAddCommGroup F][NormedSpace ℝ F]:= (i:Fin (d+1))→ Stamp i.val F
def act (v:E4): Series d F →ₗ[ℝ] (Cover→F):=∑ i:Fin (d+1),feed v ∘ₗ LinearMap.proj i
def stage (d:ℕ): (Cover→F)→ₗ[ℝ] Series d F:=LinearMap.pi fun i:Fin (d+1)=> grasp i.val
lemma collected (v:E4)(A:Series d F)(i:Fin (d+1)): stage d (act v A) i=A i+∑ j∈ Finset.Ioi i,(grasp i.val (feed v (A j))):=by
  change grasp _ _ = _; simp only [act,LinearMap.sum_apply,LinearMap.comp_apply,LinearMap.proj_apply,map_sum]; rw [Finset.sum_eq_add_sum_sdiff_singleton i]; swap; · simp
  rw [poured]; congr 1; symm; apply Finset.sum_subset _ _
  · intro j hj; simp only [Finset.mem_Ioi] at hj; simp [ne_of_gt hj]
  intro j hj hh; rw [Finset.mem_Ioi,not_lt] at hh; have hE : j < i:= lt_of_le_of_ne hh (by simpa using hj)
  exact flunked v (A j) (Fin.lt_def.mp hE)
lemma takes (v:E4): Injective (stage d ∘ₗ (act v : Series d F →ₗ[ℝ] _)):=by
  intro x y h; funext i
  induction i using WellFoundedGT.induction with
  | _ i ih =>
    have he:= congr_fun h i; change stage d (act v x) i=stage d (act v y) i at he; rw [collected,collected] at he; rw [Finset.sum_congr rfl (g:=fun j:Fin (d+1)=>grasp i.val (feed v (y j))) (fun j (hj:j∈ Finset.Ioi i)=>by rw [ih j (Finset.mem_Ioi.mp hj)])] at he; exact add_right_cancel he
lemma punch (v:E4):Injective (act v (F:=F) (d:=d)):=Injective.of_comp (f:=stage d) (takes v)

variable [FiniteDimensional ℝ F]
def spell (v:E4)(d:ℕ): Series d F ≃ₗ[ℝ] Series d F:= LinearEquiv.ofBijective (stage d ∘ₗ act v) ⟨takes v,LinearMap.injective_iff_surjective.mp (takes v)⟩
def showTime (v:E4)(d:ℕ): (Cover→F) →ₗ[ℝ] Series d F := (spell v d).symm.toLinearMap ∘ₗ stage d
lemma shows (v:E4)(d:ℕ)(u: Cover→F): stage d (act v (showTime v d u))=stage d u:= (spell v d).apply_symm_apply _
lemma old (v:E4)(d:ℕ)(u:Series d F): showTime v d (act v u)=u:= (spell v d).symm_apply_apply _
lemma extracts (v:E4)(u: Cover→F)(l:List Axis)(h:l.length≤d): crack l (u-act v (showTime v d u)) 0=0:=by
  let i:Fin (d+1):=⟨l.length,by omega⟩; let A:=u-act v (showTime v d u); have ht: stage d A=0:= by rw [show A=u-_ from rfl,map_sub,shows,sub_self]
  have he: talent i.val A=0:= congr_fun ht i; have he:= congr_arg (fun Q:Stamp i.val F=> Q.val (basis∘l.get)) he; change (talent i.val A).val (basis ∘ l.get)=(0:F) at he; rw [talent_ap,peaked,List.ofFn_get] at he
  exact (smul_eq_zero.mp he).resolve_left (by positivity)

-- scaled convergence without assuming analytic correction on the projector

def invest (t:ℝ)(k:ℕ): Module.End ℝ (Series d F):= LinearMap.pi fun i:Fin (d+1)=> (t^(k+i.val)) • LinearMap.proj i
lemma shares (t:ℝ)(k:ℕ)(x:Series d F)(i:Fin (d+1)): invest t k x i=t^(k+i.val) • x i:=rfl
lemma invest_inv (a:ℝ)(h:a≠0)(A:Series d F)(k:ℕ):invest a k (invest a⁻¹ k A)=A:= by funext i; rw [shares,shares,inv_pow,smul_inv_smul₀ (pow_ne_zero _ h)]
private lemma dynamics (v:E4)(A:Series d F)(k:ℕ)(a:ℝ)(h:a≠0)(i:Fin (d+1)): invest a⁻¹ k (stage d (act v A)) i=(invest a⁻¹ k A i)+ ∑ j∈Finset.Ioi i, (a^(j.val-i.val)) • grasp i.val (feed v (invest a⁻¹ k A j)):=by
  rw [shares,collected,smul_add, Finset.smul_sum]; congr 1; refine Finset.sum_congr rfl fun j hj=>?_; rw [shares,map_smul, map_smul, smul_smul]; congr 1
  have he: i.val< j.val := (Finset.mem_Ioi.mp hj : i<j); rw [show k+j.val=(k+i.val)+(j.val-i.val) by omega,pow_add _ (k+i.val),mul_left_comm, ← mul_pow,mul_inv_cancel₀ h,one_pow,mul_one]
variable {ι:Type*}{L:Filter ι}{a:ι→ℝ}
lemma high (v:E4)(k:ℕ)(u: ι→Cover→F)(A:Series d F)(h:Tendsto a L (𝓝 0))(he:∀ᶠ i in L, a i≠0) (ht:Tendsto (fun i=> invest (a i)⁻¹ k (stage d (u i))) L (𝓝 A)):
    Tendsto (fun i=> invest (a i)⁻¹ k (showTime v d (u i))) L (𝓝 A):=by
  let f i:=showTime v d (u i); let X i:= invest (a i)⁻¹ k (f i); change Tendsto X L _; refine tendsto_pi_nhds.mpr ?_; intro j
  induction j using WellFoundedGT.induction with
  | _ j ih=>
    set y:=fun i:ι=> invest (a i)⁻¹ k (stage d (u i)) j; let s:Finset (Fin (d+1)):= Finset.Ioi j; let r (l:Fin (d+1)) (i:ι):= ((a i)^ (l.val-j.val)) • grasp j.val (feed v (X i l)); have hv: Tendsto (fun i=> ∑ l∈s,r l i) L (𝓝 (∑ _l∈s,(0:Stamp j.val F))) :=tendsto_finsetSum s fun l hl=>by
      let g:= (grasp j.val) ∘ₗ (feed v (F:=F) (n:=l.val)); have hw:=Finset.mem_Ioi.mp hl; have hp: (0:ℝ)^(l.val-j.val)=0:=zero_pow (show l.val-j.val ≠ 0 from Nat.sub_ne_zero_of_lt hw); have ht:= (h.pow (l.val-j.val)).smul (g.continuous_of_finiteDimensional.continuousAt.tendsto.comp (ih l hw)); rw [hp,zero_smul] at ht; exact ht
    have hw: Tendsto y L (𝓝 (A j)):=tendsto_pi_nhds.mp ht j; have hv:=hw.sub hv; simp only [Finset.sum_const_zero,sub_zero] at hv; refine hv.congr' ?_
    filter_upwards [he] with i hi; simp only [y]; rw [← shows v d (u i),dynamics v (f i) k (a i) hi]; exact add_sub_cancel_right ..
end YM.XSpace.Litter
