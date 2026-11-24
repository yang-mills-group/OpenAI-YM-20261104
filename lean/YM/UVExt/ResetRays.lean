import YM.UVExt.ThermoMove

/-! Literal one-loop equation from mixed side Slab and its TWO thermal parts, on real rays. Does not send the volume here. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExt.Paths
open Function Set Filter Matrix Laurent Lattice Tree Wilson RG Bid Precision Exterior Work.F03 Tensor
open scoped Classical BigOperators ContDiff Topology
variable {G : Gauge} {A : Levels G} {m : ℕ} {w p k : ℝ} {c : Clip} {M : ℕ→PathData G} {H : ℕ→Bed}
lemma stored_fiscal {n : Side} {u v} {M : PathData G} (B : Bed) (hc : Attached B M) (hQ : Floor B c n u v) (hb : Sworn B n G) {σ C Λ} (hK : M.Bounds c σ C Λ) (x : fieldDir G n 1) :
  Tensor.diagonal (iteratedFDeriv ℝ 2 (centered n M c) 0) x = gaugeFiscal B x x := by
   have hx := fun x (s:Signed)=>quadratic_limit hK hc hQ (pulled x s)
   have he (x) : Tendsto (fun t : ℝ=>centered n M c (t • x) /t^2) (𝓝[≠] 0) (𝓝 (gaugeFiscal B x x / 2)) := by
      have hh := hx x; simp_rw [show ∀ s,gaugeFiscal B (pulled x s) (pulled x s)=_ from fun s=>hb s x x] at hh
      have hp : (Fintype.card Signed:ℝ) ≠ 0 := by exact_mod_cast Fintype.card_pos.ne'
      simpa only [centered,secondTerm,Patch.average, represent_pulled, mul_div_assoc, Finset.sum_div, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,inv_mul_cancel_left₀ hp] using
           (tendsto_finsetSum _ (fun e (_ : e∈Finset.univ)=>hh e)).const_mul (Fintype.card Signed:ℝ)⁻¹
   have hH (x y : Dir G n) : gaugeFiscal B x y=gaugeFiscal B y x := by
      rw [metric_pair _ hK hc x y hQ,metric_pair _ hK hc y x hQ]
      exact Finset.sum_congr rfl fun i _=> by rw [real_inner_comm (faceCurl ..),real_inner_comm (ellLine M _ _)] -- try
   obtain ⟨_,_,hφ⟩ := Work.F03.hessian_of_limit ((centered_analytic (n:=n) M hK).of_le le_top) he gaugeFiscal_add hH -- edit
   · exact (congr_arg (iteratedFDeriv ℝ 2 (centered n M c) 0) (constant_two x)).trans (hφ x x)

lemma center_equal {σ C Λ W} (h : Harbor A m k p H M c) (P : Passing M W σ C Λ c) (j : ℕ) :
    P.economicTensor (A.S.side m j) 2=P.planeTensor (A.S.side m j) 2 := by
   let n := A.S.side m j
   have ht {P Q : ℕ→ Dir G n →ℝ} {S T : Tensor.T (Dir G n) ℝ 2} (hp : Tendsto (spray P 2) atTop (𝓝 S)) (hQ : Tendsto (spray Q 2) atTop (𝓝 T)) (hL : lucid P) (hR : lucid Q) (he : ∀ᶠ i in atTop, Tensor.diagonal (spray P 2 i)=Tensor.diagonal (spray Q 2 i)) : S=T := by
      exact tendsto_nhds_unique hp (hQ.congr' ((he.and (hL.and hR)).mono fun i hi=> Tensor.ext_diag _ _ (Analysis.sym_Jet (hi.2.2.of_le (finite_cap _))) (Analysis.sym_Jet (hi.2.1.of_le (finite_cap _))) hi.1.symm))
   refine ht (P.centeredLimit n 2 |>.1) (P.mainLimit n 2 |>.1) (P.second_groomed n) (P.groomed n) ?_
   filter_upwards [h.ties,h.full n,P.mask,h.symmetry j,fiscal_given h P (z:=j)] with i hi hf hb hz hA
   obtain ⟨u,v,hQ⟩ := hf
   exact funext fun x=> (stored_fiscal (H i) hi hQ hz hb x).trans <| Eq.symm <| (congr_arg (iteratedFDeriv ℝ 2 (knotted n c (M i)) 0) (constant_two _)).trans (hA.2.2 x x) -- dotted terms reduce

namespace Slab
variable {f c:Side} {S:StepData c f} {F : Forest S.ratio} {O : ChartRatio G}
variable {U R : ℕ→PathData G} {p r : Clip} {t : S.Choices} {ρ : ℕ→fieldDir G c 1 → AxisChart G F}
    {Y : ℕ→Matrix (Body 1 f) (Body 1 c) ℝ} {η : ℝ}
    {U' R' η' ρ' Y'} (L : Slab F U R p r t ρ η Y) (V : Slab F U' R' p r t ρ' η' Y')
variable {hσ hC hΛ hμ hZ hA uσ uC uΛ uμ uZ uA : ℝ} {K V' K' T : Shadow G} (hU : Passing U K hσ hC hΛ p) (hP : Passing R K' hμ hZ hA r) (hB : Passing U' V' uσ uC uΛ p) (hD : Passing R' T uμ uZ uA r)

def thermalRay (_:Slab F U R p r t ρ η Y) (O : ChartRatio G) (w : Dir G c) (i : ℕ) (z:ℝ) := thermal F t p (U i) (ρ i) O (z • w)
def draftRay (_:Slab F U R p r t ρ η Y) (b : ℕ→ℝ) (w:Dir G c) i (z:ℝ) := draft (b i) (R i) r (z • w)
def finalCover (M : ℕ→PathData G) (p : Clip) (b : ℕ→ℝ) (w : Dir G c) i := iteratedFDeriv ℝ 2 (draft (b i) (M i) p) 0 ![w,w]

def thermalTotal (e p q : ℝ→ℝ) := e + (1/2:ℝ) • p - q
private lemma total_rate (e p q : ℝ→ℝ) (H : ContDiffAt ℝ ∞ e 0) (P : ContDiffAt ℝ ∞ p 0) (Q : ContDiffAt ℝ ∞ q 0) : tag 2 (thermalTotal e p q)=tag 2 e+(1/2:ℝ)*tag 2 p-tag 2 q := by
  unfold tag thermalTotal; have ht := ContDiffAt.const_smul (1/2:ℝ) P
  have hh := iteratedDeriv_sub ((H.add ht).of_le (finite_cap 2)) (Q.of_le (finite_cap 2))
  exact hh.trans (sub_left_inj.mpr (Eq.trans (iteratedDeriv_add (H.of_le (finite_cap 2)) (ht.of_le (finite_cap _))) (congr_arg (_+·) (iteratedDeriv_const_smul (P.of_le (finite_cap _)) (1/2:ℝ))))) -- const_smul p target

include L V hU hB
lemma thermal_ray_limit {Y0 : Matrix (Body 1 f) (Body 1 c) ℝ} (HO : LocalRatio O) (ht' : Junction L.inFine V.inFine 4) (he : 0 < η) (h : 0 < η') (w : Dir G c) (hY : Tendsto Y atTop (𝓝 Y0)) :
   Tendsto (fun i=>tag 2 (thermalRay L O w i)-tag 2 (thermalRay V O w i)) atTop (𝓝 (discrep (hU.spiralTensor f 2) (hB.spiralTensor f 2) (polish Y0 w))) := by
     have ht := L.track ht' (hU.groomed _) (hB.groomed _)
     obtain ⟨ha,hb,k⟩:= determinant_branch L V _ ht he h
     obtain ⟨hu,hv,q⟩:= chart_terms L V _ (ht.mono (by decide)) he h HO
     obtain ⟨u,hK,hK'⟩:=k 2 le_rfl; obtain ⟨v,hV,hV'⟩:=q 2 le_rfl
     let x i (t : ℝ) := L.perLoop i (t • w); let x' i (t:ℝ) := V.perLoop i (t • w)
     let y i := L.determinantLine i w; let y' i := V.determinantLine i w; let d i := contribution O w (ρ i); let d' i := contribution O w (ρ' i)
     have hp (n : ℕ) : thermalRay L O w n=thermalTotal (x n) (y n) (d n) := by funext z; rfl
     have hp' (n : ℕ) :thermalRay V O w n=thermalTotal (x' n) (y' n) (d' n) := by funext z; rfl
     have hX := (inLoop_rate L hU w).1; have hX' := (inLoop_rate V hB w).1
     let hφ := (inLoop_transfer L V hU hB he h w hY (ht'.mono (by omega)))
     let e := discrep (hU.spiralTensor f 2) (hB.spiralTensor f 2) (polish Y0 w);
     have hH := ((hφ.add ((hK.sub hK').const_mul (1/2:ℝ))).sub (hV.sub hV'))
     rw [show u-u=0 from sub_self _,show v-v=0 from sub_self _,mul_zero,add_zero,sub_zero] at hH
     refine hH.congr' ?_; change (fun n=> tag 2 (x n) - tag 2 (x' n) + (1/2:ℝ)*(tag 2 (y n)-tag 2 (y' n)) - (tag 2 (d n)-tag 2 (d' n))) =ᶠ[atTop] _ -- equality on differences
     filter_upwards [hX,hX',ha,hb,hu,hv] with n hx hy hj hk hpw hpk
     change _ = tag 2 (thermalRay L O w n)-tag 2 (thermalRay V O w n)
     rw [hp n,hp' n,total_rate (x n) (y n) (d n) hx hj hpw, total_rate (x' n) (y' n) (d' n) hy hk hpk]; ring


include hP hD
omit V hU hB hD in
lemma surface_jet (b : ℕ→ℝ) (w : Dir G c) : ∀ᶠ i in atTop, tag 2 (draftRay L b w i) = b i*tag 2 (fun t : ℝ=>secondTerm r (R i) (represent (t•w))) + tag 2 (fun t : ℝ=> Precision.loop (R i) (represent (t • w))) := by
   have ht := ((lucid_pin w (hP.second_groomed c)).and (lucid_pin w (hP.loop_groomed c)))
   filter_upwards [ht] with i hx
   let p := fun t : ℝ=>secondTerm r (R i) (represent (t • w)); let u := fun t : ℝ=>Precision.loop (R i) (represent (t•w))
   change iteratedDeriv 2 ((b i) • p + u) 0= _
   change ContDiffAt ℝ ∞ p 0 ∧ ContDiffAt ℝ ∞ u 0 at hx
   have hp : iteratedDeriv 2 ((b i) • p + u) 0 = iteratedDeriv 2 ((b i) • p) 0 + iteratedDeriv 2 u 0 := iteratedDeriv_add ((ContDiffAt.const_smul (b i) hx.1).of_le (finite_cap _)) (hx.2.of_le (finite_cap _))
   rw [hp]; exact congr_arg (·+_) (iteratedDeriv_const_smul (hx.1.of_le (finite_cap _)) (b i) : iteratedDeriv 2 ((b i) • p) 0=_)
omit V hU hD hB in
lemma surface_eq (b : ℕ→ℝ) (w : Dir G c) : ∀ᶠ i in atTop,tag 2 (draftRay L b w i)=Tensor.diagonal (iteratedFDeriv ℝ 2 (draft (b i) (R i) r) 0) w := ((hP.second_groomed c).and (hP.loop_groomed c)).mono fun u hu => (ray_tag (draft (b u) (R u) r) (((ContDiffAt.const_smul (b u) hu.1).add hu.2).of_le (finite_cap _)) w)

lemma reset_limit (b b' : ℕ→ℝ) {x y : ℝ} (w : Dir G c) (hX : Tendsto b atTop (𝓝 x)) (hY : Tendsto b' atTop (𝓝 y)) :
    Tendsto (fun i => finalCover R r b w i - finalCover R' r b' w i) atTop (𝓝 (x*Tensor.diagonal (hP.economicTensor c 2) w - y*Tensor.diagonal (hD.economicTensor c 2) w + discrep (hP.spiralTensor c 2) (hD.spiralTensor c 2) w)) := by
     let v := fun t : ℝ=>t • w
     have hG {f : ℕ→Dir G c→ℝ} {u : Tensor.T (Dir G c) ℝ 2} (hu : Tendsto (spray f 2) atTop (𝓝 u)) (he : lucid f) : Tendsto (fun i=>tag 2 (f i ∘ v)) atTop (𝓝 (Tensor.diagonal u w)) := ((view_cont.continuousAt.tendsto.comp (hu.prodMk_nhds (tendsto_const_nhds (x:=fun (_:Fin 2)=>w)))).congr' (he.mono fun i hi=> Eq.symm (ray_tag (f i) (hi.of_le (finite_cap 2)) w)))
     let A := hG (hP.centeredLimit c 2|>.1) (hP.second_groomed c); let B := hG (hP.loopLimit c 2|>.1) (hP.loop_groomed c)
     let A' := hG (hD.centeredLimit c 2|>.1) (hD.second_groomed c); let B' := hG (hD.loopLimit c 2|>.1) (hD.loop_groomed c)
     apply Tendsto.congr' ?_ (((hX.mul A).sub (hY.mul A')).add (B.sub B'))
     filter_upwards [surface_eq L hP b w, surface_eq V hD b' w, surface_jet L hP b w,surface_jet V hD b' w]
     intro n a' b'' k z
     try dsimp only [Function.comp_apply]
     change _ = finalCover _ _ _ _ n - finalCover _ _ _ _ n
     rw [show finalCover R r b w n=tag 2 (draftRay L b w n) from (congr_arg (iteratedFDeriv ℝ 2 _ 0) (constant_two w).symm).trans a'.symm,
         show finalCover R' r b' w n=tag 2 (draftRay V b' w n) from (congr_arg _ (constant_two w).symm).trans b''.symm, k,z]
     change (b n*tag 2 (fun t=>secondTerm r (R n) (represent (v t))) - b' n * tag 2 (fun t=>secondTerm r (R' n) (represent (v t))))+ (tag 2 (fun t=> Precision.loop (R n) (represent (v t))) - tag 2 (fun t=> Precision.loop (R' n) (represent (v t)))) = _
     unfold v; ring

end Slab
end YM.UVExt.Paths
