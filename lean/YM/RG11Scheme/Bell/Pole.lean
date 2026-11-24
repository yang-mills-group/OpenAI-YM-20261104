import YM.RG11Scheme.Bell.Steps
import YM.RG11Scheme.Hinge.Attach

/-! Polynomials over native coordinates, top homogeneous part. Encoded by finite-difference jets rather than R^4 coordinates and coercions. Include pure-gradient part since signals see only transverse on-shell curl. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG11Scheme.Bell
open Filter Function Set Lattice Mesh Maxwell Analysis Next.Rank.Radian Tensor Pert Full Hinge
open Stencil Stencil.Point Stencil.Shot
open scoped BigOperators Classical ContDiff Topology
variable {E:Type} [NormedAddCommGroup E][NormedSpace ℝ E][CompleteSpace E]{j p q:ℕ}
local notation "S" => Tensor.T E4 E

omit [CompleteSpace E] in
lemma flat_shade (Q:S (j+1))(hq:Sym Q) (i:Axis) : grad i (diagonal Q) = diagonal ((↑(j+1:ℕ):ℝ) • Q.curryLeft (basis i)) := by
   funext x
   unfold grad Analysis.D; rw [differential_diagonal Q hq]; unfold Tensor.diagonal; rw [smul_apply]; exact (Nat.cast_smul_eq_nsmul ℝ _ _).symm -- simp deprecated
omit [CompleteSpace E] in
lemma measured (Q:S j)(hq:Sym Q)(γ : Fin j → Axis) (x:E4): dV (List.ofFn γ).reverse (diagonal Q) x=(j.factorial:ℝ) • Q (basis ∘ γ) := by
   induction j with
   | zero => simp only [List.ofFn_zero,List.reverse_nil,dV,List.foldr_nil,Nat.factorial_zero,Nat.cast_one,one_smul]; exact congrArg Q (Subsingleton.elim ..)
   | succ j IH=>
      let R:S j:=Q.curryLeft (basis (γ 0))
      have hR:Sym R:=freeze_sym _ hq _
      let k:ℝ:=↑(j+1:ℕ)
      have hr : Sym (k • R):=fun r s=>congrArg (fun x=> k • (x:E)) (hR r s)
      rw [List.ofFn_succ,List.reverse_cons,dV_append (_ ) (γ 0),flat_shade Q hq]
      change dV _ (diagonal (k • R)) _=_
      rw [IH _ hr]; unfold R k
      simp only [ContinuousMultilinearMap.curryLeft_apply,smul_apply]
      rw [show Fin.cons (basis (γ 0)) (basis ∘ (fun i=>γ i.succ))=basis ∘ γ from funext fun i=> by refine Fin.cases ?_ (fun j=>?_) i<;>rfl,Nat.factorial_succ,Nat.cast_mul,mul_comm _ (↑j.factorial:ℝ),smul_smul]

def traces (U:S j) (x:Cover) := diagonal U (row x)
private def chain := Align.itinerary 2 (by simp)
private lemma at_atom (A:S j) (D:List Axis)(x:Cover) : Tendsto (fun i:ℕ=> (((chain.gap i)^D.length)⁻¹ * (chain.gap i)^j) • go D (traces A) x) atTop (𝓝 (dV D (Tensor.diagonal A) 0)) := by
   have he := sample chain (Tensor.diag_smooth A ∞) (k:=D.length) |>.runs id tendsto_id 0 (mem_univ _) (fun i=>x) (Align.inc_const chain x) D le_rfl
   apply he.congr
   intro i
   simp_rw [_root_.id_eq, inc_row, Tensor.homogeneous]
   erw [← smul_smul]; refine congrArg _ ?_
   exact go_map (Y:=E) ((((chain.gap i)^j) • LinearMap.id : E→ₗ[ℝ]E).toAddMonoidHom) _ D x
lemma traces_grade (A:S j) : traces A∈hill E j := by
   intro D hD; funext x
   have he:=at_atom A D x; have hh:= (chain.cutoff.pow (D.length-j)).smul he
   have ht (i:ℕ) : (chain.gap i)^(D.length-j) * ((chain.gap i ^ D.length)⁻¹ * (chain.gap i)^j)=1 := by
      have hp : chain.gap i≠0 := (chain.positive i).ne'
      rw [pow_sub₀ (chain.gap i) hp hD.le]; field_simp
   simp_rw [smul_smul,ht,one_smul,zero_pow (by omega : D.length-j≠0),zero_smul] at hh
   exact tendsto_nhds_unique tendsto_const_nhds hh
lemma leading (A:S j)(γ : Fin j→Axis)(x:Cover) : go (List.ofFn γ).reverse (traces A) x= dV (List.ofFn γ).reverse (Tensor.diagonal A) 0 := by
   have he := at_atom A (List.ofFn γ).reverse x; simp_rw [List.length_reverse,List.length_ofFn, inv_mul_cancel₀ (pow_ne_zero j (chain.positive _).ne'), one_smul] at he
   exact tendsto_nhds_unique tendsto_const_nhds he
lemma deliver (A:S j)(hA:Sym A)(γ:Fin j→Axis)(x:Cover) : go (List.ofFn γ).reverse (traces A) x=(j.factorial:ℝ) • A (basis ∘ γ) := (leading ..).trans (measured A hA ..)

variable (p) (X:Cover→E)
def axes_tab (γ:Fin p→Axis):E := ((p.factorial:ℝ))⁻¹ • go (List.ofFn γ).reverse X 0
def roll : S p:= ∑ γ:Fin p→ Axis,Pert.Bare.spaceMon γ (axes_tab p X γ)
omit [CompleteSpace E] in
lemma centered (γ:Fin p→Axis): roll p X (basis ∘ γ)=axes_tab p X γ := by
   rw [roll,sum_apply,Finset.sum_eq_single_of_mem γ (Finset.mem_univ _)]
   · rw [Pert.Bare.mon_eq]; simp
   intro v _ h
   obtain ⟨t,e⟩:= Function.ne_iff.mp h
   rw [Pert.Bare.mon_eq]; simp only [Function.comp_apply]; rw [Finset.prod_eq_zero (Finset.mem_univ t) (f:=fun i : Fin p=> basis (γ i) (v i)) (show _=0 by simp [e]),zero_smul]

def cranium := symmetrize (roll p X)
omit [CompleteSpace E] in
lemma tipped (γ:Fin p→Axis): cranium p X (basis ∘ γ)=axes_tab p X γ := by
   let r := List.ofFn γ
   have hc (s:Equiv.Perm (Fin p)): axes_tab p X γ=axes_tab p X (γ ∘ s) := by
       have h:= s.ofFn_comp_perm γ; unfold axes_tab; rw [shuffle _ _ _ (show r.reverse.Perm (List.ofFn (γ ∘ s)).reverse from (List.reverse_perm _).trans (h.symm.trans (List.reverse_perm _).symm))] -- name
   unfold cranium symmetrize
   simp_rw [smul_apply,sum_apply, ContinuousMultilinearMap.domDomCongr_apply]
   rw [Finset.sum_congr rfl (s₂:=Finset.univ) (f:=fun s:Equiv.Perm (Fin p)=> roll p X (fun i=> (basis ∘ γ) (s i))) (g:=fun _ : Equiv.Perm (Fin p) => axes_tab p X γ) (fun s _=> (centered p X (γ ∘ s)).trans (hc s).symm), Finset.sum_const, Finset.card_univ]
   rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ (by positivity),one_smul]
lemma skates (D:List Axis)(hd:D.length=p): go D X 0 = go D (traces (cranium p X)) 0 := by
   let γ:= fun i:Fin p=>D.reverse.get ⟨i,by rw [List.length_reverse,hd]; exact i.isLt⟩
   have he : List.ofFn γ = D.reverse := by apply List.ext_getElem <;> simp [←hd,γ]
   rw [show D=(List.ofFn γ).reverse from by simp only [he, List.reverse_reverse], deliver (cranium p X) (Tensor.symmetrize_sym _), tipped, axes_tab,smul_smul,mul_inv_cancel₀ (by positivity),one_smul]
lemma lowerings {X:Cover→E} (h:X∈hill E (p+1)): X-traces (cranium (p+1) X) ∈ hill E p := by
   apply (lower_iff ((hill E _).sub_mem h (traces_grade _))).2; intro D hd
   change ladder D (X-traces _) 0=_
   rw [map_sub]; exact sub_eq_zero.mpr (skates _ _ _ hd)
end YM.RG11Scheme.Bell
