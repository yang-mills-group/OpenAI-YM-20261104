import YM.Contacts.Pulse.Picket
import YM.Next.STATIONARY.Spectral.ComplexGap
namespace YM.Pulse.Spine
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior Matrix Tree
open Finset Bloch Laurent Push.AbsoluteSums Extra.Iteration MergeProof Next.Free Work.F08 Extension.UV.Linear
open scoped Classical Topology BigOperators NNReal ENNReal Matrix
noncomputable section
variable {G:Gauge}{L c f n:Side}{S: StepData c f}{P:Patch}{α β X:Type}
open FreeResolvent Larch
variable {s η:ℝ≥0}{a b C D:ℝ}
namespace Origin
abbrev Stairs (G:Gauge)(L: Side) := Row (Loose G L) (Loose G L)
def brick (G:Gauge)(P:Patch)(k:ℝ)(B:Bed): Stairs G P.L:= fun i j=> fullRow G P k B.metric i.val j.val
local notation "T" => planting S.ratio S.patch.odd_side
lemma descent {A:Row X X}(e:α→X) (c:Side): Row.acts (fun (i j:α)=> A (e i) (e j)) c=(A.acts c).submatrix (Prod.map id e) (Prod.map id e):= rfl
lemma front {B:Bed} (h:Whole B.metric) : treeMatrix G S T B.metric = ((brick G S.patch S.kernel.penalty B).acts c).submatrix (aperture S.ratio S.patch.odd_side G) (aperture S.ratio S.patch.odd_side G):= by
  ext i j; unfold treeMatrix; obtain ⟨s,K,hs,hg⟩:= h; rw [fullRow_periods S hs.le hg]; simp only [submatrix_apply]; rw [← plant_free S.ratio S.patch.odd_side G i,← plant_free S.ratio S.patch.odd_side G j]; rfl
lemma hurt [Fintype α][Fintype β]{A:Matrix α α ℝ}{B:Matrix β β ℝ}{t:ℝ} (e:α≃β) (g:A=B.submatrix e e)(h:Gap A t): Gap B t:= by
  rw [show B=A.submatrix e.symm e.symm from by rw [g]; ext; simp]; exact h.submatrix e.symm e.symm.injective
lemma inside {B:Bed} (h:Whole B.metric){V:Stairs G S.patch.L}(hp:Cabinet (brick G S.patch S.kernel.penalty B) V): treeInverse G S T B.metric 0=(V.acts c).submatrix (aperture S.ratio S.patch.odd_side G) (aperture S.ratio S.patch.odd_side G):= by
  simp only [treeInverse,resolve,zero_smul,add_zero, front h]; apply Eq.trans (Matrix.inv_submatrix_equiv _ (aperture S.ratio S.patch.odd_side G) (aperture S.ratio S.patch.odd_side G)); apply congr_arg (fun q : Matrix (Co c (Loose G S.patch.L)) (Co c (Loose G S.patch.L)) ℝ=> q.submatrix (aperture S.ratio S.patch.odd_side G) (aperture S.ratio S.patch.odd_side G)); apply Matrix.inv_eq_left_inv; convert hp.l c using 1; any_goals congr!
-- pad for covariance not asserting projected inverse in forgotten columns
abbrev Cellar (G:Gauge)(L:Side):= Co L (Dye G)
def crisp (L:Side)(x: Cellar G L) := ¬ seed x.1 (axisEquiv.symm x.2.1)
def prom (V: Stairs G L) : Row (Cellar G L) (Cellar G L):= fun x y k=> if h:crisp L x then if H:crisp L y then V ⟨x,h⟩ ⟨y,H⟩ k else 0 else 0
lemma brace (V:Stairs G L)(h:V.strip s a)(hc:0≤a) : (prom V).strip s a:= by
  intro x y; unfold prom
  by_cases he:crisp L x <;> by_cases hz:crisp L y <;> simp only [he,hz,↓reduceDIte] <;> first | exact h _ _ | exact (by simpa [Width] using budget_loosen (budget_zero (α:=Cover)) hc)
lemma intake (V:Stairs G L)(i j:Co c (Loose G L)): (prom V).acts c (annex c i) (annex c j)= V.acts c i j:= by simp [Row.acts,prom,annex,show crisp L i.2.val from i.2.property,show crisp L j.2.val from j.2.property]
lemma ap_free (F:Stairs G L) (i:Co c (Co L (Dye G))) (j) (h:i∉ Set.range (annex c)) : (prom F).acts c i j=0 ∧ (prom F).acts c j i=0:= by
  have hx : ¬ crisp L i.2:= fun he=> h ⟨(i.1,⟨i.2,he⟩),rfl⟩
  by_cases he:crisp L j.2 <;> simp [Row.acts,prom,hx,he]
section
variable [Fintype α][Fintype β][DecidableEq α][DecidableEq β]{A:Matrix α α ℝ}{B:Matrix β β ℝ}{F:β→α}
lemma towards (h:F.Injective)(hf:B=A.submatrix F F)(hu: ∀ p∉Set.range F,∀ i,A p i=0 ∧ A i p=0): A = insertion F * B * (insertion F)ᵀ:= by
  ext i j; simp only [mul_apply, transpose_apply,insertion,Matrix.of_apply,ite_mul,mul_ite,zero_mul,one_mul,mul_one,mul_zero]; by_cases hp:i∈Set.range F
  · obtain ⟨i,rfl⟩:=hp; simp_rw [h.eq_iff,Finset.sum_ite_eq',Finset.mem_univ,if_true]; by_cases hj:j∈Set.range F
    · obtain ⟨j,rfl⟩:=hj; simp_rw [h.eq_iff,Finset.sum_ite_eq',Finset.mem_univ,if_true,hf]; rfl
    rw [Finset.sum_eq_zero (fun i _ => if_neg (fun h=>hj ⟨_,h⟩)), (hu j hj _).2]
  rw [Finset.sum_eq_zero, (hu i hp _).1]; intro i hi; split <;> first | rfl | exact Finset.sum_eq_zero (fun j _=> if_neg (fun h=> hp ⟨_,h⟩))
end
lemma issue {B:Bed} (h:Whole B.metric){V:Stairs G S.patch.L}(hp:Cabinet (brick G S.patch S.kernel.penalty B) V): covariance G S T B.metric=((prom V).acts c).submatrix (splitCo S.ratio (Dye G)) (splitCo S.ratio (Dye G)) := by
  unfold covariance reduce; symm; let f:= splitCo S.ratio (Dye G); let e:= aperture S.ratio S.patch.odd_side G
  refine towards (plant_inj T) ?_ (fun i hx j=> ?_)
  · ext i j; rw [inside h hp]; change V.acts c (e i) (e j)= (prom V).acts c (f (plant T i)) (f (plant T j)); rw [← intake V]; exact congr_arg₂ ((prom V).acts c) (plant_free ..) (plant_free ..) -- arrow Tri
  apply ap_free _ (f i) _; rintro ⟨k,h⟩; exact hx ⟨e.symm k,f.injective (Eq.trans (plant_free S.ratio S.patch.odd_side G (e.symm k)).symm ((congr_arg _ (e.apply_symm_apply k)).trans h))⟩
variable (K: KernelChoices)
def sprig (P:Patch)(K:KernelChoices)(c:Side): StepData c (c*P.L):=⟨P,K,rfl⟩
lemma ceilCapacity (P:Patch)(G:Gauge)(K:KernelChoices)(h:P.Branches K G)(hs:0<s)(ha:0≤ a)(hD:0<D): ∃ (η:ℝ≥0)(c:ℝ),0<η∧0≤c∧∀ B:Bed, B.metric.strip s a → (∀ n,(B.metric.acts n)ᵀ=B.metric.acts n ∧ Gap (B.metric.acts n) D) → ∃ V, V.strip (η:ℝ) c ∧ Cabinet (brick G P K.penalty B) V:= by
  let A:=Loose G P.L; let k i:Side:= ⟨100*Pressure.macroR P+2+(i:ℕ),by omega⟩; have hm:Tendsto (fun i=>(k i).val) atTop atTop:= tendsto_atTop_mono (f:=id) (fun i=> (Nat.le_add_left ..: i≤ (k i).val)) tendsto_id
  have he i: Bid.Larger (G:=G) (sprig P K (k i)) := by
    refine ⟨h,?_ ,?_⟩
    · change 100*Pressure.macroR P ≤ (k i).val*P.L.val; exact le_trans (b:=(k i).val) (by dsimp [k]; omega) (Nat.le_mul_of_pos_right _ P.L.property)
    dsimp [k]; omega
  obtain ⟨η,C,hη,hC,H⟩:= cabinet A s (outputPrice P K.penalty s a) (treeFare G P K D) hs (outputPrice_nn _ _ _ _ ha) (treeFare_pos _ _ _ hD)
  refine ⟨η,C,hη,hC,fun B hB hP=> ?_⟩; let M:= brick G P K.penalty B; have hh:Whole B.metric:= ⟨_,_,NNReal.coe_pos.mpr hs,hB⟩
  apply H M (fun i j=> fullRow_width P K.penalty s.property ha hB i.val j.val) k hm
  · intro i; let e:= aperture (sprig P K (k i)).ratio P.odd_side G
    ext p q; obtain ⟨p,rfl⟩:=e.surjective p; obtain ⟨q,rfl⟩:= e.surjective q
    have hu := front (S:=sprig P K (k i)) (G:=G) hh; let v:= sprig P K (k i); have hy:(treeMatrix G v (planting v.ratio P.odd_side) B.metric)ᵀ=((brick G P K.penalty B).acts (k i)).submatrix e e:= by apply Eq.trans ?_ hu; unfold treeMatrix; rw [Matrix.transpose_submatrix,full_symmetric B.metric (hP _).1]
    exact congr_fun (congr_fun (transpose_submatrix .. |>.symm.trans ((congr_arg Matrix.transpose hu).symm.trans hy)) p) q
  intro i; let v:= sprig P K (k i); let Tx:=planting v.ratio P.odd_side; refine hurt (aperture v.ratio P.odd_side _) (front hh) (tree_gap v Tx B.metric (he _) hD ((hP _).2))
end Origin
end
end YM.Pulse.Spine
