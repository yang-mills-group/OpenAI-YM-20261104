import YM.RG17.Press

/-!
 # Integrable bills on OUTPUT POLYNOMIAL (not a representative norm)
 means actual exact projection pulls aggregated in `Press` units.
 At every scale retaining selected part of all real numerics.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG17
open Function Set Filter MeasureTheory RG Lattice Wilson Marker Overlay Extraction Spec
open scoped Topology Classical BigOperators Matrix.Norms.Frobenius
variable {G:Gauge} {C:Family G} {b N p:ℕ} {S:Table C.book} {f:Extraction.Order} (F:Final C f S)
set_option quotPrecheck false
local notation "μ" => prior G

def share (C:Family G)(N p t:ℕ) := (C.path.levels.clock.op t p).push (X:=ℂ) (G:=G) (C.path.β N p (t+1)) -- binder inspect
abbrev Book (C:Family G) (p:ℕ):=(j:ℕ)→ Config G (C.side j p)→ℂ

structure Shelved (C:Family G)(N p:ℕ) (g:Book C p) : Prop where
   carry (j:ℕ)(hj:j<N): g j= share C N p j (g (j+1))
   smooth (j:ℕ)(hj:j≤N): Continuous (g j)
variable {g g':Book C p} {i j:ℕ}
namespace Shelved
lemma intake (h : Shelved C N p g) (hj:j≤ N) : Integrable (g j) (μ _):=(h.smooth _ hj).integrable_of_hasCompactSupport (by exact HasCompactSupport.of_compactSpace _)
lemma add (h:Shelved C N p g) (h': Shelved C N p g') : Shelved C N p (g+g') := by
   constructor <;> intro j hj
   · rw [Pi.add_apply,Pi.add_apply,h.carry j hj,h'.carry j hj]; exact (StepData.push_add (C.path.levels.transition_mass ..) _ _ (h.intake hj) (h'.intake hj)).symm
   exact (h.smooth j hj).add (h'.smooth j hj)
lemma penny (h:Shelved C N p g) (c:ℂ) : Shelved C N p (c • g):=by
   constructor <;> intro j hj
   · rw [Pi.smul_apply,Pi.smul_apply,h.carry j hj]; exact (StepData.push_smul _ _ _ _ (h.intake hj)).symm
   exact (h.smooth _ hj).const_smul c
lemma sub (h:Shelved C N p g)(h':Shelved C N p g'): Shelved C N p (g-g'):= by simpa only [sub_eq_add_neg,neg_smul,one_smul] using h.add (h'.penny (-1))
theorem void : Shelved C N p 0 := by
    constructor
    · intro j hj; funext i; change 0= ∫ _,_ ∂prior ..; simp
    exact fun _ _=>continuous_const
lemma total {ι:Type*}{I:Finset ι}(g:ι→Book C p)(h:∀ i∈I,Shelved C N p (g i)): Shelved C N p (∑ i∈I,g i):=by
    induction I using Finset.induction with
    | empty => simpa using void
    | @insert a s he ih => rw [Finset.sum_insert he]; exact (h a (Finset.mem_insert_self ..)).add (ih (fun i hi=> h i (Finset.mem_insert_of_mem hi)))
def price (j:ℕ)(g:Book C p):= ∫ V,‖g j V‖∂ μ _
-- no loss in L1 budgets, after actual normalized-pay in Press units
lemma budget (h : Shelved C N p g)(hi:i ≤ j)(hj:j≤ N) : price i g ≤ price j g:=by
    induction j,hi using Nat.le_induction with
    | base=> exact le_rfl
    | succ k hk ih=>
          apply (ih (by omega)).trans
          let H:=C.path.levels.clock.op k p; let β:= C.path.β N p (k+1); let P:= C.path.levels.transition_mass k p β
          let b:= g (k+1); let v(x:Config G (C.side k p)):= H.push β (fun y=>‖b y‖) x
          have he(x:Config G (C.side k p)) : ‖g k x‖ ≤ v x:=by
              rw [h.carry k (by omega)]; change ‖∫ y, H.density β y x • b y ∂ prior G _‖ ≤ _
              simp_rw [v,StepData.push,smul_eq_mul]
              apply (norm_integral_le_integral_norm ..).trans (le_of_eq ?_); apply integral_congr_ae; filter_upwards with y
              rw [norm_smul_of_nonneg (P.positive ..)]
          unfold price; rw [← StepData.push_integral (X:=ℝ) P _ (h.intake hj).norm]; exact MeasureTheory.integral_mono (h.intake (j:=k) (by omega)).norm (StepData.push_integrable P _ (h.intake hj).norm) he
lemma sealBook (h:Shelved C N p g)(hj:j≤ N) : (∫ V,g j V∂μ _)= ∫ V,g N V∂μ _:=by
    induction hj using Nat.decreasingInduction with
    | self=> rfl
    | of_succ k hk ih=> rw [h.carry k hk]; exact (StepData.push_integral (C.path.levels.transition_mass ..) _ (h.intake hk)).trans ih
end Shelved

variable (h:b≤ N){n:ℕ}(K:Set (Points (n+1)))(T:Test 1)
variable (v:Fin (n+1)→ C.book.Token)

def asset (v:Fin (n+1)→ C.book.Token)(U:Finset (Fin (n+1) → Site (C.side N p)))(ψ:Test (n+1)) : Book C p :=
    ((C.S.a N:ℂ)^(4*(n+1))) • ∑ u∈U, (ψ (Order.cells C N p u)) • (pullDimes v u (Stock.final (Fin (n+1))))
lemma assetsBound (U:Finset (Fin (n+1)→ Site (C.side N p)))(ψ:Test (n+1)) : Shelved C N p (asset v U ψ):= Shelved.penny (Shelved.total _ (fun u _=> (show Shelved C N p (pullDimes v u (Stock.final (Fin (n+1)))) from ⟨fun _ h=>weighDimes _ _ _ h,fun _ h=>continuousDimes _ _ _ h⟩).penny _ )) _

variable (hz:C.Makes)
include hz
lemma stockBook {r:ℝ} (ψ:Test (n+1))(hψ:tsupport ψ ⊆ gathersIn C F T K r) :
    (∑ z ∈ spools C F T K b N p h r, ∫ V,asset v (yarns C F T K b N p h z r) ψ N V∂μ _)=
      (keyMass C N p:ℂ)*Order.smears C N p v ψ:=by
    let a:ℂ:=(C.S.a N:ℂ)^(4*(n+1)); let S:=spools C F T K b N p h r; let k:ℂ:=keyMass C N p
    let f(u):= ψ (Order.cells C N p u)* C.numeric N p v u; let U(z):= yarns C F T K b N p h z r
    have hh(z): (∫ V,asset v (U z) ψ N V∂μ _)= k*a*∑ u∈ U z, f u:=by
       let H(u: Fin (n+1) → Site (C.side N p))(V):= pullDimes v u (Stock.final (Fin (n+1))) N V
       let b(u: Fin (n+1)→ Site (C.side N p)):=ψ (Order.cells C N p u)
       simp only [asset,Pi.smul_apply,Finset.sum_apply,smul_eq_mul]; rw [integral_const_mul,integral_finsetSum]; swap
       · intro u _; exact ((continuousDimes v u (Stock.final (Fin (n+1))) le_rfl).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).const_mul _
       rw [mul_comm k a,mul_assoc]; apply congr_arg; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro u _; rw [integral_const_mul, fullDimes hz v u le_rfl]; unfold f k; ring
    change (∑ z ∈ S,∫ V,asset v (U z) ψ N V ∂ _)= k*(a*∑ u,f u); simp_rw [hh]; rw [← mul_assoc,← Finset.mul_sum]; refine congr_arg (fun z:ℂ=> k*a*z) ?_
    rw [← Finset.sum_biUnion]
    · refine (Finset.sum_subset (Finset.subset_univ (S.biUnion U)) fun i _ hi=>?_ ); unfold f
      apply mul_eq_zero_of_left _ (C.numeric ..)
      apply image_eq_zero_of_notMem_tsupport; intro hx; apply hi
      let z:= (C.S.toDepth h p).parent (i 0); have hj:i∈U z:= Finset.mem_filter.mpr ⟨Finset.mem_univ _,hψ hx,rfl⟩
      exact Finset.mem_biUnion.mpr ⟨_,Finset.mem_filter.mpr ⟨Finset.mem_univ _,i,hj⟩,hj⟩
    intro i _ j _ hij; apply Finset.disjoint_left.mpr; intro x hx hw; exact hij ((Finset.mem_filter.mp hx).2.2.symm.trans (Finset.mem_filter.mp hw).2.2)
end YM.RG17
