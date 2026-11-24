import YM.XSpace.Orbital
import YM.PECompat4984.Donor.Gaussian
/-! # No lost primary samples after Maxwell constraints -/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Stab
open Function Set Filter MeasureTheory Next.Rank Normal Maxwell Maxwell.Free ProbeLine MvPolynomial OJoint
open scoped Topology BigOperators InnerProductSpace ContDiff Classical Polynomial
variable {G : Gauge} {n k:ℕ}

lemma energy_wire (x:Points n)(h:x∈conf n) (k:ℕ)(c:G.ColorIndex) (a b: Deck n k)(u v:G.ColorIndex): (energy x G k).cov (a,u) (b,v)= if a.1=b.1 then 0 else if u=v then (fare c (pieces _ a.2.2) (pieces _ b.2.2) (x a.1-x b.1):ℂ) else 0:= by
  let p:=flavor _ u (pieces _ a.2.2); let q:=flavor _ v (pieces _ b.2.2)
  have he(z:WebKey G→₀ℂ)(w:WebKey G→ℂ): slit w (glyph z) = C (Finsupp.linearCombination ℂ w z) := by
    simp only [glyph,Finsupp.linearCombination_apply,Finsupp.sum,map_sum,(slit _).map_smul,slit_X,smul_eq_mul,map_mul,C_mul']
  have hp : MvPolynomial.C ((energy x G k).cov (a,u) (b,v)) = slit (form (x a.1) p) (factors (x b.1) q):= by rw [strokes]; exact (he _ _).symm
  apply C_injective (σ:=WebKey G); rw [hp,remainder_eqn];simp only [(show Injective x.ofLp from h).eq_iff]
  by_cases ht:a.1=b.1; · simp only [ht,ite_true]
  have h':x a.1 - x b.1≠0:= sub_ne_zero.mpr ((show Injective x.ofLp from h).ne ht)
  rw [if_neg ht,any_ink c _ _ u v h']; split <;> simp [*]

lemma carried (x:Points n)(h:x∈conf n) (k)(c:G.ColorIndex)(s:O G.ColorIndex):
    Normal.scope (changeRow (D:=Deck n k) s.val) (energy x G k)=energy x G k:= by
  apply Normal.Symmetric.ext; funext a b
  obtain ⟨a,u⟩:=a; obtain ⟨b,v⟩:=b;
  simp only [scope,treats,changeRow,map_sum,Finsupp.linearCombination_single,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,energy_wire x h k c]
  split_ifs with h' he
  · simp
  · subst u; let f:= fare c (pieces _ a.2.2) (pieces _ b.2.2) (x a.1 - x b.1); simp only [mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true];
    rw [show (∑ j:G.ColorIndex, (s.val v j:ℂ)*((s.val v j:ℂ)*(f:ℂ)))= (f:ℂ) by
      have he :∑ j,s.val v j*s.val v j=1:=by simpa [Matrix.mul_apply] using congr_fun (congr_fun ((Matrix.mem_orthogonalGroup_iff _ _).mp s.property) v) v
      simp only [← mul_assoc,← Finset.sum_mul, ← Complex.ofReal_mul, ← Complex.ofReal_sum,he,mul_one, Complex.ofReal_one,one_mul]]
  have hp : ∑ j,s.val v j*s.val u j=0:= by simpa [Matrix.mul_apply,Matrix.one_apply,Ne.symm he] using congr_fun (congr_fun ((Matrix.mem_orthogonalGroup_iff _ _).mp s.property) v) u
  simp only [mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true,← mul_assoc, ← Finset.sum_mul,← Complex.ofReal_mul, ← Complex.ofReal_sum]; rw [hp]; simp

lemma evoke_heat (x:Points n)(h:x∈conf n)(c:G.ColorIndex)(p:Mark G n k): evoke (milk (energy x G k) p)=milk (energy x G k) (evoke p):= by
  let K:=energy x G k
  apply grid_full; intro y; let L:= (MvPolynomial.aeval (R:=ℂ) (fun i => (↑(y i):ℂ))).toLinearMap
  have he (s:O G.ColorIndex): changing s (milk K p)=milk K (changing s p):= by unfold changing; rw [Normal.prepared,carried x h _ c s] -- inspect
  change L (evoke (milk K p))=(L.comp (milk K)) (evoke p)
  rw [(evoke_out _ L).2,(evoke_out ..).2]; simp_rw [he]; rfl

lemma taken (x:Points n)(h:x∈conf n)(c:G.ColorIndex)(p:Mark G n k)(hp:Silent (emitters x) (score x G k p)): evoke p=0:= by
  have he:= lost (licensed x c h p hp); rw [evoke_heat x h c p] at he; rw [← thaw (energy x G k) (evoke p),he, map_zero] -- inspect

abbrev Chamber (G:Gauge)(d:ℕ):= Channel (Voice d) G.ColorIndex

def appears (G:Gauge)(d:ℕ): Chamber G d→ₐ[ℂ] WickPol G := MvPolynomial.aeval (fun i: Voice d×G.ColorIndex => bit (G:=G) (pieces _ i.1.2) i.2)

def chord (x:TaylorTower G) (n:ℕ): VectorA (Voice n×G.ColorIndex):= WithLp.toLp 2 fun i=> flavor _ i.2 (pieces _ i.1.2) (x _)
lemma appears_read (p:Chamber G n)(x:TaylorTower G): probe x (appears G n p)=watches p (chord x n):= by
  apply DFunLike.congr_fun (f:=(probe x).comp (appears G n)); ext1 i; rw [AlgHom.comp_apply,appears,aeval_X,aeval_X]; exact symbol_test ..

lemma chord_full (Q:VectorA (Voice n × G.ColorIndex)): ∃ x:TaylorTower G,chord x n=Q:= by
  let V i (c:G.ColorIndex): Sheet (i:Fin n).val := ∑ v:Effects i.val,Q ((⟨i,v⟩:Voice n),c) • value _ v
  let A (i:Fin n) := ∑ c:G.ColorIndex,fill i.val (unitColor G c) (V i c)
  let x: TaylorTower G := fun i=> if h:i<n then A ⟨i,h⟩ else 0
  have he(i:Fin n)(c:G.ColorIndex): faceMap i.val (cp (G:=G) c) (A i) = V i c:= by unfold A; simp only [map_sum,which,unitPaint,ite_smul,one_smul,zero_smul]; simp
  refine ⟨x,?_⟩; apply PiLp.ext; intro i; obtain ⟨⟨i,v⟩,c⟩:=i
  change pieces i.val v (faceMap i.val (cp (G:=G) c) (x i.val))= _
  rw [show x i.val=A i by simp only [x,dif_pos i.isLt],he]; simp [V,map_smul, pieces, Finsupp.single_apply, mul_ite] -- fix

lemma appears_inj : Injective (appears G n):= by
  intro p q h; apply grid_full; intro y; obtain ⟨x,rfl⟩:= chord_full y
  rw [← appears_read,← appears_read,h]

-- all fields in shellSector fit. take n=d (allowed slight overestimate)
lemma modal (p: shellSector G n):∃ q, appears G n q=p.val:=by
  let a (i:Slot G) := scaleW i
  have hp:= ((Maxwell.Free.sector).mp p.property).1
  have hx (i: Slot G→₀ℕ)(hi:i∈p.val.support) (j:Slot G)(hj:j∈i.support): j.1<n:= by
    have hb: Maxwell.Free.degree i≤n:= hp hi
    have he : a j ≤ Maxwell.Free.degree i:= by unfold Maxwell.Free.degree; rw [Finsupp.weight_apply]; exact (le_mul_of_one_le_left (Nat.zero_le _) (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hj))).trans (Finset.single_le_sum (f:=fun j=>i j • scaleW j) (fun i _=> Nat.zero_le _) hj)
    change j.1+2 ≤ _ at he; omega
  let X:=p.val; let R:= (appears G n).range
  suffices X∈ R from this
  apply show p.val∈R → X∈R from id
  rw [MvPolynomial.as_sum p.val] -- dependent rw
  refine Subalgebra.sum_mem R fun i hi=>?_ ; rw [MvPolynomial.monomial_eq]; refine Subalgebra.mul_mem R (R.algebraMap_mem _) ?_
  unfold Finsupp.prod; refine Subalgebra.prod_mem _ fun j hj=>?_
  refine Subalgebra.pow_mem R ?_ _
  rw [← Maxwell.symbol_coordinate, Maxwell.Free.divide]; refine Subalgebra.sum_mem R fun c _=>?_
  let m:=j.1; let k:Flavor m:= flavor_pick (coordinateLeg j) c; change bit k c ∈ R
  let L:=pieces m
  let t:=hx i hi j hj

  rw [← L.sum_repr k,bit,map_sum]
  obtain ⟨Y,H⟩:= symbol_linear (G:=G) m
  rw [← H]; dsimp only; rw [map_sum]; refine Subalgebra.sum_mem R fun v _=>?_; simp only [map_smul]; rw [show Y (flavor _ c _) = bit (L v) c from congr_fun H _,← Complex.coe_smul]; exact Subalgebra.smul_mem R ⟨MvPolynomial.X ((⟨⟨_,t⟩,v⟩:Voice n),c),MvPolynomial.aeval_X (f:=fun i:Voice n×G.ColorIndex=> bit (pieces _ i.1.2) i.2) _⟩ _
end YM.XSpace.Stab
