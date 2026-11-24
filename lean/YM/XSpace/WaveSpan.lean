import YM.XSpace.Switchboard
/-!
# Externals move every bounded primary direction, even off any specified finite set

On multiple independent Maxwell gauge jets jointly. No independence
of cross covariance itself! Proof uses single-point pole homogeneity
and the genuine radial-flux injectivity lemma for the free field.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Stab
open Function Set Filter MeasureTheory Next.Rank Normal Maxwell Maxwell.Free ProbeLine MvPolynomial
open scoped Topology BigOperators InnerProductSpace ContDiff Classical Polynomial
variable {G: Gauge} {n k:ℕ}

abbrev value (k:ℕ):= Module.finBasis ℝ (Sheet k)
abbrev Effects (k:ℕ):= Fin (Module.finrank ℝ (Sheet k))
def pieces (k:ℕ):Module.Basis (Effects k) ℝ (Flavor k):= (value k).dualBasis
abbrev Voice (k:ℕ):=(i:Fin k)× Effects i.val -- through derivative k-1, k≥1 when probing B
abbrev Deck (n k:ℕ):= Fin n × Voice k

def emitters (x:Points n) : Finset E4:= Finset.univ.image x.ofLp

def fromFace (x:Points n)(c:G.ColorIndex)(y:E4)(a:Flavor 0)(d:Deck n k) := fare c (pieces _ d.2.2) a (x d.1-y)

lemma allt (x:Points n)(i): x i∈emitters x:= Finset.mem_image_of_mem _ (Finset.mem_univ i)
lemma flare_span (x:Points n)(h:x∈conf _) (U:Finset E4) (_he : emitters x⊆U) (c:G.ColorIndex) (α: Fin n→(j:Fin k)→Flavor j.val)
    (hq: ∀ z:E4,z∉U→∀ p:Flavor 0, ∑ i:Fin n,∑ j:Fin k,fare c (α i j) p (x i-z)=0):∀ i j,α i j=0:= by
  intro i J
  have hp (m j) (hJ:k-j.val=m) : α i j=0:= by
    induction m using Nat.strong_induction_on generalizing j with
    | h m ih=>
      have hy (a:Fin k) (ha:j<a): α i a=0:= ih (k-a.val) (by rw [← hJ]; omega) a rfl
      apply payment c; intro z hz v
      let Q(t:ℝ):=x i-t • z
      let H:=𝓝[>] (0:ℝ)
      have hs: Tendsto (fun t:ℝ=>Q t) H (𝓝 (x i)):= by
        have hz': ContinuousWithinAt Q (Set.Ioi 0) (0:ℝ):=(show Continuous Q by unfold Q; fun_prop).continuousWithinAt
        have he:= hz'.tendsto; rw [show Q 0=x i by simp [Q]] at he; exact he
      have hf:∀ᶠ t in H,Q t∉U:= by
        have hh (y:E4):∀ᶠ t in H,Q t≠y:= by
          by_cases he:y=x i
          · refine (show ∀ᶠ t in H,0<t from self_mem_nhdsWithin).mono fun t ht=> ?_; unfold Q; rw [he]; exact fun h=> smul_ne_zero (ne_of_gt ht) hz (by simpa using h)
          exact hs.eventually (isOpen_compl_singleton.mem_nhds (show x i ∈({y}ᶜ:Set E4) from Ne.symm he))
        exact ((eventually_all_finset U).mpr (fun y _=>hh y)).mono fun t ht ha=> ht _ ha rfl
      let T t i:= ∑ a:Fin k, fare c (α i a) v (x i-Q t)
      let d := 4+j.val
      have he (r:Fin n)(w:r≠i) : Tendsto (fun t:ℝ=> t^d*T t r) H (𝓝 0):= by
        have hh:x r-x i≠0:=sub_ne_zero.mpr ((show Injective x.ofLp from h).ne w)
        have hx a:Tendsto (fun t=>fare c (α r a) v (x r-Q t)) H (𝓝 (fare c (α r a) v (x r-x i))):= ((kernel_smooth (flavor (G:=G) _ c (α r a)) (flavor _ c v) hh).continuousAt).tendsto.comp (tendsto_const_nhds.sub hs)
        have he:= ((continuousWithinAt_id (s:=Set.Ioi 0) (x:= (0:ℝ))).tendsto.pow d).mul (tendsto_finsetSum Finset.univ fun a _=> hx a)
        simp only [id_eq,zero_pow (show d≠0 from by unfold d; omega),zero_mul] at he; exact he
      have ht : Tendsto (fun t:ℝ=> t^d*T t i) H (𝓝 0):= by
        let S:= Finset.univ.erase i
        have hp:Tendsto (fun t:ℝ=> ∑ r∈S,-(t^d*T t r)) H (𝓝 0):= by
          have hx:= tendsto_finsetSum S (fun r hr=> (he r (Finset.mem_erase.mp hr).1).neg)
          simpa using hx
        refine hp.congr' (hf.mono fun t ht=>?_)
        have hf:= congr_arg (fun y:ℝ=> t^d*y) (hq (Q t) ht v); change t^d*∑ j,T t j=_ at hf; rw [Finset.mul_sum] at hf
        simp only [mul_zero] at hf; rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),add_eq_zero_iff_eq_neg] at hf; rw [Finset.sum_neg_distrib]; exact hf.symm
      have hu (a:Fin k): Tendsto (fun t:ℝ=> t^d*fare c (α i a) v (x i-Q t)) H (𝓝 (if a=j then fare c (α i j) v z else 0)):= by
        have H':∀ t:ℝ,0<t→ fare c (α i a) v (x i-Q t)=t⁻¹^(4+a.val)*fare c (α i a) v z:= by
          intro t ht; unfold Q; rw [sub_sub_cancel]; simpa [fare] using (kernel_pole (flavor _ c (α i a)) (flavor 0 c v)).degree t ht z hz -- inspect
        rcases lt_trichotomy a j with H|H|H
        · have hi:∃ l:ℕ,d=(l+1)+(4+a.val):= ⟨d-(1+(4+a.val)),by unfold d; omega⟩
          obtain ⟨ℓ,Hd⟩:=hi
          rw [if_neg H.ne]; refine (show Tendsto (fun t:ℝ=> t^(ℓ+1)*fare c (α i a) v z) _ (𝓝 0) from ?_).congr' ?_
          · simpa using (continuousWithinAt_id (x:= (0:ℝ)) (s:=Ioi 0)|>.tendsto.pow (ℓ+1)).mul (tendsto_const_nhds (x:=fare c (α i a) v z))
          filter_upwards [self_mem_nhdsWithin] with t ht; rw [H' t ht,Hd,pow_add, inv_pow]; have h:t≠0:=ne_of_gt ht; field_simp; ring
        · subst a; rw [if_pos rfl]; apply (tendsto_const_nhds (x:=fare c _ v z)).congr'; filter_upwards [self_mem_nhdsWithin] with t ht; rw [H' t ht]; unfold d; have h:t≠0:=ne_of_gt ht; rw [inv_pow]; field_simp
        rw [if_neg H.ne']; apply (tendsto_const_nhds (x:=(0:ℝ))).congr'; filter_upwards [self_mem_nhdsWithin] with t ht; rw [H' t ht,hy a H]; rw [show fare c (0:Flavor a.val) v z=0 from LinearMap.congr_fun (map_zero (assay c hz a.val 0)) v]; simp
      have hh:= tendsto_finsetSum Finset.univ (fun a _=> hu a)
      simp only [← Finset.mul_sum,Finset.sum_ite_eq',Finset.mem_univ,ite_true] at hh
      exact tendsto_nhds_unique hh ht
  exact hp _ J rfl
lemma waves_launch (x:Points n)(k:ℕ)(h:x∈conf _) (U:Finset E4)(he:emitters x⊆ U)(c:G.ColorIndex):
    Submodule.span ℝ {v : Deck n k→ ℝ|∃ y∉U,∃ p:Flavor 0,v=fromFace x c y p}=⊤:= by
  let V:= Deck n k→ℝ
  let S := Submodule.span ℝ {v : Deck n k→ ℝ|∃ y∉U,∃ p:Flavor 0,v=fromFace x c y p}
  have hp(f:V→ₗ[ℝ] ℝ)(hF:∀ y∉ U,∀ p:Flavor 0,f (fromFace x c y p)=0): f=0 := by
    let α (v:Deck n k):= f (Pi.single v 1)
    have ht (w: V): f w=∑ v:Deck n k,w v*α v:= by
      conv_lhs=> rw [show w=∑ i:Deck n k,w i • Pi.single i (1:ℝ) from _root_.funext fun i=>by simp [Pi.single_apply,Finset.sum_apply,mul_ite]]
      rw [map_sum]; simp_rw [map_smul]; rfl
    let A (i:Fin n) (j:Fin k):Flavor j.val:= ∑ z:Effects j.val, α (i,⟨j,z⟩) • pieces j.val z
    have hh :∀ i j,A i j=0:= by
      apply flare_span x h U he c; intro y hy p
      rw [← hF y hy p,ht,Fintype.sum_prod_type]; simp_rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _
      have hz:=sub_ne_zero.mpr (ne_of_mem_of_not_mem (he (allt x i)) hy)
      unfold A; rw [← fare_pair c _ _ hz, map_sum (assay c hz j.val 0),LinearMap.sum_apply]; refine Finset.sum_congr rfl fun v _=> ?_; rw [map_smul,LinearMap.smul_apply]; exact mul_comm ..
    have hv i : α i=0:= by
      obtain ⟨i,a,b⟩:=i
      have hp := hh i a
      unfold A at hp; replace hp:= DFunLike.congr_fun (congr_arg ((pieces a.val).repr) hp) b; simpa [Finsupp.single_apply,Finsupp.finsetSum_apply,mul_ite] using hp
    apply LinearMap.ext; intro i; rw [ht]; simp [hv]
  have hv : S.dualAnnihilator=⊥:= by
    rw [eq_bot_iff]; intro f hf; apply (Submodule.mem_bot _).mpr
    exact hp f fun y hy q=> Submodule.mem_dualAnnihilator _ |>.mp hf _ (show fromFace x c y q∈ S from Submodule.subset_span ⟨y,hy,q,rfl⟩)
  apply Submodule.eq_top_of_finrank_eq; have h:= Subspace.finrank_add_finrank_dualAnnihilator_eq S; rw [hv,finrank_bot,add_zero] at h; exact h
end YM.XSpace.Stab
