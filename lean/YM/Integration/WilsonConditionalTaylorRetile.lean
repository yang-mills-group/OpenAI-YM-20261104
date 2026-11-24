import YM.FormalBulk08.Bank.Tee

/-! Reblock an arbitrary converging family of spatial kernels, on the actual
finite tori, with a single uniform price for the exponential strip. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorRetile
open FormalBulk08
open Lava Gorge Shore Lattice Laurent Filter Function Lotus Orb Wick Reef Jets Series PowerSeries Stationary Wilson Next.Free
open Exterior Bloch RG Precision UVExtension.Free Work.F08 Flat Mesa Tree Work.F05 Bank
open scoped Topology ENNReal BigOperators Classical

variable {I : Type} {c f : Side} (S : Ratio c f)

theorem distance (x y : Tor c (Tor S.count I)) :
    S.count.val*skit c (x.1-y.1) ≤ skit f (((splitCo S I).symm x).1-((splitCo S I).symm y).1)+8*S.count.val := by
  let A:=((splitCo S I).symm x).1
  let B:=((splitCo S I).symm y).1
  have price (v : Site S.count) : skit f (wrap f (lift v)) ≤ 4*S.count.val:=by
    apply (skirt f (lift v)).trans
    have hh : ∑ k:Axis,(lift v k).natAbs ≤ ∑ _:Axis,S.count.val:=by
      apply Finset.sum_le_sum;intro k _;have:=lift_centers v k;omega
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,Laurent.size,smul_eq_mul] using hh
  have first : S.count.val*skit c (x.1-y.1)=skit f (S.embed (x.1-y.1)):=by
    unfold skit;rw [S.lift_embed];simp [size,Finset.mul_sum,Int.natAbs_mul]
  have shift : S.embed (x.1-y.1)=(A-B)+wrap f (lift y.2.1)+ -(wrap f (lift x.2.1)):=by
    change S.embed (x.1-y.1)=((S.embed x.1+_)-(S.embed y.1+_))+_+_
    rw [←S.root_embed,map_sub];simp only [S.root_embed];abel
  rw [first,shift]
  have d:=skit_add f ((A-B)+wrap f (lift y.2.1)) (-wrap f (lift x.2.1))
  have p:=skit_add f (A-B) (wrap f (lift y.2.1))
  rw [skit_neg] at d
  have px:=price x.2.1;have py:=price y.2.1
  change _ ≤ skit f (A-B)+8*S.count.val
  omega

theorem span {r : ℕ} (v : chain (Tor c (Tor S.count I)) r) :
    S.count.val*wide (lake c _) v ≤ wide (lake f _) ((splitCo S I).symm ∘ v)+8*S.count.val := by
  rw [Nat.mul_comm]
  refine (Nat.le_div_iff_mul_le S.count.property).mp (known_wide _ _ _ fun i j=>?_)
  apply (Nat.le_div_iff_mul_le S.count.property).mpr
  rw [Nat.mul_comm]
  apply (distance S (v i) (v j)).trans (Nat.add_le_add_right ?_ _)
  exact reached (lake f _) ((splitCo S I).symm ∘ v) i j

theorem weight {r : ℕ} {σ τ : ℝ} (v : chain (Tor c (Tor S.count I)) r) (h : τ ≤ S.count.val*σ) (he : 0 ≤ τ) :
    shine τ (wide (lake c _) v) ≤ ENNReal.ofReal (Real.exp (8*τ))*shine σ (wide (lake f _) ((splitCo S I).symm ∘ v)) := by
  let a:=wide (lake c _) v
  let z:=wide (lake f _) ((splitCo S I).symm ∘ v)
  have hp : (S.count.val:ℝ)*a ≤ (z:ℝ)+8*S.count.val:=by exact_mod_cast span S v
  have nonzero : 0 < (S.count.val:ℝ):=by exact_mod_cast S.count.property
  have t : τ*(a:ℝ) ≤ 8*τ+σ*(z:ℝ):=by
    apply le_of_mul_le_mul_left (a:=(S.count.val:ℝ)) _ nonzero
    have h1:=mul_le_mul_of_nonneg_left hp he
    have h2:=mul_le_mul_of_nonneg_right h (Nat.cast_nonneg z : (0:ℝ) ≤ (z:ℝ))
    nlinarith only [h1,h2]
  unfold Gorge.shine
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,←Real.exp_add]
  exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr t)

theorem amount {r : ℕ} {σ τ C : ℝ} {T : Tile (Tor f I) r} (bound : τ ≤ S.count.val*σ) (pos : 0 ≤ τ)
    (price : Bail (lake f _) σ T C) : Bail (lake c _) τ (jetty (splitCo S I).symm T) (Real.exp (8*τ)*C) :=by
  refine ⟨mul_nonneg (Real.exp_pos _).le price.1,fun i a=>?_⟩
  let F : Gorge.pack i a→Gorge.pack i ((splitCo S I).symm a):=fun u=>⟨(splitCo S I).symm ∘ u.val,congr_arg _ u.property⟩
  rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
  refine le_trans ?_ (mul_le_mul_right (price.watch F (fun v w hv=>Subtype.ext (funext fun j=>(splitCo S I).symm.injective
    (congr_fun (congr_arg Subtype.val hv) j)))) _)
  rw [←ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun v=>?_
  unfold glitter jetty
  exact (mul_le_mul_left (weight S v.val bound pos) _).trans_eq (mul_assoc ..)

theorem sides (L : Side) : Tendsto (fun n : Side=>n*L) atTop atTop:=by
  apply tendsto_atTop.mpr;intro m
  filter_upwards [eventually_ge_atTop m] with n hn
  exact hn.trans (Nat.le_mul_of_pos_right n.val L.property)

theorem scaled {r : ℕ} (L : Side) {σ τ : ℝ} (h : τ ≤ L.val*σ) (he : 0 ≤ τ) {A : Tile (Biglot I) r}
    {U : (n:Side)→Tile (Tor n I) r} (prior : Kith σ A U) :
    Kith τ (jetty (scroll L I).symm A) (fun n=>jetty (splitCo (endo n L) I).symm (U (n*L))) :=by
  obtain ⟨lines,C,price⟩:=prior
  refine ⟨?_,Real.exp (8*τ)*C,?_⟩
  · intro v
    have ready:=(lines ((scroll L I).symm ∘ v)).comp (sides L)
    apply ready.congr
    intro n
    apply congrArg (U (n*L));funext i
    have wire:=scroll_pull ((scroll L I).symm (v i)) (endo n L)
    change drip n (scroll L I ((scroll L I).symm (v i)))=(splitCo (endo n L) I) (drip (n*L) ((scroll L I).symm (v i))) at wire
    rw [Equiv.apply_symm_apply] at wire
    apply (splitCo (endo n L) I).injective
    change (splitCo (endo n L) I) (drip (n*L) ((scroll L I).symm (v i)))=
      (splitCo (endo n L) I) ((splitCo (endo n L) I).symm (drip n (v i)))
    rw [Equiv.apply_symm_apply];exact wire.symm
  filter_upwards [(sides L).eventually price] with n paid
  exact amount (endo n L) h he paid

end YM.Integration.WilsonConditionalTaylorRetile
end

