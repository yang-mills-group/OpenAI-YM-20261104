import YM.XSpace.TrinityFields
/-! # Color argument and selection of the initial projects -/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Chiral
open Function Set Filter Lattice Trace Chart2 Maxwell Maxwell.Free Normalize Structure1 Source Source.Drops Wilson MvPolynomial Stall Pages Next.Rank.Normal Finsupp Mu
open scoped Topology BigOperators InnerProductSpace Classical
variable {G:Gauge} {d:ℕ} {I:Type*}
lemma rank1_support (s:I→₀ℕ)(h:Volume s=1):∃ i,s= single i 1:=by
  have he:s.support.Nonempty:=by rw [Finset.nonempty_iff_ne_empty,ne_eq,Finsupp.support_eq_empty]; rintro g; simp [g,Volume] at h
  obtain ⟨i,hi⟩:=he; have hg: single i 1 ≤ s:= Finsupp.single_le_iff.mpr (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi)); obtain ⟨v,hv⟩:= exists_add_of_le hg; rw [hv, add_comm,Pages.volume_fee] at h; have ht:= size_nil (s:=v) (by omega); exact ⟨i,by rw [hv,ht, add_zero]⟩
lemma monomial_single_one (p:I)(a:ℂ) : monomial (single p 1) a = C a * MvPolynomial.X p:= by simp [C_mul_monomial,MvPolynomial.X]
lemma mic {q:Stamp G}(h: Hom q 1) (X Y: Contact G)(v:ℝ): pit (X + v • Y) q= pit X q + v • pit Y q:=by
  rw [q.as_sum]; simp_rw [_root_.map_sum, Finset.smul_sum, ← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro i hi; obtain ⟨j,rfl⟩:= rank1_support i (h (MvPolynomial.mem_support_iff.mp hi)); simp only [monomial_single_one, map_mul,pit,aeval_X,aeval_C,numbers,Pi.add_apply, Pi.smul_apply, PiLp.add_apply,PiLp.smul_apply,Algebra.algebraMap_self,RingHom.id_apply,Complex.real_smul,smul_eq_mul]; push_cast; ring
lemma mic0 {q:Stamp G}(h: Hom q 1): pit (0:Contact G) q=0:=by 
  have ht:= sags h 0 (0:Contact G); simpa using ht
private def singleA (e:Edge Cover): G.Color →ₗ[ℝ] Contact G:= LinearMap.single ℝ (fun _:Edge Cover=> G.Color) e
lemma tune_mic {q:Stamp G}(h: Hom q 1) (e:Edge Cover):∃ f:G.Color →ₗ[ℝ] ℂ,∀ x : G.Color,f x=pit (singleA (G:=G) e x) q:=by
  let f (x:G.Color):=pit (singleA e x) q; let A := singleA (G:=G) e
  have h1 (x y): f (x+y)= f x+ f y:=by
    have he:= mic h (A x) (A y) 1; simp_rw [one_smul] at he; unfold f; rw [map_add]; exact he
  have h2 (x:G.Color)(k:ℝ):f (k • x)= k • f x:=by unfold f; rw [map_smul, Pages.sags h,pow_one,Complex.real_smul]
  exact ⟨{toFun:=f, map_add':=h1,map_smul':=fun a x=> h2 x a},fun _=>rfl⟩
private lemma crown (x y:UnitIndex G) (a:ℂ) : pit (crumb x) (monomial (single y 1) a)= if x=y then a else 0:=by rw [monomial_single_one]; simp only [pit,numbers,aeval_X,aeval_C,map_mul,Algebra.algebraMap_self,RingHom.id_apply,← ram_at,dotter]; by_cases h:y=x; rw [if_pos h, if_pos h.symm]; simp; rw [if_neg h,if_neg (Ne.symm h)]; simp
lemma color_mic {q:Stamp G}(h: Hom q 1)(S:Show.Color G q)(H:G.Simple): q=0:=by
  have ht(c:UnitIndex G): pit (crumb c) q=0:=by
    obtain ⟨L,hL⟩:=tune_mic h c.1
    have he (g:G.El)(x:G.Color): L (G.adjoint g x)= L x:=by
      rw [hL,hL, show singleA c.1 (G.adjoint g x)=Show.paint g (singleA c.1 x) from funext fun i=> by rw [Show.pigment]; change Pi.single (M:=fun _ : Edge Cover=>G.Color) c.1 (G.adjoint g x) i= _; unfold singleA; by_cases hv:i=c.1 <;> simp [hv],← Show.greener,S g]
    have hp(t:Module.Dual ℝ ℂ): t ∘ₗ L=0:= singles_inv H _ (fun g x=>by simp [he]); have hq:L (basisC G c.2)=0:=Complex.ext (DFunLike.congr_fun (hp Complex.reLm) _) (DFunLike.congr_fun (hp Complex.imLm) _); rw [hL] at hq; exact hq
  ext1 s; by_contra hv; rw [MvPolynomial.coeff_zero] at hv; have hg := MvPolynomial.mem_support_iff.mpr hv; obtain ⟨i,rfl⟩:= rank1_support s (h hv); specialize ht i; rw [q.as_sum, _root_.map_sum, Finset.sum_eq_single_of_mem _ hg, crown,if_pos rfl] at ht; exact hv ht
  intro b hb hB; obtain ⟨t,rfl⟩:= rank1_support b (h (MvPolynomial.mem_support_iff.mp hb)); rw [crown,if_neg]; rintro rfl; contradiction
lemma color_strike (i:ℕ){q:Stamp G}(h:Show.Color G q): Show.Color G (strike (UnitIndex G) i q):= fun g=> by
  rw [← show strike _ i (Show.castTone g q)= Show.castTone g (strike _ i q) from ?_, h g]; apply Maxwell.Free.commuting
  intro j; unfold Show.castTone; rw [exchange_x]; exact strongs _
lemma color_lower (H:G.Simple){q:Stamp G}(h:Show.Color G q): strike _ 1 q=0:= color_mic (weightedHomogeneousComponent_mem ..) (color_strike _ h) H
lemma color_moved (x:Cover){q:Stamp G}(h:Show.Color G q): Show.Color G (Trace.volume x q):= by
  refine Show.tone fun g A=>?_ ; rw [Trace.ting,Trace.ting,show zone x (Show.paint g A)=Show.paint g (zone x A) from rfl, ← Show.greener,h g]
variable (W:Initialize G)
local notation "S" => W.surveys 4
lemma inkU : Show.Color G (Prelude.mark1 S (Ufield G)):= by intro g; unfold Prelude.mark1; rw [Show.cast_wick]; exact congr_arg flicker (Show.proud S _ g)
lemma inkTop (x:Cover): Show.Color G (u_1 W x):= by
  have he : u_1 W x= Trace.volume x (p1 S (0:Cover) (On.lifting (U G))):= by rw [stained, Outline.Chart.pull1, u_1,π1]; simp [Outline.Chart.lug]
  rw [he]; apply color_moved; rw [← show (Price.preparedL (Ufield G)).val=On.lifting (U G) from Price.preparedV (Ufield G)]; apply Show.proud
end YM.XSpace.Chiral
