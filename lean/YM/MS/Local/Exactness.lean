import YM.MS.Local.Radial
/-!
# The one-leg complex has no negative-charge cohomology

Kernel of Maxwell symbol on polynomial vectors uses radial derivative division.
Can retain grade bound ~UINT from start.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Local.BV
open Function Filter Set Finset Plane Koszul Real Momentum Wire Tensor
open Landau Detect Detect.Mark Radial Submodule MatrixLet
open Complex (I)
open scoped Topology ContDiff
variable {G: Gauge} {h q : ℤ}

lemma norm_part (x : FourP) (hx:x≠0) : Momentum.sq x≠0:= ne_of_gt ((sq_pos_of_pos (norm_pos_iff.mpr hx)).trans_le (Momentum.sup_square x)) -- sq_pos_of_pos?
lemma parallel_from_K (L: Axis→ℂ) (x: FourP) (h : ∀ i:Axis, ∑ j:Axis, (precision j i x:ℂ)*L j=0) (i j : Axis): (x j:ℂ)*L i=(x i:ℂ)*L j:= by
   by_cases hv:x=0; subst x; simp
   let T:= ∑ i:Axis,(x i:ℂ)*L i
   have ht i : (Momentum.sq x:ℂ)*L i=(x i:ℂ)*T := by
       unfold precision delta at h
       specialize h i; simp_rw [Complex.ofReal_sub,Complex.ofReal_mul,sub_mul, apply_ite ((↑):ℝ→ℂ),Complex.ofReal_zero,ite_mul,zero_mul] at h
       unfold T; rw [Finset.sum_sub_distrib] at h; simp at h
       rw [Finset.mul_sum,(sub_eq_zero.mp h)]; exact Finset.sum_congr rfl fun _ _=>by ring
   have hn : (Momentum.sq x:ℂ)≠0:= by exact_mod_cast norm_part x hv
   apply mul_left_cancel₀ hn; rw [mul_left_comm,mul_left_comm (Momentum.sq x:ℂ) (x i:ℂ),ht,ht]; ring

variable {f : Grade G}
lemma top_ghost (hf:f∈yields h (-2)) (H:Q f=0): f=0:= by
   ext ⟨⟨⟨_|i,_|_⟩,c⟩,p⟩ <;> first | (solve | refine (seedStar.mp hf).real' _ ?_; norm_num [ghostNo,ghostChannel])| skip
   change f (S c p)=0; let T:= fun p=> f (S c p)
   have ht i p:= movesU f c i p -- check order
   rw [H] at ht
   have hq p (hp : (p:FourP) 0≠0): T p=0:= by simpa [hp,T] using (ht 0 p).symm
   by_cases hv:p 0=0; swap; exact hq p hv
   let L:= fun t:ℝ=> p+t • spike 0; have hz : Continuous (T ∘ L):= ((seedStar.mp hf).form (gaugeC,c)).smooth.continuous.comp (by unfold L; fun_prop: Continuous L)
   have he : T ∘ L =ᶠ[𝓝[≠] 0] 0:= by
      filter_upwards [self_mem_nhdsWithin] with t ht; have ht:t≠0:= ht; exact hq _ (by simp [L,hv,ht])
   have hd:= tendsto_nhds_unique (Filter.Tendsto.congr' he hz.continuousWithinAt) (show Tendsto _ _ (𝓝 (0:ℂ)) from tendsto_const_nhds)
   simpa [comp_apply, L,T] using hd

-- one-letter primitive implementing $Q A^+$ negative; use pure ghost `S`.
def Ssharp (u : CI G→FourP→ℂ) : Grade G := fun l=> if ghostNo l.1= -2 then u l.1.2 l.2 else 0
lemma sharp_at (u : CI G→FourP→ℂ) (he : ∀ i : CI G, Plane.Shape (u i) (h-4)) : Ssharp u∈ yields h (-2):= by
   refine seedStar.mpr ⟨fun i=> ?_, fun i h'=>if_neg h'⟩; by_cases h1:ghostNo i= -2
   · unfold Ssharp; dsimp only; simp only [h1,↓reduceIte]; rcases i with ⟨⟨_|i,_|_⟩,c⟩ <;> norm_num [ghostNo,ghostChannel] at h1
     exact he c
   unfold Ssharp; dsimp only; simp only [h1,↓reduceIte]; exact form_zero _
lemma anti_ghost (hF:f∈ yields h (-1)) (H:Q f=0) : ∃ g∈ yields h (-2), Q g=f:= by
   let U (c:CI G) (i:Axis) (x:FourP):= f (Landau.Detect.U i c x)
   have hU (i) (c:CI G) : Plane.Shape (U c i) (h-3):= (seedStar.mp hF).form (anti i,c)
   rcases lt_or_ge h 3 with hx|hx
   · have he : f=0:= by
        ext ⟨⟨⟨_|i,_|_⟩,c⟩,p⟩ <;> first | (solve | refine (seedStar.mp hF).real' _ ?_; norm_num [ghostNo,ghostChannel])| exact congr_fun ((hU i c).charge (by omega)) p
     exact ⟨0,zero_mem _,by simp [he]⟩
   have hz c p a i : (p a:ℂ)*U c i p=(p i:ℂ)*U c a p := by
      refine parallel_from_K (fun i=> U c i p) p (fun j=>?_) i a
      have hL:= movesA f c j p; rw [H] at hL; simpa [U,Finset.sum_neg_distrib] using hL.symm
   have hn : (h:ℂ)≠0:= Int.cast_ne_zero.mpr (by omega)
   let T := fun c p=> I*((h:ℂ)⁻¹)*(Radial.div (U c) p)
   have he : ∀ c: CI G, Plane.Shape (T c) (h-4) := by
      intro c; convert (Radial.div_shape (fun i=>hU i c)).scalar (I*(h:ℂ)⁻¹) using 1; rfl; omega
   refine ⟨Ssharp T,sharp_at _ he,?_⟩; have hm : Q (Ssharp T)∈ yields h (-1):= stays _ h _ (sharp_at _ he)
   ext ⟨⟨⟨_|i,_|_⟩,c⟩,p⟩ <;> first | (solve | refine ((seedStar.mp hm).real' _ ?_).trans ((seedStar.mp hF).real' _ ?_).symm <;> norm_num [ghostNo,ghostChannel])| skip
   change Q (Ssharp T) (Landau.Detect.U i c p)=U c i p
   have hx := Radial.taken (fun i=>hU i c) (hz c) p i
   push_cast at hx
   rw [movesU]; simp only [Ssharp, ghostNo, ghostChannel,↓reduceIte]; unfold T
   have he': I^2=(-1:ℂ):= Complex.I_sq
   field_simp; linear_combination -hx - ((p i:ℂ)*Radial.div (U c) p)*he'

lemma below (hf : f∈yields h q) (he:q< -2): f=0:= by
   ext ⟨⟨⟨_|i,_|_⟩,c⟩,p⟩ <;> (refine (seedStar.mp hf).real' _ ?_; norm_num [ghostNo,ghostChannel]; omega)
lemma negative (hf : f∈ yields h q) (hq:q<0) (hQ : Q f=0): ∃ g∈ yields h (q-1), Q g=f:= by
   by_cases he:q= -1; · subst q; exact anti_ghost hf hQ
   have hx : f=0:= by
       by_cases hv:q= -2; · subst q; exact top_ghost hf hQ
       exact below hf (by omega)
   exact ⟨0,zero_mem _,by rw [hx,map_zero]⟩
end YM.MS.Local.BV
