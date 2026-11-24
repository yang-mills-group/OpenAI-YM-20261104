import YM.WilsonCoeffUV.Ward.LocalChord

/-! Local form of the impulsive Ward recursion. Used for rooted moment
improvement. Tests still in arbitrary source-valued directions scalarized.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Power
open Lattice Laurent Bloch Exterior Wilson Precision RG Function Filter Metric
open Blue FreeResolvent Tree Matrix PowerSeries Next.Free Gauge
open scoped ContDiff Topology BigOperators Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {c:Side}{G:Gauge}

section slot
variable (a b:G.Color)(i:Edge (Site c))(j:G.ColorIndex)
-- Watt order e; lift linear.
def localC (e:ℕ): Ten ℝ (Woods G c) e:= fade (spear (sourceEdge i)) (shine (rye (electric a b j) e)) e
lemma local_eval (e:ℕ): coeff e (nameF (sourceEdge i) (jet (electric a b j)))=paint e (localC a b i j e) := by rw [←loom_spear,loom,coeff_map,jet_apply,localC,fade_one,shine_lit]; rfl
lemma local_null : localC (0:G.Color) 0 i j= fun _=>0 := by
  funext e
  apply unique_kernel (fade_pure (shine_pure (rye_sym (liveCurrent (0:G.Color) 0 j) _)) _ e) Smooth.zero
  change paint e (localC (0:G.Color) 0 i j e)= _; rw [← local_eval,emptyStop]; simp
lemma local_ground : localC a b i j 0=fun _=>(a-b) j := by
  funext r
  have ht:=local_eval a b i j 0; rw [nameF,coeff_map,coeff_zero_eq_constantCoeff_apply, jet_lead,electric_point,shell _ r] at ht
  apply MvPolynomial.C_injective (σ:=Woods G c); simpa using ht.symm

-- product as homogeneous

def lamp (e:ℕ)(P: Gen ℝ (Woods G c)): Gen ℝ (Woods G c):= fun r=> swirl (spore (shine (localC a b i j e)) (sever (sourceEdge i j) P) r)
lemma lamp_finite (e:ℕ)(P:Gen ℝ (Woods G c))(h:FiniteGen P): FiniteGen (lamp a b i j e P) := by
  have he : FiniteGen (shine (localC a b i j e)):=⟨e+1,fun i hi=>shine_dark (by omega)⟩
  exact squeezed _ (finite_spore he (finite_sever _ h))
lemma visible_lamp {e:ℕ}(P: Gen ℝ (Woods G c))(h:FiniteGen P)(ht:Pure P): totalR (lamp a b i j e P)= coeff e (nameF (sourceEdge i) (jet (electric a b j)))*MvPolynomial.pderiv (sourceEdge i j) (totalR P) := by
  have he : FiniteGen (shine (localC a b i j e)):=⟨e+1,fun i hi=>shine_dark (by omega)⟩
  rw [show totalR (lamp a b i j e P)=totalR (spore (shine (localC a b i j e)) (sever (sourceEdge i j) P)) from ?a,visible_spore he (finite_sever _ h),visible_sever h ht,visible_shine,local_eval]
  case a=> unfold totalR lamp; exact finsum_congr fun i=> swirl_paint _
lemma lamp_at (P:Gen ℝ (Woods G c)){r e:ℕ}(h:r<e): lamp a b i j e P r=0 := by
  unfold lamp; rw [show spore (shine _) _ _=0 from ?io,swirl_exact Smooth.zero]
  case io=> apply Finset.sum_eq_zero; intro u hu; rw [shine_dark (by have he:= Finset.mem_antidiagonal.mp hu; omega), inter_zero_left]
lemma lamp_holds (P:Gen ℝ (Woods G c)){r e:ℕ}(h:e≤r): lamp a b i j e P r= swirl (interweave (localC a b i j e) (sever (sourceEdge i j) P (r-e)) r) := by
  unfold lamp spore; rw [Finset.sum_eq_single_of_mem (e,r-e)];
  · simp only [shine_lit]
  · exact Finset.mem_antidiagonal.mpr (by omega)
  intro x hx he; obtain ⟨u,v⟩:= x
  have hg:u≠e:= fun y=> he (Prod.ext y (by have h':u+v=r:=Finset.mem_antidiagonal.mp hx; change v=r-e; omega))
  rw [shine_dark (show e≠u from hg.symm), inter_zero_left]
lemma lamp_ground (P: Gen ℝ (Woods G c))(h:Pure P): lamp a b i j 0 P=(a-b) j • sever (sourceEdge i j) P:= by
  ext1 r; rw [lamp_holds a b i j P (Nat.zero_le _)]
  have ht : interweave (localC a b i j 0) (sever (sourceEdge i j) P r) r=(a-b) j • sever (sourceEdge i j) P r := by
    funext q; rw [local_ground, interweave,dif_pos (by omega),Pi.smul_apply]; congr 2
    funext i; change q _ = q i; congr 1; apply Fin.ext; simp
  rw [Nat.sub_zero,ht]; exact swirl_exact ((pure_sever (sourceEdge i j) h r).smul _)
lemma lamp_empty (P: Gen ℝ (Woods G c))(e:ℕ): lamp (0:G.Color) 0 i j e P=0 := by
  ext1 r; rcases lt_or_ge r e with hk|hk
  · exact lamp_at _ _ _ _ _ hk
  rw [lamp_holds _ _ _ _ _ hk, local_null,inter_zero_left,swirl_exact Smooth.zero]; rfl
end slot

section coords
variable (u:Site c→G.Color){P:PChart G c}
lemma unravels (w:rollTest (flash P) (flash P) 1 0) (n:ℕ)(p:shellK n P)(h:∀ i,Pure (P i))(k) :
    ∑ i:Edge (Site c),∑ j:G.ColorIndex,∑ s∈ Finset.antidiagonal k,lamp (u i.1) (u (i.1+step i.2)) i j s.1 (P s.2)=0 := by
  have hg i j e t : FiniteGen (lamp (u i.1) (u (i.1+step i.2)) i j e (P t)):= lamp_finite _ _ _ _ _ _ (finite_shell p _)
  refine gen_inj (finite_sum (fun i _=>finite_sum (fun j _=>finite_sum (fun v _=>hg i j v.1 v.2)))) (by exact ⟨0,fun _ _=>rfl⟩) (pure_sum (fun i _=>pure_sum (fun j _=>pure_sum (fun v _=>fun r=>swirl_smooth _)))) Pure.zero ?_
  have hx := congr_arg (coeff k) (wrench u w)
  simp_rw [map_sum, map_zero,coeff_mul,brush,blot_apply,flash,coeff_mk] at hx
  rw [visible_sum (fun i _=>finite_sum (fun j _=>finite_sum (fun v _=>hg i j _ _))),show totalR _=0 from (by simp [totalR]: totalR (0:Gen ℝ (Woods G c))=0), ←hx]
  apply Finset.sum_congr rfl; intro i _; rw [visible_sum (fun j _=>finite_sum (fun v _=>hg i j _ _))]; apply Finset.sum_congr rfl; intro j _; rw [visible_sum (fun v _=>hg i j _ _)]
  exact Finset.sum_congr rfl fun v hv=> visible_lamp _ _ _ _ (P _) (finite_shell p _) (h _)

-- decompose to neighbors avoiding self-edge degeneracy (eventual).
lemma step_ne (hc:1<c.val)(i:Axis) : (step i:Site c)≠0:= by
  intro h; have e:=congr_fun h i; haveI : Fact (1<c.val):=⟨hc⟩;
  simp at e
lemma one_site (w:rollTest (flash P) (flash P) 1 0)(n:ℕ)(p:shellK n P)(h:∀ i,Pure (P i))(hc:1<c.val)(b:G.Color)(x:Site c)(k) :
    ∑ v:Axis,∑ j:G.ColorIndex,∑ z∈Finset.antidiagonal k, (lamp b 0 (x,v) j z.1 (P z.2) + lamp 0 b (x-step v,v) j z.1 (P z.2))=0 := by
  let u : Site c→G.Color := Pi.single x b
  have he:= unravels u w n p h k
  rw [Fintype.sum_prod_type, Finset.sum_comm] at he
  rw [←he]; apply Finset.sum_congr rfl; intro j _
  let C (y:Site c): Gen ℝ (Woods G c) := ∑ i,∑ z∈Finset.antidiagonal k, lamp (u y) (u (y+step j)) (y,j) i z.1 (P z.2)
  have ht : x-step j ≠ x:= by simp [step_ne hc j]
  have hh : ∑ i,C i=C x+C (x-step j):= by
    rw [← Finset.add_sum_erase _ C (Finset.mem_univ x)]; rw [Finset.sum_eq_single (x-step j)];
    · intro y hy h'; have he : y≠x:=(Finset.mem_erase.mp hy).1
      have ht : y+step j≠x:= fun hd=> h' (eq_sub_of_add_eq hd)
      simp_rw [C,u,Pi.single_eq_of_ne he,Pi.single_eq_of_ne ht]; simp_rw [lamp_empty]; simp
    simp [ht]
  change _ = ∑ i,C i
  rw [hh]
  have hb : x+step j ≠ x:= by simp [step_ne hc j];
  simp only [C,u,Pi.single_eq_of_ne hb, Pi.single_eq_of_ne ht,sub_add_cancel,Pi.single_eq_same,Finset.sum_add_distrib]
end coords
end YM.WilsonCoeffUV.Power
