import YM.FormalBulk08.Avenue.Hear
set_option autoImplicit false
noncomputable section
namespace YM.FormalBulk08.Avenue
open Filter Set Metric MeasureTheory Function Lattice Laurent Bloch Exterior Precision RG Next.Free
open Stationary
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix
variable {n:Side}
open MSbar.Tree.Resolvent
variable {j:ℕ}{k:ℝ}
open Flat UVExtension.Free
variable {G:Gauge}
open Reef Mesa Gorge

variable {D l:ℕ}
open Kemp Pose Dawn Spigot Orb Wick Series Jets MeasureTheory Lotus Shore Lava Rift
open Grail
variable {x:Loc G 1}{η σ A B C:ℝ}{u r p:ℕ} {q:edgeL G→edgeL G→ℝ}
open City PowerSeries Wilson
lemma suits_orth (g:G.El): suit g*(suit g)ᵀ=1:= by
    apply mul_eq_one_comm.mp; ext i j; let F:= EuclideanSpace.basisFun (hue G) ℝ
    have he b : (moon G).symm (F b)=Pi.single b 1:= by ext1 u; simp [F,moon, Pi.single_apply]
    have hx b v: suit g b v=G.adjoint g (F v) b:= by
       change _= (moon G).symm (G.adjoint g (F v)) b; rw [←shy,he,Matrix.mulVec_single_one];rfl
    rw [Matrix.mul_apply,Matrix.one_apply]; simp_rw [Matrix.transpose_apply,hx,← Work.F03.inner_color]
    let L: G.Color→ₗᵢ[ℝ] G.Color:={G.adjoint g with norm_map':= fun i=> G.norm_adjoint g i};change inner ℝ (L _) (L _) = _;rw [L.inner_map_map]; simp [OrthonormalBasis.inner_eq_ite]
private lemma tint_sums (s : wire G n) (f:wire G n→ℝ)(h:∀ j:wire G n,s.1 ≠ j.1 ∨ s.2.1 ≠ j.2.1→ f j=0):∑ j,f j= ∑ u:hue G,f (rowD s u):= by
   rw [Fintype.sum_prod_type, Finset.sum_eq_single s.1];rotate_left
   · intro b _ hb; exact Finset.sum_eq_zero fun i _=>h (b,i) (Or.inl (Ne.symm hb))
   · simp
   rw [Fintype.sum_prod_type, Finset.sum_eq_single s.2.1];rfl
   · intro b _ hb; exact Finset.sum_eq_zero fun i _=>h (s.1,b,i) (Or.inr (Ne.symm hb))
   simp
private lemma darkness (g:G.El)(x y:wire G n)(h:x.1≠y.1 ∨ x.2.1≠y.2.1): pointL g n x y=0:= if_neg (fun e=>h.elim (· e.1) (· e.2))
lemma copies_color (g:G.El)(A:Matrix (Body 1 n) (Body 1 n) ℝ) : pointL g n*patron G A = patron G A * pointL g n := by
   ext i j; rw [Matrix.mul_apply,Matrix.mul_apply]
   calc _ = ∑ x:hue G,pointL g n i (rowD i x)*patron G A (rowD i x) j:=tint_sums _ _ fun a h=> by rw [darkness _ _ a h, zero_mul]
        _ = ∑ x:hue G,patron G A i (rowD j x) *pointL g n (rowD j x) j:= by
            have hx x: pointL g n i (rowD i x) * patron G A (rowD i x) j = if x = j.2.2 then suit g i.2.2 x*A (i.1,i.2.1) (j.1,j.2.1) else 0:= by by_cases h:x=j.2.2 <;> simp only [pointL,rowD,blue_cost,eq_self,and_true,h,↓reduceIte,mul_zero]
            have he x: patron G A i (rowD j x)* pointL g n (rowD j x) j=if x=i.2.2 then A (i.1,i.2.1) (j.1,j.2.1)*suit g x j.2.2 else 0:= by
               by_cases h:x=i.2.2
               · simp only [pointL,rowD,blue_cost,eq_self,and_true,h,↓reduceIte]
               simp only [pointL,rowD,blue_cost,h,Ne.symm h,↓reduceIte,zero_mul]
            simp_rw [hx,he];simp only [Finset.sum_ite_eq',Finset.mem_univ, ↓reduceIte,mul_comm]
        _ = _ := (tint_sums j (fun x=>patron G A i x * pointL g n x j) (fun a h=>by rw [darkness g a j (h.imp Ne.symm Ne.symm),mul_zero])).symm
lemma point_price (g:G.El)(v:Train j)(n:Side)(k:ℝ): pointL g n*bandR G v k n*(pointL g n)ᵀ=bandR G v k n := by
    unfold bandR; rw [copies_color,Matrix.mul_assoc,show pointL g n *(pointL g n)ᵀ=1 from ?_,Matrix.mul_one]
    ext i j'; rw [Matrix.mul_apply, tint_sums i (fun x=>pointL g n i x*(pointL g n)ᵀ x j') (fun a h=>by rw [darkness _ _ a h,zero_mul])]
    rcases i with ⟨x,i,a⟩;rcases j' with ⟨y,k,b⟩; by_cases h:x=y∧ i=k; swap
    · rw [Finset.sum_eq_zero (s:=Finset.univ),Matrix.one_apply_ne (show _ from fun hl=> h (by simp_all))]; intro j _; rw [Matrix.transpose_apply, show pointL g n (y,k,b) _=0 from if_neg (fun hl=> h (And.intro hl.1.symm hl.2.symm)),mul_zero]
    obtain ⟨rfl,rfl⟩:=h; simp only [rowD,pointL,Matrix.transpose_apply,eq_self,and_true,↓reduceIte, Matrix.one_apply,Prod.mk.injEq,true_and]; have he:=congr_fun (congr_fun (suits_orth g) a) b; rw [Matrix.one_apply] at he; exact he
lemma mantle_glow (T:Pap (wire G n))(h:Glare T 0)(g:G.El): coeff 0 T = mixRows (pointL g n) (coeff 0 T):= by
   let P:= coeff 0 T; let V:=mixRows (pointL g n) P; let N:=max P.totalDegree V.totalDegree
   have he i: marble i P=marble i V:= by unfold V; rw [Lava.target]; exact luster g T h 0 i (le_refl _)
   have hp (X:TypeR (wire G n))(hh:X.totalDegree≤ N): (∑ i∈ Finset.range (N+1),facade i (marble i X)) = X:= crema X N (fun r hr=> (marble_eq_zero_iff _ X).mpr (MvPolynomial.homogeneousComponent_eq_zero _ _ (lt_of_le_of_lt hh hr)))
   change P=V; exact (hp P (le_max_left ..)).symm.trans ((Finset.sum_congr rfl (fun i _=>congr_arg _ (he i))).trans (hp V (le_max_right ..)))
-- operations directly on leading core
variable {T: Anthem D G}
lemma tor_earn (v:Train j)(n:Side)(k:ℝ)(p:Dawn.Studio D)(h:Glyph x T l 0)(g:G.El):
    let Q:=hearth (bandR G v k n) (coeff 0 (Kemp.banner l (T p) n))
    Q=mixRows (pointL g n) Q:= by
        intro Q; let V:=bandR G v k n; unfold Q; nth_rw 1 [mantle_glow _ (h.glows n p) g]; rw [hearth_mix V,point_price]
end YM.FormalBulk08.Avenue
