import YM.SchemeRG11.Wisp.Index
/-! Edge rewrite with compact support (no translating a conditionally
 summable tower). -/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeRG11.North
open Function Lattice Pert Maxwell Flock Bare Tree Bark Haze Pile Atoll Crest Labels MvPolynomial RawLabels
open scoped Classical
variable {G:Gauge} {E:Type*}[AddCommGroup E][Module ℝ E]
def drift (θ: Cover→G.Color)(v:Shaft G): Touch G:= ∑ c:G.ColorIndex, Finsupp.single (v.1,c) (G.ad (unitColor G c) (θ (v.1.1+step v.1.2) + θ v.1.1) v.2)
lemma drifts (θ: Cover→G.Color)(v:Shaft G)(A:trunk G ℤ): sense (cant A) (drift θ v)=cant (spur θ A) v:=by
 let Z:= θ (v.1.1+step v.1.2)+θ v.1.1
 unfold drift; rw [map_sum]; change _=G.ad (A v.1) Z v.2; conv_rhs=>rw [←Triangle.sum_color (A v.1)]
 rw [map_sum]; simp only [LinearMap.sum_apply,LinearMap.smul_apply,map_smul,LinearMap.smul_apply,WithLp.ofLp_sum, Finset.sum_apply,PiLp.smul_apply,smul_eq_mul,sense,Finsupp.linearCombination_single]
 exact Finset.sum_congr rfl fun _ _=>mul_comm ..
lemma rand_c (θ: Cover→G.Color)(p:Shaft G): G.ad (unitColor G p.2) (θ (p.1.1+step p.1.2)+θ p.1.1) p.2=0:=by
 let f:=unitColor G p.2; let b:= θ (p.1.1+step p.1.2)+θ p.1.1
 rw [← Align.to_color]; have hh:= G.ad_skew f b f; have he:G.ad f f=0:=by apply G.colorMat_injective; simp
 rw [he,inner_zero_right] at hh; linarith only [hh]
lemma rear0 (p:Shaft G)(θ:Cover→G.Color): vent ((land G).windfall (radius p)) (leaf (drift θ p))=0:=by
 rw [taste, domino, drift, map_sum]; simp only [sense,Finsupp.linearCombination_single,Pi.add_apply,splinter,Pi.single_apply,cant,Bark.ascent,knob, PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul,unitPaint]; rw [show (∑ i:G.ColorIndex,_)= (0:ℝ) from ?_,MvPolynomial.C_0] -- check
 apply Finset.sum_eq_zero; intro i _; by_cases hi:i=p.2
 · subst i; rw [rand_c]; simp
 simp [hi,show (p.1,i)≠p from fun w=>hi (congrArg Prod.snd w)]
lemma anti_b(a:Bevy E)(i j:Axis):bend a i j= -bend a j i:=by unfold Flock.bend; abel
lemma rear_sum (u:Finset Cover) (χ:Cover→ℝ)(h:∀p∉u, χ p=0 ∧ ∀i:Axis,χ (p-step i)=0)(f:Cover→ E)(i:Axis): ∑ p∈u,χ p • f p=∑ p∈u,χ (p-step i) • f (p-step i):=by
 let v:=u.filter fun p=>χ p≠0; let w:= u.filter fun p=>χ (p-step i)≠0
 have hx : w=v.image (fun p:Cover=> p+step i):=by
    ext x; simp only [v,w,Finset.mem_filter,Finset.mem_image,ne_eq]; constructor
    · rintro ⟨_,hq⟩; exact ⟨x-step i, ⟨by contrapose! hq; exact (h _ hq).1,hq⟩,sub_add_cancel ..⟩
    rintro ⟨y,⟨-,hy⟩,rfl⟩; rw [add_sub_cancel_right]; exact ⟨by contrapose! hy; simpa using (h _ hy).2 i,hy⟩
 have he : (∑ p∈u,χ p • f p)=∑ p∈v,χ p • f p:=(Finset.sum_subset (Finset.filter_subset ..) (fun p he hh=>by simp [show χ p=0 from not_ne_iff.mp (fun hp=>hh (Finset.mem_filter.mpr ⟨he,hp⟩))])).symm -- warning simp
 rw [he]; trans ∑ p∈w,χ (p-step i) • f (p-step i)
 · rw [hx,Finset.sum_image]; apply Finset.sum_congr rfl;intro t ht; simp
   exact fun _ _ _ _ h=>add_right_cancel h
 exact Finset.sum_subset (Finset.filter_subset ..) (fun p he hh=>by simp [show χ (p-step i)=0 from not_ne_iff.mp (fun hp=>hh (Finset.mem_filter.mpr ⟨he,hp⟩))])
lemma sum_tri (u:Axis→Axis→ℝ): (∑ i:Axis,∑ j:Axis, if i<j then u i j+u j i else 0)=∑ i:Axis,∑ j:Axis,if i≠j then u i j else 0:=by
 -- avoid Fin calc
 simp only [ite_add_zero]; rw [show ∑ i:Axis,∑ j:Axis,_= (∑i:Axis,∑j:Axis, if i<j then u i j else 0)+∑i:Axis,∑j:Axis, if i<j then u j i else 0 from by simp only [Finset.sum_add_distrib], Finset.sum_comm (f:=fun i j:Axis=> if i<j then u j i else 0),←Finset.sum_add_distrib]
 apply Finset.sum_congr rfl; intro i _; rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro j _; rcases lt_trichotomy i j with H|H|H <;> grind
lemma groove_i (χ:Cover→ℝ)(s:Finset Cover)(h: ∀ p∉s,χ p=0 ∧∀i:Axis,χ (p-step i)=0)(A B:Bevy G.Color) :
 ∑ z∈s,χ z * (∑ i:Axis,∑ j:Axis,(if i<j then inner ℝ (bend A i j z) (bend B i j z) else 0)) =
 ∑ z∈s,∑ j:Axis,∑ i:Axis,(χ (z-step i)*inner ℝ (bend A i j (z-step i)) (B j z)-χ z*inner ℝ (bend A i j z) (B j z)):=by
 let f(z:Cover)(i j:Axis):= inner ℝ (bend A i j z) (soar i (B j) z)
 have hh z:(∑i:Axis,∑j:Axis,(if i<j then inner ℝ (bend A i j z) (bend B i j z) else 0))= ∑ j:Axis,∑ i:Axis,f z i j:=by
   have hw i j:inner ℝ (bend A i j z) (bend B i j z)=f z i j+f z j i:=by
      change inner ℝ (bend A i j z) (_-_) = _
      rw [inner_sub_right]; conv_rhs=> unfold f; rw [anti_b A j i]; simp only [Pi.neg_apply,inner_neg_left]
      abel
   simp_rw [hw]; rw [sum_tri,Finset.sum_comm (f:=fun j i:Axis=> f z i j)]; apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; by_cases H:i=j
   · subst j; simp [f,Flock.bend]
   rw [if_pos H]
 simp_rw [hh,Finset.mul_sum]; rw [Finset.sum_comm, Finset.sum_comm (s:=s)] -- syntax
 apply Finset.sum_congr rfl; intro j _; rw [Finset.sum_comm,Finset.sum_comm (s:=s)]
 apply Finset.sum_congr rfl; intro i _; simp only [f,soar_apply,inner_sub_right,mul_sub]; rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]; congr 1
 exact Eq.trans (rear_sum (E:=ℝ) s χ h (fun z=> inner ℝ (bend A i j z) (B j (z+step i))) i) (Finset.sum_congr rfl fun z _=>by rw [sub_add_cancel]; rfl)
end YM.SchemeRG11.North
