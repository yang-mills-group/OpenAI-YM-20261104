import YM.Integration.WilsonMeasuredSignedActionAverage
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredSignedActionWindow
open Function Filter Finset Labels Extra.Histories
open WilsonMeasuredSignedActionCourse WilsonMeasuredSignedActionAverage
open scoped BigOperators Classical
variable {G:Gauge}(F:Frame G 4)

theorem scale (s:ℝ)(v:F.Coeff):pool F ((s:ℂ) • v)=(s:ℂ) • pool F v:=by
  have bar:star ((s:ℂ) • v)=(s:ℂ) • star v:=by funext i;simp
  simp only [pool,bar,←smul_add,map_smul,Finset.smul_sum]

theorem count (v:F.Coeff)(hv:fixed F v):
    pool F v=((2*(Fintype.card Signed:ℝ):ℝ):ℂ) • v:=by
  have bar:star v=v:=by
    simpa only [Motion.patch,if_true,show (1:Signed).ortho=1 from map_one Signed.inclusionO,
      Frame.act_one] using hv (1,true)
  have spin(s:Signed):F.act s.ortho v=v:=hv (s,false)
  simp only [pool,bar,map_add,spin,Finset.sum_const,Finset.card_univ]
  funext i
  simp [nsmul_eq_mul]
  ring

private theorem magnitude (s:ℝ)(v:F.Coeff):F.coeffSize ((s:ℂ) • v)=|s| *F.coeffSize v:=by
  simp [Frame.coeffSize,Finset.mul_sum]

private theorem negative (v:F.Coeff):F.core (-v)= -F.core v:=by
  funext i
  by_cases z:i=0 <;> simp [Frame.core,z]

theorem margin (simple:G.Simple){v:F.Coeff}{s:ℝ}(sp:0<s)
    (small:F.coeffSize ((s:ℂ) • F.core (pool F v)-axis F)<F.coeffSize (axis F)):
    positive F (pool F v):=by
  obtain ⟨t,gt⟩:=read simple (held F v)
  refine ⟨t,?_,gt⟩
  have n:0<F.coeffSize (axis F):=lt_of_le_of_lt (Work.G08.size_nonneg F _) small
  have combine:(s:ℂ) • ((t:ℂ) • axis F)-axis F=((s*t-1:ℝ):ℂ) • axis F:=by
    push_cast
    rw [sub_smul,one_smul,smul_smul]
  rw [gt,combine,magnitude] at small
  have h:|s*t-1|<1:=(mul_lt_mul_iff_of_pos_right n).mp (small.trans_eq (one_mul _).symm)
  have l:0<s*t:=by linarith only [neg_le_abs (s*t-1),h]
  exact (mul_pos_iff_of_pos_left sp).mp l

theorem pulled (simple:G.Simple)(A:F.Coeff≃ₗ[ℂ]F.Coeff)
    (moved:∀y w,Motion.patch F y (A w)=A (Motion.patch F y w))
    (signed:∀v,fixed F v→positive F v→positive F (A v))
    {v:F.Coeff}{s:ℝ}(sp:0<s)
    (heard:F.coeffSize ((s:ℂ) • F.core (pool F (A v))-axis F)<F.coeffSize (axis F)):
    ∃c:ℝ,0≤c ∧ F.core (pool F v)=(c:ℂ) • axis F:=by
  obtain ⟨t,gt⟩:=read simple (held F v)
  refine ⟨t,?_,gt⟩
  by_contra h
  have ht:t<0:=lt_of_not_ge h
  have negfixed:fixed F (-pool F v):=by
    rintro ⟨a,b⟩
    have fix:=held F v (a,b)
    cases b <;> simp only [Motion.patch,if_true,if_false,Bool.false_eq_true,map_neg,star_neg] at fix ⊢ <;> rw [fix]
  have npos:positive F (-pool F v):=by
    refine ⟨-t,neg_pos.mpr ht,?_⟩
    rw [negative,gt]
    simp
  obtain ⟨b,bp,bh⟩:=signed _ negfixed npos
  rw [map_neg,negative,linear F moved] at bh
  obtain ⟨c,cp,ch⟩:=margin F simple sp heard
  have nz:axis F≠0:=by
    intro z
    rw [z] at heard
    simpa [Frame.coeffSize] using (lt_of_le_of_lt (Work.G08.size_nonneg F _) heard)
  have both:((b+c:ℝ):ℂ) • axis F=0:=by
    rw [Complex.ofReal_add,add_smul,←bh,←ch,neg_add_cancel]
  have bad:= (smul_eq_zero.mp both).resolve_right nz
  have zero:b+c=0:=by exact_mod_cast bad
  linarith

end YM.Integration.WilsonMeasuredSignedActionWindow
end
