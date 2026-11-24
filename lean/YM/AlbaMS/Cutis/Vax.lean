import YM.AlbaMS.Cutis.Cool
/-!
# Scalar content of `T:day`. Kinetic Λ matrix. native period.

Show even at wrap & no separation. Scale later uniformly. Uses no comparison
assertion to adopt Hess artifacts (operates per totalized matrices and colors).
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Cutis.Winter
open Set Function Filter LinearMap Matrix
open scoped BigOperators Classical Topology Matrix InnerProductSpace
open Bric Loft Inlay Inlay.Net Odom Lattice Nexus
variable {n : Side}{G:Gauge}(n)(i j:Axis)

lemma mouth_vec (f:Arm n→ℝ) (x): ((mouth n i)ᵀ *ᵥ f) x=f (x,i):=by simp [mouth,Matrix.mulVec,dotProduct,eq_comm,ite_mul]
lemma tip_ap (u : Arm n→ℝ)(x:Site n): (tip n i j *ᵥ u) x=u (x,i)+u (x+step i,j)-u (x+step j,i)-u (x,j):=by
  rw [tip,Matrix.sub_mulVec,Pi.sub_apply, ← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec, delV,delV]; simp_rw [mouth_vec]; abel
lemma t_slab (p:Face (Per n))(v:Flit G (Arm n)): (squareN (Per n) p).arson (slabQ v)=tip n p.2.val.1 p.2.val.2 p.1 v.1 • base G v.2:=by
  obtain ⟨x,⟨⟨i,j⟩,hj⟩⟩:=p
  have hf e : slabQ v e= (Pi.single v.1 1 : Arm n→ℝ) e • base G v.2:=by rw [show v=(v.1,v.2) from rfl,Inlay.slab]; by_cases h:e=v.1<;> simp [h]
  change slabQ v (x,i)+slabQ v (x+step i,j)-slabQ v (x+step j,i)-slabQ v (x,j)= tip n i j x _ • _; -- MulVec projection equals entry
  rw [show tip n i j x v.1=(tip n i j *ᵥ Pi.single v.1 1) x by simp [Matrix.mulVec,dotProduct,Pi.single_apply,mul_ite],tip_ap]; simp only [add_smul,sub_smul] ; rw [hf,hf,hf,hf]
lemma pa (x:Arm n)(y:Vtx n): bound n x y=(if x.1 + step x.2=y then 1 else 0) - if x.1=y then 1 else 0:=by obtain ⟨x,i⟩:=x; simp [flash,del,Matrix.one_apply,limo] -- avoid progress
lemma earmark {Ω : Inlay.Net (Arm n) (Site n)} (F: Odom.Book Ω G)(x y:Flit G (Arm n)) : (waveLots F).Z x y = iteratedFDeriv ℝ 2 F.toLuster.caseG.val 0 ![slabQ x,slabQ y]:=by
  let U:=F.toLuster.caseG; let X':=bare (I:= Vtx n) U
  have he : F.main [Place.a x,Place.a y]= X' [Place.a x,Place.a y]:= by
    unfold Odom.Book.main superb feeds; simp only [Coil.plus_read,Coil.sub_read]; simp_rw [Coil.sum_read]
    have ht (x' u' v':Flit G (Arm n)): (K ℝ x' * Loft.beam Ω.chat x':Heave G (Arm n) (Site n) ℝ) [Place.a u', Place.a v']=0:=by simp_rw [K, Coil.mul_cons]; simp [Coil.tap_mul, Place.k, Place.a, Coil.polar, Coil.D_read,Coil.var_read] -- simpler zero via Inside projection D's
    have hs (x' :Flit G (Site n)) : (Loft.L (E:=Flit G (Arm n)) ℝ x'*rod (grit G (Site n)) x':Heave G (Arm n) (Site n) ℝ) [Place.a x,Place.a y]=0:=by exact not_not.1 (fun hv=> by have ht:= Coil.needy.mul (Coil.needy.var (ρ:=ø) (R:=ℝ) _) (cool x') _ hv; simp at ht)
    simp only [ht,hs,Finset.sum_const_zero,add_zero,sub_zero]; rfl
  change F.main _= _; rw [he,← Loft.Chart.nd_and _ _ F.toLuster.caseG.2]; rfl
abbrev ink1 (G: Gauge)(n:Side):= Flit G (Arm n)
abbrev ink0 (G:Gauge)(n:Side):= Flit G (Vtx n)

-- colon
abbrev dotC (G: Gauge){E B:Type*}: Matrix E B ℝ→Matrix (Flit G E) (Flit G B) ℝ:= chip G.ColorIndex -- Dec Eq infer; Fin.
abbrev energyB (n:Side):= dotC G (mono n)
abbrev rock (n:Side):= dotC G (bound n)
variable {P:Precision.ChartRatio G}(hp:Precision.LocalRatio P)
lemma normB : (waveLots (Rack G n P hp)).Z=energyB n:=by
  ext i j; rw [earmark, show ((Rack G n P hp).toLuster) = day G n from rfl,(front G n).2.2, Fintype.sum_prod_type]
  simp_rw [t_slab, real_inner_smul_left, real_inner_smul_right,orthonormal_iff_ite.mp (base G).orthonormal]; unfold energyB dotC chip; rw [← salute, Matrix.of_apply]; split_ifs with h
  · rw [Matrix.sum_apply]; simp_rw [Matrix.mul_apply]; rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=>?_ ; simp only [mul_one]; rfl
  simp
lemma normD : (waveLots (Rack G n P hp)).X=rock n:=by
  ext i j; change (deck n).chat j i []=_; rw [grid]; unfold rock dotC; change coefQ i.2 (slabQ j _-slabQ j i.1.1)= _; obtain ⟨a,x⟩:=i; obtain ⟨b,y⟩:=j; change coefQ x (slabQ (b,y) (a.1+step a.2)-slabQ (b,y) a.1)= ite (x=y) (bound n a b) 0; rw [pa, Inlay.slab,Inlay.slab]; rw [map_sub]; split_ifs <;> first| rfl| (simp_all only [coef_base, eq_comm (a:=y),↓reduceIte,map_zero,sub_zero])
end YM.MSBar.Cutis.Winter
