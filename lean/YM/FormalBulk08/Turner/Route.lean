import YM.FormalBulk08.Orb.Swans
set_option autoImplicit false
noncomputable section
namespace YM.FormalBulk08.Turner
open Series Jets Wick Orb Matrix Filter Set Function PowerSeries
open scoped Topology BigOperators Classical
variable {V I J K S R: Type*}[Fintype I][DecidableEq I][Fintype V][DecidableEq V]
section common
variable [CommRing R]
def door (e:I≃V)(T: Saddle R V): Saddle R I:= ⟨T.q.submatrix e e,T.P.submatrix e e,fun i j=>T.ok _ _,fun i j=>T.valid _ _,by rw [submatrix_mul_equiv,T.inv, Matrix.submatrix_one_equiv]⟩
lemma bases (e:I≃V) [Algebra ℚ R] (T:Saddle R V) : (MvPolynomial.rename e.symm) T.base=(door e T).base := by
   unfold Saddle.base; simp_rw [map_neg,map_sum,map_mul,MvPolynomial.rename_C,MvPolynomial.rename_X]; apply congr_arg Neg.neg; symm; exact Fintype.sum_equiv e _ _ fun i=> Fintype.sum_equiv e _ _ fun j=> by simp [door]
lemma measures (e:I≃V)[Algebra ℚ R](T:Saddle R V)(p:Glyphs R V): (door e T).call (MvPolynomial.rename e.symm p)=T.call p:= by
    apply LinearMap.congr_fun (f:=((door e T).call).comp (MvPolynomial.rename e.symm).toLinearMap) (g:=T.call) (?_) p
    apply moment_unique T.q T.ok
    · simp [Saddle.call]
    intro p i
    simp [Saddle.call, paired (door e T).q (door e T).ok];symm; exact Fintype.sum_equiv e.symm _ _ fun j=> by simp [door,MvPolynomial.pderiv_rename e.symm.injective]
end common
variable (e: I≃V)
def porch (H:Hull V K): Hull I K:= ⟨door e H.saddle,H.main,H.drift ∘ e⟩
def tunnelP {V I:Type*}[CommRing S](f:V→I): Plate S V →+* Plate S I:=PowerSeries.map (MvPolynomial.rename f).toRingHom
@[simp] lemma tunnelP_C (f : K→J) [CommRing S](p:Glyphs S K): tunnelP f (C p)=C (MvPolynomial.rename f p) := by simp [tunnelP]
omit [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V] in
lemma tunnelP_boost (p: Pap J): tunnelP e.symm (boost V p)=boost I p:= by ext1 n; simp_rw [tunnelP,boost,coeff_map];simp
abbrev abroad := tunnelP (S:=ℝ) (Sum.elim (Sum.inl ∘ e.symm) (Sum.inr (α:=I) (β:=K))) -- plate activation
lemma ink_cover (H: Hull V K) (p:Pap (V⊕K)): toInk (porch e H) (abroad e p) = tunnelP e.symm (toInk H p) := by
    unfold toInk roam abroad tunnelP; rw [change_after,change_beam]; suffices hz:(insertAt ℝ (fueled (porch e H))).comp ((MvPolynomial.rename (Sum.elim (Sum.inl ∘ e.symm) (Sum.inr (α:=I) (β:=K)))).toRingHom)=(tunnelP e.symm).comp (insertAt ℝ (fueled H)) by rw [hz]; rfl
    ext
    case hC c n m a=> simp [tunnelP]
    case hX i n m a=> cases i with
      | inl i=>simp [fueled, porch,boost,tunnelP]
      | inr i=>simp [fueled, boost,tunnelP]
lemma door_base (T:Saddle ℝ V) : door e (variation T K)= variation (door e T) K:=rfl
lemma packed (H:Hull V K)(p:Pap (V⊕K))(h:Solved H p): Solved (porch e H) (abroad e p):= by
   unfold Solved at *; rw [ink_cover,tunnelP,coeff_map,h,map_add];change MvPolynomial.rename _ _+MvPolynomial.rename _ _=_+_;rw [bases,MvPolynomial.rename_C];rfl
lemma mappedP (H:Hull V K)(p:Pap (V⊕K)):positive (porch e H) (abroad e p)= tunnelP e.symm (positive H p):= by
   unfold positive; rw [ink_cover,map_sub,map_sub,tunnelP_C,tunnelP_boost,bases];rfl
lemma minted (T:Saddle ℝ V)(p : Ink V K): beam (variation (door e T) K).call (tunnelP e.symm p) = beam (variation T K).call p:= by
   ext1 n; rw [coeff_beam,tunnelP,coeff_map, coeff_beam]; exact measures e (variation T K) (coeff n p)
lemma pounds (H:Hull V K)(p:Pap (V⊕K))(hp:Solved H p): vocal (porch e H) (abroad e p)= vocal H p := by unfold vocal; rw [mappedP, show expan (tunnelP e.symm _)= tunnelP e.symm (expan _) from (map_expan _ (plur H p hp)).symm]; exact minted ..
lemma posed (H:Hull V K)(p:Pap (V⊕K))(hp:Solved H p)(U:Pap (V⊕K)): flag (porch e H) (abroad e p) (abroad e U)= flag H p U:= by
   unfold flag; rw [pounds _ _ _ hp,mappedP, show expan (tunnelP e.symm _)= tunnelP e.symm (expan _) from (map_expan _ (plur H p hp)).symm, ink_cover, ←map_mul, show (porch e H).saddle=_ from rfl]; congr 1; exact minted ..
end YM.FormalBulk08.Turner
