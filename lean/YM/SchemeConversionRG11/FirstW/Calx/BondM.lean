import YM.SchemeConversionRG11.FirstW.Calx.Wash
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW
open Function MeasureTheory Filter Set Metric Topology Lattice Pert Align Laurent Position SchemeConversionRG11 SchemeConversionRG11.Horizon Deck MvPolynomial
open scoped BigOperators Classical ContDiff
variable {G:Gauge} {F:Labels.Frames G} {T:Itinerary} {n:Side} {p:E F 6}
-- ambient before limiting to jets, asym totals
abbrev Weather (G:Gauge) := Field4 G→ₗ[ℝ] Field4 G→ₗ[ℝ]ℂ -- not an axiom
abbrev saleF (T:Itinerary)(m:ℕ)(Q:Wash)(p:E F 6): Weather G:= burn (tin G (T.period m)) 1 0 (wheelS G T m Q) (cloak F p)
def dew (T:Itinerary)(m:ℕ)(Q:Wash)(p:E F 6): Weather G:= (2:ℂ)⁻¹ • (saleF T m Q p + (saleF T m Q p).flip)
lemma dew_val (T:Itinerary)(m:ℕ)(Q:Wash)(p:E F 6) (A B:Field4 G): dew T m Q p A B=(2:ℂ)⁻¹*(saleF T m Q p A B+saleF T m Q p B A):=rfl
lemma dew_plus (T:Itinerary)(m:ℕ)(Q:Wash)(p r:E F 6): dew T m Q (p+r)=dew T m Q p+dew T m Q r:=LinearMap.ext (fun x=>LinearMap.ext (fun y=>by simp only [LinearMap.add_apply,dew_val,saleF,burn_eq,root3,D1, ←robes_eq,map_add,coeff_add,add_mul,Finset.sum_add_distrib]; ring))
lemma dew_smul (T:Itinerary)(m:ℕ)(Q:Wash)(p:E F 6)(c:ℂ): dew T m Q (c • p)=c • dew T m Q p := by
 apply LinearMap.ext; intro A; apply LinearMap.ext; intro B
 simp only [LinearMap.smul_apply,dew_val,saleF,burn_eq,root3,D1,←robes_eq,map_smul,Derivation.map_smul, coeff_smul, smul_eq_mul, mul_assoc]; simp_rw [←Finset.mul_sum]; ring
lemma dove_color (p:E F 6)(T:Itinerary)(r:ℕ)(Q:Wash)(u:G.El)(A B:Field4 G): saleF T r Q p (putting u A) (putting u B)=saleF T r Q p A B := by
 have hc : ∀ A B C,wheelS G T r Q (putting u A) (putting u B) (putting u C)=wheelS G T r Q A B C := by intro A B C; simp only [wash_eq,tower_key]
 exact Eq.symm (tint_burn _ _ _ _ _ _ _ _ (tint_pl 6 u 0 1) (fun x=>(tint F u x p).symm) (fun a=> tone_tin u a _) hc A B)
lemma dove_pull (p:E F 6)(T:Itinerary)(r:ℕ)(Q:Wash)(s:Signed)(A B:Field4 G): saleF T r Q (tripS F s p) A B=saleF T r Q p (Bare.wideLink G s A) (Bare.wideLink G s B) :=
 tint_burn _ _ _ _ _ _ _ _ (spin_pl G 6 s 1) (fun x=> cirrus F s x p) (fun a=>spin_tin s a _) (wash_spin G T s r Q) A B -- maybe diamond
lemma dew_bar (T:Itinerary)(m:ℕ)(Q:Wash)(p:E F 6) (x y:Field4 G): star (dew T m Q p x y) = dew T m Q (bar F 6 p) x y := by
 have he (x y:Field4 G): star (saleF T m Q p x y)=saleF T m Q ((Maxwell.freeTable F).conj (Extra.FD.table_spin F) 6 p) x y:=by simp [saleF,burn_eq,barcloak,root_map_bar]
 rw [dew_val,dew_val] -- star_mul first
 simp [he]
private def reelW (F:Labels.Frames G)(T:Itinerary)(v:ℕ)(Q:Wash): Letter G F where
 toFun p:= ((dew T v Q p).comp (cabin G 4).subtype).compl₂ (cabin G 4).subtype
 map_add' p q:=LinearMap.ext (fun x=>LinearMap.ext (fun y=>by simp [dew_plus]))
 map_smul' r p:= LinearMap.ext (fun x=>LinearMap.ext (fun y=>by simp [dew_smul]))
private lemma bondsE (p:E F 6)(T:Itinerary)(m:ℕ)(Q:Wash)(v w:la G): reelW F T m Q p v w=dew T m Q p v.val w.val:=rfl
def bondM (F:Labels.Frames G)(T:Itinerary)(m:ℕ)(Q:Wash): Bond F:= ⟨reelW F T m Q, by
 refine ⟨fun p hp=>?_,fun p x y=>?_,fun u p x y=>?_,fun p x y=>?_,fun s p x y=>?_⟩
 · apply LinearMap.ext; intro x; apply LinearMap.ext; intro y
   have ht (a b c:Who G 6): root3 (cloak F p) a b c=0 := tangI F a b c p 5 (by decide) hp
   rw [bondsE,dew_val]; simp [saleF,burn_eq,ht]
 · rw [bondsE,bondsE,dew_val,dew_val,add_comm]
 · rw [bondsE,bondsE,dew_val,dew_val]; simp only [ColorS,dove_color]
 · rw [bondsE,bondsE,dew_bar]
 rw [bondsE,bondsE,dew_val,dew_val,dove_pull,dove_pull]; simp only [rink,rex]
 ⟩
lemma bond_paid (T:Itinerary)(m:ℕ)(Q:Wash)(p:E F 6)(x y:la G): (bondM F T m Q).val p x y=dew T m Q p x.val y.val:=rfl
end YM.RG11.FirstW
