import YM.OPE.Compatible.Tides.Alfa
/-!
# Local weighted extraction.Bloom permits multiplication. Sap uses no constant. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Balsam
open Function MeasureTheory Set Topology Metric Filter Lattice
open scoped BigOperators Classical ContDiff
variable {U:Gloam}{k j m:ℕ}{f g:ℕ→ℝ}{x y:ℝ}
def dye (i:ℕ):ℝ:=i+1
def booze (U:Gloam)(k:ℕ)(f:ℕ→ℝ):ℕ→ℝ:=fun i=>f i/(dye i * U.h i^k)
def Bose (U:Gloam)(k:ℕ)(f:ℕ→ℝ)(x:ℝ):Prop:= Tendsto (booze U k f) atTop (𝓝 x)
def Fruit (U:Gloam)(k:ℕ)(f:ℕ→ℝ)(x:ℝ):Prop:= ∃ a, Bose U k (f - billX U a k) x
lemma Bose.fuse (h:Bose U k f x)(he:Bose U k g y):Bose U k (f+g) (x+y):=by
   have hx:=h.add he -- Bose non reducible?
   unfold Bose booze; simpa only [Bose, booze, add_div,Pi.add_apply] using! hx
lemma Bose.pen (h:Bose U k f x)(ha:Bloom U j g y): Bose U (k+j) (f*g) (x*y):=by
    unfold Bose; rw [show booze U (k+j) (f*g)=booze U k f * (fun i=>(U.h i^j)⁻¹ * g i) from funext fun i=>by simp only [booze,Pi.mul_apply,div_eq_mul_inv,pow_add,mul_inv];ring]; exact (show Tendsto _ _ _ from Filter.Tendsto.mul h ha.2.2)
lemma notor : Tendsto dye atTop atTop:=tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
lemma booze_sake (hf:Sake U k f): Bose U k f 0:=by
    obtain ⟨C,hC,H⟩:=hf; apply tendsto_zero_iff_norm_tendsto_zero.mpr; have he:=tendsto_inv_atTop_zero.comp notor|>.const_mul C; rw [mul_zero] at he; apply squeeze_zero (fun i=> norm_nonneg _) _ he; intro i; unfold booze; rw [norm_div]; have hi:0<dye i:=by unfold dye; positivity
    have hx:=U.h_pos i; rw [Real.norm_of_nonneg (r:=dye i * U.h i^k) (by positivity), div_le_iff₀ (by positivity)]; exact (H i).trans (le_of_eq (by change C*_= C*(dye i)⁻¹*_; field_simp))
lemma Fruit.call (h:Bose U k f x):Fruit U k f x:=⟨0,by rw [show billX U (0:ℕ→ℝ) k=0 from funext fun j=>by simp [billX,coral],sub_zero]; exact h⟩
lemma Marble.sap (h:Marble U k f):Fruit U k f 0:=by obtain ⟨a,h⟩:=h; exact ⟨a,booze_sake h⟩
lemma Cleared.sap (h:Cleared U f):Fruit U k f 0:=by cases k with | zero=>exact Fruit.call (booze_sake h.cost) | succ k=> exact Marble.sap (h (k+1) (by omega))
lemma Fruit.sum (h: Fruit U k f x)(he:Fruit U k g y): Fruit U k (f+g) (x+y):=by
   obtain ⟨a,A⟩:=h; obtain ⟨b,B⟩:=he; refine ⟨a+b,?_⟩; rw [show (billX U (a+b) k)=(billX U a k)+(billX U b k) from funext fun j=>by simp only [billX, Pi.add_apply,coral,smul_add,Finset.sum_add_distrib],show f+g-(billX U a k+billX U b k)= (f-billX U a k)+(g-billX U b k) from by abel]; exact A.fuse B
lemma Fruit.pen (h:Fruit U k f x)(hp:Bloom U j g y): Fruit U (k+j) (f*g) (x*y):=by
    obtain ⟨a,A⟩:=h; rw [show f*g=(f-billX U a k)*g+billX U a k*g from by ring,← add_zero (x*y)]; exact (Fruit.call (A.pen hp)).sum (Cleared.sap ((Cleared.bill).pen hp.full))
lemma Fruit.line {E:Type*}(t:Finset E)(a:E→ℕ→ℝ)(b:E→ℝ)(h:∀ i∈t,Fruit U k (a i) (b i)):Fruit U k (∑ i∈t,a i) (∑ i∈t,b i):=by
   induction t using Finset.induction_on with
   | empty=> rw [Finset.sum_empty,Finset.sum_empty]; exact (cleared_zero U).sap
   | insert e t he ih=> rw [Finset.sum_insert he,Finset.sum_insert he]; exact (h _ (Finset.mem_insert_self ..)).sum (ih (fun _ hp=> h _ (Finset.mem_insert_of_mem hp)))
end YM.OPE.Balsam
