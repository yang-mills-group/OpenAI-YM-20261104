import YM.OPE.Compatible.Slope.Slip
/-!
# Tsum polynomial under affine modulation. Need exact case order zero -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Lattice Laurent Filter MeasureTheory RG Finset Next.Free Precision Planned.PrimaryIntegral295 Planned.PrimaryIntegral295.Carrier
open scoped Topology BigOperators Classical
variable {I:Type*}[Fintype I]{L:Side}
-- weight momentum bank
omit [Fintype I] in
private lemma poly_affine (p:I→ℝ) (i:I) : (fun x:Lieu I=> (p+x) i) ∈ Flavor I 1:=by change ((fun _=> p i)+(fun x:Lieu I=>x i))∈ _; exact (Flavor I 1).add_mem (flavor_cast _ _) (flavor_position i)
abbrev Alive (u:Shift I→ℝ):Prop:=∀ m:ℕ,∃ c,Sack (poise m) u c
private lemma shade {u:Shift I→ℝ}(H:Alive u)(p:I→ℝ)(l:List I): Summable fun x=> u x*tasting l (p+translit x):=by
    obtain ⟨c,h⟩:=H l.length; let f (x:Lieu I):=p+x; have hh:= flavor_diagonal f (poly_affine p) (flavor_part l l.length le_rfl); change Summable fun x=>u x*((tasting l) ∘ f) (translit x); exact gardens hh h
private lemma massLife {u:Shift I→ℝ}(H:Alive u)(p:I→ℝ)(a:I) : Alive fun x:Shift I=> u x * (p+translit x) a:=by
    intro m; obtain ⟨c,h⟩:= H (m+1); obtain ⟨z,hz,hP⟩:= tasting_cost (poly_affine p a); let V i:=poise (m+1) i*‖u i‖
    have hs:SumBudget (fun i=> z* V i) (z*c):=⟨fun i=>mul_nonneg hz (h.1 _), h.2.1.mul_left _, by rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left h.2.2 hz⟩
    refine ⟨z*c,Work.F08.budget_minor hs ?_ ?_⟩
    · exact fun i=> mul_nonneg (zero_le_one.trans (poise_one m i)) (norm_nonneg _)
    intro i; change poise m i * ‖u i* _‖ ≤ _; rw [norm_mul]; unfold V
    apply le_trans (b:=poise m i*(‖u i‖*(z*poise 1 i)))
    · have hp :0 ≤ poise m i:=zero_le_one.trans (poise_one m i); exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hP i) (norm_nonneg _)) hp
    exact le_of_eq (by unfold poise; ring)
/-- characteristic polynomial (Wick-read shift). -/
def lineValue (u:Shift I→ℝ) (l:List I) (k:ℝ) (p: Lieu I)(x:Lieu I):= ∑' y,u y*tasting l (k • x+(p+translit y))
lemma tame (u:Shift I→ℝ)(l:List I)(k:ℝ)(p:Lieu I)(H:Alive u):
  ∃ q:Lieu I→ℝ, q∈Flavor I (l.length-1) ∧ (l=[]→q=0) ∧ ∀ x, lineValue u l k p x=(k^l.length)*(∑' i,u i)*tasting l x+q x := by
    induction l generalizing u with
    | nil=>exact ⟨0,(Flavor _ _).zero_mem,fun _=>rfl,fun x=>by simp [tasting,lineValue]⟩
    | cons i l ih=>
       let v(y:Shift I):=u y*(p+translit y) i
       obtain ⟨g,hg,hm,h⟩:= ih u H; obtain ⟨f,hf,hf',h'⟩:= ih v (massLife H p i)
       have ht(x): Summable fun y=> u y*tasting l (k • x+(p+translit y)):=by simp_rw [← add_assoc]; exact shade H (k • x+p) _
       have hv(x): Summable fun y=> v y*tasting l (k • x+(p+translit y)):=by simp_rw [← add_assoc]; exact shade (massLife H p i) _ _
       let y:=fun x:Lieu I=> x i; let z:= fun x:Lieu I=>k*y x*g x+(k^l.length*(∑' i,v i)*tasting l x+f x)
       refine ⟨z,?_,by simp,fun x=>?_⟩
       · simp only [List.length_cons, Nat.add_sub_cancel]
         let V:= Flavor I l.length
         have hA : (k • y)*g∈ V:=by
            by_cases he:l=[]; rw [hm he,mul_zero]; exact V.zero_mem
            have hx: 1+(l.length-1)=l.length:=by cases l<;> simp_all [add_comm]
            exact flavor_up hx.le (flavor_prod ((Flavor _ _).smul_mem k (flavor_position i)) hg)
         exact V.add_mem hA (V.add_mem (V.smul_mem (k^l.length*(∑' i,v i)) (flavor_part l l.length le_rfl)) (flavor_up (by omega) hf))
       unfold lineValue; rw [show (fun m:Shift I=> u m*tasting (i::l) (k • x+(p+translit m)))=(fun m=> k*(y x)*(u m*tasting l (k • x+(p+translit m)))+ v m*tasting l (k • x+(p+translit m))) from ?_,Summable.tsum_add ((ht x).mul_left _) (hv x),tsum_mul_left]; swap
       · funext m; unfold v y; change u m*((k*x i+(p+translit m) i)*tasting l _) = _; ring
       change k*y x * lineValue u l k p x+lineValue v l k p x=_; rw [h,h']; unfold z y; rw [List.length_cons]; change _= _* (x i * tasting l x)+_; ring
end YM.OPE.Flume
