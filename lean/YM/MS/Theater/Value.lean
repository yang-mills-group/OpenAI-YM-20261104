import YM.MS.Theater.Grip
/-!
# Projection and image before color
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Theater
open Set Function Filter Finset Metric MeasureTheory Real Maxwell Labels
open Analysis Tensor Koszul Plane Landau Detect Detect.Mark Local.BV InnerProductSpace Submodule Momentum Local Woven
open Complex (I)
open scoped Topology ContDiff BigOperators RealInnerProductSpace
variable {G:Gauge}{h k n r:ℕ}{u x v:ℤ}{p q:Pol G}{F H:Law G}{f:Local.BV.Grade G}
local notation "KΩ"=> hands G
local notation "ζ"=> Koszul.mono
local infix:70 " ⋆ "=> product KΩ
abbrev LabelC (i:Key G):= (MvPolynomial.X ( R:=ℂ ) i)
def page (i:ℕ)(L:Witness G i): Pol G:= ∑ j,L ( axes G i j ) • LabelC ⟨i,j⟩
lemma bypage (L:Witness G h): At (page h L) ( h+2,1 ):= by unfold page; exact sum_mem fun i _=> smul_mem _ _ ( show LabelC (G:=G) ⟨h,i⟩∈charge G ( h+2,1 ) from MvPolynomial.isWeightedHomogeneous_X ℂ bidegree .. ) -- x term implicit maybe
lemma re_step (X: Labels.Taylor G h)(L:Witness G h): L X=∑ j,L ( axes G h j ) * pick ⟨h,j⟩ X:= by
    nth_rw 1 [ ← ( axes G h ).sum_repr X ]; simp_rw [map_sum,map_smul,Complex.real_smul]; exact Finset.sum_congr rfl fun i hi=> mul_comm ..
lemma bookX (L: Witness G h)(X:Labels.Jet G): Labels.read X ( page h L )=L ( X h ):= by
   unfold page; simp_rw [ map_sum,map_smul,LabelC,Labels.read, MvPolynomial.aeval_X ]; exact (re_step (X h) L).symm
lemma pageX (L: Witness G h): orbit G ( page h L ) = ζ (RowLeg G h L) := by
    let M: Witness G h→ₗ[ℂ] Law G:= ( ( place _ _ ).flip hit ).comp ( RowLeg G h ); have hm(f:Witness G h): M f= ζ ( RowLeg G h f ):= dawnB _
    let Z(f : Labels.Taylor G h): Witness G h →ₗ[ℂ] ℂ:= { toFun X:= X f, map_add' _ _:=rfl, map_smul' _ _:=rfl }; have he:L=∑ j,L ( axes G h j ) • pick (G:=G) ⟨h,j⟩:= by apply LinearMap.ext; intro x; change L x=Z x _; rw [ map_sum ]; exact re_step ..
    rw [ ← hm ]; conv_rhs=> rhs; rw [he]
    unfold page; simp_rw [map_sum,map_smul,LabelC,cusp,hm]; -- `pick` vs base lamp defeq
-- admissible kernel lift. Color-compatible extension needed later.
def above (i:ℕ): Module.End ℝ ( Labels.Taylor G i ):= let X:= gaugeJet ( G:=G ) ( j:= i ); X.comp X.leftInverse
lemma stem (h:ℕ)(i:Shell G h): above h ( gaugeJet i )= gaugeJet i:= by unfold above; change gaugeJet _=_; rw [LinearMap.leftInverse_apply_of_inj (LinearMap.ker_eq_bot.mpr leg_injective) i]
lemma nextθ (h:ℕ)(i:Labels.Taylor G h): ∃ t:Shell G h,above h i=gaugeJet t:=⟨ _,rfl⟩
lemma re_pose ( X:Pol G)(h:∀ U: Maxwell.TaylorTower G,Labels.read (fun i=> gaugeJet ( U i )) X=0): changed above X=0:= by apply Labels.eval_ext; intro A; let U: TaylorTower G := fun i=> gaugeJet.leftInverse ( A i ); rw [eval_changed]; exact ( h U ) |>.trans ( map_zero (Labels.read A) ).symm
lemma moved_v (V:(i:ℕ)→ Module.End ℝ (Labels.Taylor G i))(i:Key G): changed V (LabelC i)=page i.1 (( pick i).comp ( V i.1 )):= by apply Labels.eval_ext; intro A; rw [eval_changed, bookX]; unfold Labels.read LabelC; rw [MvPolynomial.aeval_X]; rfl
lemma still (V:(i:ℕ)→ Module.End ℝ (Labels.Taylor G i))(H:At p ( h,n )): At (changed V p) (h,n):= by
   apply MvPolynomial.IsWeightedHomogeneous.induction_on (motive:=fun (p:Pol G) _=> At ( changed V p ) ( h,n )) _ _ _ ((nodeId _ _).mp H); · rw [map_zero]; exact zero_mem _
   · intro x y hx hy hX hY; rw [ map_add ]; exact add_mem hX hY
   intro d r hr; rw [← hr]; exact pure_moved (fun i=>( i+2,1 )) V d r
private lemma monocL (he:Local.BV.Grade G): True:= trivial -- remove
lemma less (H:At p (h,n)): orbit G p - orbit G (changed above p)∈ PastSym G h n := by
    let P:= PastSym G; let D:= changed (G:=G) above; refine axisI (fun k p=> orbit G p - orbit G (D p)∈ P k.1 k.2) H (fun j=>?_) (fun j=>?_) ( fun u i f he hp=>?_ ) ( fun v f g hf hg hv hw=>?_ );
    · unfold D changed; simp
    · rw [map_zero, map_zero, map_zero,sub_zero]; exact zero_mem _
    · obtain ⟨i,j⟩:=i; let L:= pick (G:=G) ⟨i,j⟩; let K:= L.comp ( above i ); let u':= u.1; let h':= u.2; have hc:At f (u',h') := he; obtain ⟨H',hm⟩:= setting_K ( p:=changed above f ) ( still above hc ); have hL :( L-K ).comp gaugeJet=0:= by ext x; change L (gaugeJet x)-L ( above i ( gaugeJet x ) )=0; rw [stem,sub_self]
      obtain ⟨v,hv,hV⟩:= ( isoLeg ( L-K ) ).mp hL;
      rw [bags,cusp,map_mul,bags]; -- replace
      rw [ show D ( MvPolynomial.X _ )=page i K from moved_v above ⟨i,j⟩,pageX ]; let p:= RowLeg G i K; let q:= RowLeg G i L; let X:= ζ p ⋆ orbit G ( D f ); let k:= PastSym G ( ( ↑(bidegree (G:=G) ⟨i,j⟩).1:ℤ )+u' ) (h'+1); change _-_∈ PastSym G ( ↑( (bidegree (G:=G) ⟨i,j⟩).1+u.1 ) ) (1+u.2); rw [Nat.cast_add,add_comm 1]; change ζ q ⋆ orbit G f-X∈ k; have hr := tim_1 ( f:=q ) ( shadow_ω ( G:=G ) ⟨i,j⟩ ) hp; have ht:= time_q hv H' hm
      have hΔ : ζ ( Q v )=ζ q-ζ p := by rw [hV, map_sub ]; ext l; rcases l with _|⟨_,_|_⟩ <;> first| rfl| simp [mono]
      have hi: ζ ( Q v ) ⋆ orbit G ( D f )∈ k:= by unfold k bidegree generation; convert! ht using 1 -- see
      suffices heq: ζ q ⋆ orbit G f-X=ζ q ⋆ (orbit G f-orbit G ( D f ))+ζ ( Q v ) ⋆ orbit G ( D f ) by rw [heq]; exact add_mem hr hi
      unfold X; rw [map_sub, hΔ,map_sub,LinearMap.sub_apply ]; abel
    rw [map_add,map_add,map_add, add_sub_add_comm ]; exact add_mem hv hw
lemma onward (hp:At p (h,r)) : orbit G p∈PastSym G h r↔Maxwell.reduceEq p=0:= by
   constructor; · intro h; exact clocked hp (map_mono inf_le_left h)
   intro h; have he := less hp; rw [re_pose p (show ∀ X: TaylorTower G,Labels.read ( fun i=> gaugeJet ( X i ) ) p=0 from fun X=> by rw [ ← jet_value,h,map_zero ]), map_zero,sub_zero ] at he; exact he
end YM.MS.Theater
