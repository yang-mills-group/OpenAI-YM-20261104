import YM.FormalBulk08.City.Table

/-! Pattern variation reduction to finite link stencils multiplied to the single
real mark shaft. No e-jet Ward premise on physical numbers. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.City
open Reef Lava Lattice Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 PowerSeries
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G : Gauge} {n : Side} (i : hue G) (v : wire G n)

abbrev shortL (V : Type) [Fintype V] : Pap (dah V)→+*Pap V := roam ℝ (motor (boxL V))
def curly (V : Type) := shaft (MvPolynomial.pderiv (R:=ℝ) (.inr () : dah V))
lemma on_shaft (l: Bool) (b) : shortL (hue G) (curly _ (motor (curtain i l) b)) = paste (will i l b) := by
    unfold shortL curly; rw [motor_diff _ (curtain_home ..) ((curtain_diff i l).of_le le_top),←paste_steps _ (boxL (hue G)) ?smooth (boxL (hue G)).contDiff.contDiffAt (map_zero _)]
    rfl
    case smooth => exact ContDiffAt.clm_apply (f:=fderiv ℝ (fun x=>curtain i l x b)) (g:=fun _ => dotI (.inr ())) ((coord_diff _ ((curtain_diff i l).of_le le_top) b).fderiv_right (by norm_num)) contDiffAt_const
lemma on_lead (l: Bool) (b) : shortL (hue G) (motor (curtain i l) b)=C (MvPolynomial.X b) := by
    unfold shortL; rw [motor_compose _ _ ((curtain_diff i l).of_le le_top) (boxL (hue G)).contDiff.contDiffAt (curtain_home ..) (map_zero _)]; rw [show C (MvPolynomial.X b)=motor (fun z:Rays (hue G)=> z ∘ id) b from (motor_wires id b).symm]
    unfold motor; apply congr_arg (fun p=>afterX p 1); apply paste_replace; filter_upwards [lit_curtain i l] with z hz; exact congr_fun hz _
set_option maxHeartbeats 500000 in
lemma on_part (Z : Pap (dah (hue G))) : shortL (wire G n) (PowerSeries.map (MvPolynomial.rename (localCoord v)).toRingHom Z)=PowerSeries.map (MvPolynomial.rename (rowD v)).toRingHom (shortL (hue G) Z) := by
    unfold shortL; rw [←fit_translate, ←fit_translate,roam_compose,roam_compose]; refine congr_arg (fun x => roam ℝ x Z) ?_; funext b
    rw [motor_compose _ _ (localCoord_cap v _) (boxL (wire G n)).contDiff.contDiffAt rfl (map_zero _)]
    let f:=fun z:Rays (wire G n)=> z ∘ rowD v
    have he : ContDiffAt ℝ ∞ f 0:=contDiffAt_pi.mpr fun _=>contDiffAt_apply ..
    rw [motor_compose _ f (boxL (hue G)).contDiff.contDiffAt he (map_zero _) rfl];refine congr_arg (fun x=> motor x b) ?_; ext1 p; funext j; cases j <;> rfl
lemma curly_turn (Z : Pap (dah (hue G))) : curly _ (PowerSeries.map (MvPolynomial.rename (localCoord v)).toRingHom Z) = PowerSeries.map (MvPolynomial.rename (localCoord v)).toRingHom (curly _ Z) := by
    have he:Injective (localCoord v) := Sum.map_injective.mpr ⟨fun a b h=>congr_arg (Prod.snd ∘ Prod.snd) h, Function.injective_id⟩
    ext1 i; rw [curly, coeff_shaft, coeff_map,curly,coeff_map,coeff_shaft]
    exact MvPolynomial.pderiv_rename he (.inr ()) _

variable (x : Site n)
lemma turning (l : Bool) (h : ∀ z, deltaS i x z v=curtain i l (z ∘ localCoord v) v.2.2) : motor (deltaS i x) v=PowerSeries.map (MvPolynomial.rename (localCoord v)).toRingHom (motor (curtain i l) v.2.2) := by
   rw [←fit_translate, motor_compose _ _ ((curtain_diff i l).of_le le_top) (localCoord_cap v _) (curtain_home ..) rfl]; unfold motor; rw [funext h]; rfl
def originP (l : Bool):=paste (will i l v.2.2)
def spinP (l : Bool) := PowerSeries.map (MvPolynomial.rename (rowD v)).toRingHom (originP i v l)
lemma dating (l : Bool) (h : ∀ z, deltaS i x z v=curtain i l (z ∘ localCoord v) v.2.2) : shortL _ (motor (deltaS i x) v)=C (MvPolynomial.X v) ∧ shortL _ (curly _ (motor (deltaS i x) v))=spinP i v l := by
   rw [turning i v x l h,curly_turn,on_part,on_part,on_shaft,on_lead]; refine ⟨?_,rfl⟩; simp [rowD]
lemma sometimes (h : ∀ z,deltaS i x z v=z (.inl v)) : motor (deltaS i x) v = motor (cheekL (wire G n)) v := by unfold motor; rw [funext h];rfl
lemma drying (h : ∀ a,step a≠(0:Site n)) : shortL _ (motor (deltaS i x) v)=C (MvPolynomial.X v) ∧
   shortL _ (curly _ (motor (deltaS i x) v))=(if v.1=x then spinP i v true else 0)+(if v.1+step (axisEquiv.symm v.2.1)=x then spinP i v false else 0) := by
   by_cases he:v.1=x
   · have hz : ¬v.1+step (axisEquiv.symm v.2.1)=x:= fun e=>h _ (add_left_cancel ((e.trans he.symm).trans (add_zero _).symm))
     rw [if_pos he,if_neg hz,add_zero]; exact dating i v x true fun _=> if_pos he
   by_cases hh:v.1+step (axisEquiv.symm v.2.1)=x
   · rw [if_neg he,if_pos hh,zero_add]; exact dating i v x false fun _=>by simp [deltaS,he,hh]
   rw [if_neg he,if_neg hh,add_zero,sometimes i v x (by simp [deltaS,he,hh])]; constructor
   · unfold shortL;rw [motor_compose _ _ (cheekL (wire G n)).contDiff.contDiffAt (boxL (wire G n)).contDiff.contDiffAt (map_zero _) (map_zero _)]; exact motor_wires id _
   rw [show motor (cheekL (wire G n)) v=_ from motor_wires (Sum.inl : wire G n→dah (wire G n)) v, curly, shaft_C]; simp

def yaw {m : Type} (v : m×TypeFace 1× hue G) := shaft (MvPolynomial.pderiv (R:=ℝ) v)
lemma shedder (p:Pap (wire G n)) (h : Rite p p 1 0) (hp : ∀ v,step v≠(0:Site n)) : ∑ v : wire G n,yaw v p*((if v.1=x then spinP i v true else 0)+(if v.1+step (axisEquiv.symm v.2.1)=x then spinP i v false else 0))=0 := by
   have he : curly _ (roam ℝ (motor (deltaS i x)) p)=0 := by
      rw [frontTable i x p h hp]; ext1 j; rw [curly,coeff_shaft,map_zero,coeff_map]; generalize coeff j p=U;change MvPolynomial.pderiv (R:=ℝ) (.inr () : dah (wire G n)) (MvPolynomial.rename Sum.inl U)=0
      induction U using MvPolynomial.induction_on <;> simp_all
   have hh := congr_arg (shortL (wire G n)) he
   rw [map_zero] at hh;refine Eq.trans ?_ hh
   unfold curly roam;rw [diff_chain,map_sum]; apply Finset.sum_congr rfl; intro a _; rw [map_mul]
   obtain ⟨h₁,h₂⟩:=drying i a x hp; rw [←h₂]; congr 1
   change _ = roam ℝ _ (roam ℝ _ (yaw a p))
   rw [roam_compose,show (fun v=>shortL _ (motor (deltaS i x) v))=_ from funext (fun b=> (drying i b x hp).1),virgin]
end YM.FormalBulk08.City
