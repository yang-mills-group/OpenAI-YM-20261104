import YM.SchemeConversionRG11.FirstW.Trice.Ham
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW
open Function Filter Set MeasureTheory Metric Lattice Pert Align Position Topology Maxwell Pert.Triangle Tensor Analysis Deck SchemeConversionRG11.FirstMS
open scoped Topology BigOperators Classical
variable {T:Itinerary}{c:ℕ→Side} {G:Gauge}{E W F:Type*}[NormedAddCommGroup E][NormedAddCommGroup F][NormedAddCommGroup W]{A B: Sight T G}{S:Set E4}
variable {f p: Hall T E}{P:E4→E} {q:Hall T W}{R:ℝ}{u v w:E4}
def Camper (T:Itinerary)(r:ℝ)(k:ℕ)(p:Hall T E):= ∃ C>0,∀ᶠ i in atTop,∀ x:Site (T.period i), out T i x∈Town r → Gulf T i x ^ k*‖p i x‖ ≤ C
variable {a b:ℕ} {r:ℝ} {Q:Wash}
lemma camp_save (h:SaveB T a f): Camper T R a f := by obtain ⟨C,H,B⟩:=h; exact ⟨C,H,B.mono fun _ hi x _=> hi x⟩
lemma campers (h:Meets T S f P) (he:Town R ⊆ S): Camper T R 0 f:= by obtain ⟨C,hC,H⟩:=h.rent (isCompact_closedBall _ _) he; refine ⟨C,hC,H.mono fun i hi x hx=>?_⟩; simpa using hi x hx
lemma campers_sum (h:Camper T R a f)(p':Camper T R a p): Camper T R a (f+p):=by obtain ⟨C,hC,H⟩:=h; obtain ⟨D,hD,Y⟩:=p'; refine ⟨C+D,by positivity,(H.and Y).mono fun i hi x hx=>?_⟩; have ht:=gulf_pos T i x; refine le_trans (mul_le_mul_of_nonneg_left (norm_add_le ..) (by positivity)) ?_; rw [mul_add]; exact add_le_add (hi.1 x hx) (hi.2 x hx)
lemma campers_nil {k:ℕ}: Camper T R k (0:Hall T E):=⟨1,one_pos,Eventually.of_forall fun i x _=>by simp⟩ -- k unknown
lemma campers_smul [NormedSpace ℝ E](h:Camper T R a f)(r:ℝ): Camper T R a (r • f):=by
 obtain ⟨C,hC,H⟩:=h; refine ⟨‖r‖*C+1,by positivity,H.mono fun i hi x hx=>?_⟩; simp only [Pi.smul_apply,norm_smul]; rw [mul_left_comm]; exact (mul_le_mul_of_nonneg_left (hi x hx) (norm_nonneg _)).trans (le_add_of_nonneg_right zero_le_one)
lemma campers_prod [NormedSpace ℝ E][NormedSpace ℝ F][NormedSpace ℝ W](h:Camper T R a f)(hp:Camper T R b q)(L:E→L[ℝ] W→L[ℝ] F): Camper T R (a+b) (fun i x=> L (f i x) (q i x)):=by
 obtain ⟨C,hC,H⟩:=h; obtain ⟨D,hD,Y⟩:=hp
 refine ⟨‖L‖*(C*D)+1,by positivity,(H.and Y).mono fun i hi x hx=>?_⟩; let t:=Gulf T i x; have ht:0<t:=gulf_pos ..
 calc t^(a+b)*_ ≤ t^(a+b) * (‖L‖*‖f i x‖*‖q i x‖):= mul_le_mul_of_nonneg_left ((ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right (L.le_opNorm _) (norm_nonneg _))) (by positivity)
      _ = ‖L‖*((t^a*‖f i x‖)*(t^b*‖q i x‖)) := by rw [pow_add]; ring
      _ ≤ _ := (mul_le_mul_of_nonneg_left (mul_le_mul (hi.1 x hx) (hi.2 x hx) (by positivity) hC.le) (norm_nonneg L)).trans (le_add_of_nonneg_right zero_le_one)
lemma Pleased.camps {Z:Type}[NormedAddCommGroup Z][NormedSpace ℝ Z]{u:Hall T Z}(h:Pleased T S u)(hz:Town R⊆ S): Camper T R 0 u:= by obtain ⟨Y,H⟩:=h; exact campers H.identity hz
-- spire with one singular leg
lemma seat_camp (h:CrestS T 0 3 A)(hp:HatP T S B)(w:Walk)(x:Cover)(he:Town R ⊆ S): let X (A B:Sight T G): Hall T G.Color:=fun i y=>swerve y w (A i) (B i); Camper T R 3 (mailR T (X A B) x) ∧ Camper T R 3 (mailR T (X B A) x):= by
 induction w generalizing x with
 | nil=> exact ⟨campers_nil,campers_nil⟩
 | cons i w ih=>
    intro X; let u:= i.vec (R:=ℤ)
    let k(v:Sight T G) := mailR T (peakC T v i) x; let C (v:Sight T G):= mailR T (fun i p=> rail p w (v i)) (x+u); let D(X Y:Sight T G):=mailR T (fun i p=> swerve p w (X i) (Y i)) (x+u)
    obtain ⟨L,H⟩:=doubles G.ad
    have hx(v p): mailR T (X v p) x=(fun (s:ℕ)(x:Site (T.period s))=>L (k v s x) (C p s x))+D v p:= funext fun j=>funext fun y=>by simp only [H,X,k,C,D,u,mailR,peakC,Pi.add_apply,swerve_eq,map_add, wrap_vec,add_assoc]
    rw [hx,hx]; exact ⟨campers_sum (campers_prod (camp_save (save_0 ((crest_leg h i).shift _))) (((walkP hp w).by _).camps he) L) (ih (x+u)).1,campers_sum (campers_prod (camp_save (save_0 ((crest_loop h w).shift _))) (((hp.leg i).by _).camps he) L.flip) (ih (x+u)).2⟩
lemma spire_camp (h:CrestS T 0 3 A)(hp:HatP T S B)(i j:Axis)(he:Town R ⊆ S) : Camper T R 3 (claw T A B i j):= by
 let X:=square i j; obtain ⟨hZ,hV⟩:= seat_camp h hp X 0 he
 have he(A:Hall T G.Color): mailR T A 0=A:=funext fun i=>funext fun x=>by simp [mailR]
 rw [he] at hZ hV; unfold claw; simp only [spire,LinearMap.smul_apply, LinearMap.add_apply,LinearMap.flip_apply]; exact campers_smul (campers_sum hZ hV) _
def MinusUnit (T:Itinerary)(f:Hall T ℝ)(i:ℕ):=T.gap i^4 * ∑ x,f i x
-- Unit Market relation (Lebesgue)
def Market (T:Itinerary)(P:Hall T ℝ)(V:E4→ℝ):= Integrable V ∧ Tendsto (MinusUnit T P) atTop (𝓝 (∫ x,V x))
lemma holdsLocal {P:Hall T ℝ}{F:E4→ℝ}(h:Camper T R 3 P)(hp:Placed T R P)(e:S∈ae (volume:Measure E4))(hc:MarkGrid T c)(V:Meets T S P F): Market T P F:=by
 obtain ⟨C,hC,H⟩:=h; have h : ∀ᵐ v∂volume,v∈S:=e
 apply sum_local hc hC.le (R:=R+1) _ (h.mono fun v hv s hs=> V id tendsto_id v hv s hs)
 filter_upwards [H,hp,T.cutoff.eventually (gt_mem_nhds (by norm_num:(0:ℝ)<1))] with i hi ht he x
 refine ⟨fun hx=> (limb (show Jam T R i (lift x) from ht x hx)).trans (by linarith only [he]), ?_⟩ -- implicit
 by_cases hx:P i x=0; · simp [hx,hC.le]
 exact hi x ((Metric.mem_closedBall ..).mpr (by simpa using ht x hx))
lemma Market.move {V:E4→ℝ} {P:Hall T ℝ}(s:StepPath T)(h: Market T (slipU T s P) (fun x=>V (x+v))) : Market T P V:= by
 obtain ⟨X,H⟩:=h; refine ⟨?_,?_⟩
 · simpa only [sub_add_cancel] using X.comp_sub_right v
 rw [integral_add_right_eq_self V] at H; exact H.congr (fun i=> by unfold MinusUnit; apply congrArg _; exact Equiv.sum_comp (Equiv.addRight (s i)) _)
lemma Market.plus {P Q:Hall T ℝ}{F W:E4→ℝ}(h: Market T P F)(hp:Market T Q W): Market T (P+Q) (F+W):=by
 refine ⟨h.1.add hp.1,?_⟩; rw [show (∫ x,(F+W) x)=_ from integral_add h.1 hp.1]; apply (h.2.add hp.2).congr; intro i; simp only [MinusUnit,Pi.add_apply,Finset.sum_add_distrib,mul_add]
end YM.RG11.FirstW
