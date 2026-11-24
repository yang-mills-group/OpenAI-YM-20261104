import YM.SchemeConversionRG11.FirstW.Fade.Draft
import YM.SchemeConversionRG11.FirstW.Calx.Wash
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW
open Function Filter MeasureTheory Set Metric Topology Lattice Pert Align
open scoped Topology BigOperators Classical
variable {T:Itinerary}{V E F:Type} [NormedAddCommGroup V][NormedSpace ℝ V][NormedAddCommGroup E][NormedSpace ℝ E] [NormedAddCommGroup F][NormedSpace ℝ F]{G:Gauge}
variable {A B: Sight T G}{f g: Hall T E} {q:Hall T V} {R:ℝ} {S:Set E4}{c:ℕ→Side}
def peakC (T:Itinerary) (A: Sight T G)(s:Step): Hall T G.Color:= fun j x=> boardAt x s (A j)
def rushC (T:Itinerary)(A:Sight T G)(i j:Step): Hall T G.Color:= fun s x=> (T.gap s)⁻¹ • rail x (icon i j) (A s)
def slipC (T:Itinerary)(p:Hall T E)(s:Step): Hall T E:= fun i x=> (T.gap i)⁻¹ • (p i (x+s.vec)-p i x)
lemma signed_ray (s:Step)(f:Hall T E): slipC T f s= flareL s • mailR T (ray s.dir f) (torMark s) := by
 rcases s with ⟨s,b|b⟩ <;> funext i x <;> simp [slipC,Step.vec,ray,surface,combine,mailR,torMark,up,smul_sub,flareL]
 abel
lemma icon_price (A:Sight T G)(i j:Step) : rushC T A i j = slipC T (peakC T A j) i-slipC T (peakC T A i) j := funext fun k=>funext fun x=>by simp only [rushC,close_read,smul_sub,peakC,slipC,Pi.sub_apply]
abbrev stalkH (T:Itinerary)(A:Sight T G)(s:Axis):Hall T G.Color:= fun i x=> A i (x,s)
omit [NormedAddCommGroup V] [NormedSpace ℝ V] in
lemma mail_vec (s:Step)(f:Hall T V): mailR T f s.vec=fun i x=>f i (x+s.vec):=funext fun i=> funext fun x=> by simp [mailR,wrap_vec]
lemma lookC (A:Sight T G)(s:Step): peakC T A s=flareL s • mailR T (stalkH T A s.dir) (torMark s) := by
 funext i x; rw [peakC,board_spin]; congr 2; simp [torMark,apply_ite]
def CalmS (T:Itinerary)(A:Sight T G):= ∀ i:Axis,Dusk T (stalkH T A i)
lemma rushP (h:CalmS T A)(a:Walk): Dusk T (fun i x=> rail x a (A i)) := by
 induction a with
 | nil=> simp only [rail,LinearMap.zero_apply]; exact dusk_zero
 | cons i a ih=>
   simp only [rail,LinearMap.add_apply]; have he:= ih.mail (i.vec (R:=ℤ)) -- name
   have h':Dusk T (fun k x=> rail (x+i.vec) a (A k)):= by simpa only [mail_vec] using he
   apply Dusk.rake (f:=peakC T A i) _ h'; rw [lookC]; exact ((h _).mail _).scale _
lemma rushD (h:CalmS T A)(i j:Step): Dusk T (rushC T A i j):=by
 rw [icon_price]; have hs(u v:Step): Dusk T (slipC T (peakC T A u) v):=by rw [signed_ray,lookC]; exact (((((h _).mail _).scale _).ray_pay _).mail _).scale _
 exact Dusk.sub (hs _ _) (hs _ _)
def capG (T:Itinerary) : Hall T ℝ:= fun i=> (T.gap i ^2)⁻¹ • linGreen (T.period i)
lemma veins (k:Labels.Key G)(a:Axis) : knot T k a= ∑ t:QuotSpot k,(fun (i:ℕ) (x:Site (T.period i))=> wageA k t a (mailR T (surface (rivDir k t) (capG T)) (footA k t) i x)):= by
 funext i x
 rw [Finset.sum_apply,Finset.sum_apply,knot,river,Pi.smul_apply,repr_river]; simp_rw [sub_zero, Finset.smul_sum]; apply Finset.sum_congr rfl; intro t _
 simp only [wageA,ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.id_apply,mailR,capG,surface,combine_smul,Pi.smul_apply,smul_eq_mul,smul_smul]
 rw [← riv_mass k t,pow_add,mul_inv,pow_one]; ring_nf
lemma duskG (hc:MarkGrid T c): Dusk T (capG T):= by
 obtain ⟨C,hp,H⟩:= tor_decay T []; refine forward_lim hc (by norm_num:2≤3) Score.origin.identity ⟨C,hp,H.mono fun i hi x=> ?_⟩
 have hh:=hi x; have he:=T.positive i; dsimp only [capG]; rw [growsOut,mul_pow,Pi.smul_apply,norm_smul,Real.norm_of_nonneg (by positivity),mul_assoc,mul_left_comm ((T.gap i)^2),← mul_assoc ((T.gap i)^2),mul_inv_cancel₀ (by positivity),one_mul]; exact hh -- mul assoc?
def SeaA (T:Itinerary)(k:Labels.Key G)(o:StepPath T) : Sight T G:= fun i=> (T.gap i)⁻¹ • river (T.gap i) k (o i)
lemma soggy (hc:MarkGrid T c)(k:Labels.Key G) : CalmS T (SeaA T k 0):=by
 intro i; change Dusk T (knot T k i); rw [veins]; exact Dusk.sum _ fun _ _=>Dusk.shape (Dusk.mail ((duskG hc).cut _) _) _
def Pleased (T:Itinerary)(S:Set E4)(p:Hall T E):= ∃ Y, Score T S p Y
lemma Pleased.squash {K:Set E4}(h:Pleased T S f)(e: K ⊆ S): Pleased T K f:=by obtain ⟨Y,H⟩:= h; exact ⟨Y,H.restrict e⟩
lemma Pleased.enclose (h:Pleased T S f)(hp:Pleased T S g): Pleased T S (f+g):=by obtain ⟨Y,H⟩:=h; obtain ⟨P,p⟩:=hp; exact ⟨_,H.plus p⟩
lemma Pleased.scale (h:Pleased T S f)(r:ℝ): Pleased T S (r • f):=by obtain ⟨Y,H⟩:=h; exact ⟨_,Score.map (r • ContinuousLinearMap.id ℝ E) H⟩
lemma Pleased.by (h:Pleased T S f)(s:Cover): Pleased T S (mailR T f s):=by obtain ⟨Y,H⟩:=h; exact ⟨_,H.nudge _⟩
lemma Pleased.slip (h:Pleased T S f)(s:Step): Pleased T S (slipC T f s):=by obtain ⟨Y,H⟩:=h; rw [signed_ray]; exact ⟨_, Score.map (flareL s • ContinuousLinearMap.id ℝ E) ((H.insect [s.dir]).nudge _)⟩
lemma Pleased.left (h:Pleased T S f)(hp:Pleased T S g): Pleased T S (f-g):= by obtain ⟨Y,H⟩:=h; obtain ⟨P,p⟩:=hp; exact ⟨_,score_diff H p⟩
lemma Pleased.map₂ (h:Pleased T S f)(hp:Pleased T S q)(L:E→L[ℝ] V→L[ℝ] F): Pleased T S (fun i x=> L (f i x) (q i x)):=by obtain ⟨Y,H⟩:=h; obtain ⟨X,p⟩:=hp; exact ⟨_,H.product L p⟩
def HatP (T:Itinerary)(S:Set E4)(A:Sight T G):= ∀ i:Axis,Pleased T S (stalkH T A i)
lemma HatP.leg (h:HatP T S A)(s:Step): Pleased T S (peakC T A s):=by rw [lookC]; exact ((h _).by _).scale _
lemma walkP (h:HatP T S A)(a:Walk): Pleased T S (fun i x=>rail x a (A i)):= by
 induction a with
 | nil=> refine ⟨0,?_⟩; simp only [rail, LinearMap.zero_apply]; exact Score.untouched
 | cons i a ih=>
   simp only [rail, LinearMap.add_apply]; apply (h.leg i).enclose (g:=fun k x=> rail (x+i.vec) a (A k)) _; simpa only [mail_vec] using ih.by i.vec
lemma seesP (h:HatP T S A)(a b:Step): Pleased T S (rushC T A a b):= by rw [icon_price]; exact ((h.leg _).slip _).left ((h.leg _).slip _)
lemma wellP (h:HatP T S A)(p:HatP T S B)(a:Walk): Pleased T S (fun i x=> swerve x a (A i) (B i)):= by
 induction a with
 | nil=> simp only [swerve,LinearMap.zero_apply]; exact ⟨0,Score.untouched⟩
 | cons i a ih=>
   have h': Pleased T S (fun k x=>swerve (x+i.vec) a (A k) (B k)):= by simpa only [mail_vec] using ih.by i.vec
   have hr: Pleased T S (fun k x=>rail (x+i.vec) a (B k)):= by simpa only [mail_vec] using (walkP p a).by i.vec
   obtain ⟨L,H⟩:= doubles G.ad
   simp only [swerve_eq,←H]; exact Pleased.enclose ((h.leg i).map₂ hr L) h'
lemma spireP (h:HatP T S A)(p:HatP T S B)(a:Walk): Pleased T S (fun i x=> spire G x a (A i) (B i)) := by
 simp only [spire,LinearMap.smul_apply, LinearMap.add_apply, LinearMap.flip_apply]; exact ((wellP h p a).enclose (wellP p h a)).scale _
end YM.RG11.FirstW
