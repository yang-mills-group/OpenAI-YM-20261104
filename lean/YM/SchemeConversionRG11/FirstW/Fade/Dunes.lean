import YM.SchemeConversionRG11.FirstW.Fade.Dusking
import YM.Pert.Triangle.Price
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW
open Function Filter Set MeasureTheory Lattice Pert Align Topology Maxwell
open scoped BigOperators Classical
variable {T:Itinerary} {c:ℕ→Side} {E F V:Type} [NormedAddCommGroup E] {G:Gauge} {k:ℕ} {o:StepPath T}{x:E4}
abbrev Gulf (T:Itinerary)(i:ℕ)(y:Site (T.period i)):= growsOut (T.gap i) y
lemma gulf_pos (T:Itinerary)(i:ℕ)(y:Site (T.period i)):0<Gulf T i y:= mul_pos (T.positive i) (zero_lt_one.trans_le (unit_cy _))
variable {f g:Hall T E}
def Dune (T:Itinerary)(o:StepPath T)(k:ℕ)(f:Hall T E):= ∃ C>0,∀ᶠ i in atTop,∀ x:Site (T.period i), Gulf T i (x-o i)^k*‖f i x‖≤ C
lemma Dune.shift (h:Dune T o k f)(s:Cover): Dune T o k (mailR T f s):=by
 let A:=1+stepY s; have ha:0<A:=by unfold A; linarith only [unit_stepY s]
 obtain ⟨C,hp,H⟩:=h; refine ⟨A^k*C,by positivity,?_⟩; filter_upwards [H,past T s] with i hi he x
 let y:=x+wrap (T.period i) s; have hv:= (he (x-o i)).2; rw [show x-o i+wrap (T.period i) s=y-o i by unfold y; abel] at hv
 have h : Gulf T i (x-o i) ≤ A*Gulf T i (y-o i):=by unfold Gulf growsOut;rw [mul_left_comm]; exact mul_le_mul_of_nonneg_left hv (T.positive i).le
 change _ *‖f i y‖≤_; refine le_trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (gulf_pos ..|>.le) h k) (norm_nonneg _)) ?_; rw [mul_pow,mul_assoc]; exact mul_le_mul_of_nonneg_left (hi y) (by positivity)
lemma Dune.roll (h:Dune T o k f)(hp:Dune T o k g): Dune T o k (f+g):=by obtain ⟨C,hC,H⟩:=h; obtain ⟨D,hD,M⟩:=hp; refine ⟨C+D,by positivity,(H.and M).mono fun i hi x=>?_⟩; have he:= gulf_pos T i (x-o i); refine le_trans (mul_le_mul_of_nonneg_left (norm_add_le ..) (by positivity)) ?_; rw [mul_add]; exact add_le_add (hi.1 x) (hi.2 x)
lemma skyhut : Dune T o k (0:Hall T E):= ⟨1,one_pos,Eventually.of_forall fun i x=>by simp⟩
lemma Dune.less (h:Dune T o k f)(hp:Dune T o k g): Dune T o k (f-g):=by
 rw [sub_eq_add_neg]; obtain ⟨C,hc,H⟩:=hp; apply h.roll; exact ⟨C,hc, H.mono fun i hi x=>by simp; exact hi x⟩
lemma Dune.scale [NormedSpace ℝ E] (h:Dune T o k f)(r:ℝ): Dune T o k (r • f):=by
 by_cases he:r=0; · rw [he,zero_smul]; exact skyhut
 obtain ⟨C,hc,H⟩:=h; refine ⟨‖r‖*C, mul_pos (norm_pos_iff.mpr he) hc,H.mono fun i hi x=>?_⟩; simp only [Pi.smul_apply,norm_smul]; rw [mul_left_comm]; exact mul_le_mul_of_nonneg_left (hi x) (norm_nonneg _)
def CrestS (T:Itinerary)(o:StepPath T)(k:ℕ)(A:Sight T G) :=∀ i:Axis,Dune T o k (stalkH T A i)
def Shore (T:Itinerary)(o:StepPath T)(k:ℕ)(A:Sight T G):= CrestS T o k A ∧ ∀ i j:Step,Dune T o (k+1) (rushC T A i j)
lemma seaA_prices (k:Labels.Key G)(a:Axis)(o:StepPath T)(D:List Axis): Dune T o (D.length+mass k+1) (surface D (stalkH T (SeaA T k o) a)):=by
 let n:= D.length+mass k+1; obtain ⟨C,hC,H⟩:= tread k T a D; refine ⟨C,hC,H.mono fun i hi x=>?_⟩
 have hp: (fun y:Site (T.period i)=> stalkH T (SeaA T k o) a i y)= ((T.gap i)⁻¹ • ((T.gap i ^ (mass k))⁻¹ • fun y:Site (T.period i)=> canal k (o i) (y,a))):= rfl
 have he := hi x (o i); let p:=T.gap i; have hx : p>0:=T.positive _; let F:= combine D (fun y=> canal k (o i) (y,a)) x
 unfold surface; rw [show stalkH T (SeaA T k o) a i=_ from hp, combine_smul, combine_smul]; simp only [Pi.smul_apply, smul_smul]; change (p * _)^n*‖_ • F‖≤ _
 have hv : p^n*((T.gap i^D.length)⁻¹ * ((T.gap i)⁻¹ *(T.gap i ^(mass k))⁻¹))=1:=by unfold n p; field_simp [(T.positive i).ne']; ring
 rw [norm_smul, Real.norm_of_nonneg (by have := T.positive i; positivity), mul_pow]; exact le_trans (le_of_eq (show _= cy (x-o i)^n*‖F‖ from by rw [← one_mul (cy _ ^ _ * ‖F‖),← hv]; ring)) he
lemma ray_post (f:Hall T G.Color)(a: Axis)(s:Cover): ray a (mailR T f s)=mailR T (ray a f) s:= funext fun i=>funext fun x=>by simp only [ray,mailR,surface,Pi.smul_apply, combine, up]; rw [add_right_comm]
lemma ray_weight (f:Hall T G.Color)(r:ℝ)(a:Axis): ray a (r • f)=r • ray a f:= funext fun i=>funext fun x=>by simp only [ray,surface,combine,up,Pi.smul_apply,← smul_sub];rw [smul_comm]
lemma shore_quote (k:Labels.Key G)(o:StepPath T): Shore T o (mass k+1) (SeaA T k o):=by
 constructor
 · intro i; simpa only [List.length_nil,zero_add,surface_root] using seaA_prices k i o []
 intro i j
 have h(u v:Step): Dune T o (mass k+1+1) (slipC T (peakC T (SeaA T k o) u) v):=by
   rw [signed_ray, lookC,ray_weight,ray_post]; apply Dune.scale; apply Dune.shift; apply Dune.scale; apply Dune.shift; rw [add_comm (mass k)]; exact seaA_prices k u.dir o [v.dir]
 rw [icon_price]; exact (h j i).less (h i j)
end YM.RG11.FirstW
