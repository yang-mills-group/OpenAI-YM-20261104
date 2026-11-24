import YM.MS.Image.Mecca
/-!
# Four-scope. Full angular installing for interactions.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Outlook
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color _root_.YM.MS.Shine Hem Mell Logarithm Pearl Train Dock Emit
open Signal Book Convolve Garment.Wave Garment.Wick High Detect Domain Tone.Frame Momentum
open scoped Topology ContDiff Interval
variable {I E:Type} {G:Gauge}{X Y F:T ( Flats G)}{J N:Flats G}{b:Bool}{t r:ℤ}{n m h:ℕ}{s y:ℝ} {K:Mob G}
def handLE (s:Signed): FourP ≃ₗ[ℝ] FourP :=
    { s.actEquiv (R:=ℝ) with map_smul' c x := by funext i; change s.act (c • x) i= c*s.act x i; simp only [Signed.act]; split <;> simp }
def hand (s:Signed) : Arts.Spin Axis where
   turn:= (handLE s).toContinuousLinearEquiv
   rad x y:= by change pairing (s.act x) (s.act y)=_; refine Eq.symm (Fintype.sum_equiv s.perm (fun i=>x i*y i) _ (fun i=>?_)); rw [show _=_ from s.act_at x i,s.act_at]; split <;> simp
lemma hand_s (s:Signed)(i j:Axis): ((hand s).profile i j:ℂ)=(if s.perm i=j then cross (s.flip i) true else 0):= by obtain ⟨j,rfl⟩:= s.perm.surjective j; change (( s.act (spray i) (s.perm j):ℝ):ℂ)=_; rw [s.act_at]; by_cases h:i=j <;> simp [h, spray]; (cases s.flip j <;> simp)
lemma hand_index (s:Signed)(l:List (Lane4 G))(F:Law G) : ( flagS (m:=0) (hand s) G ).beam F l= (l.map (negateField s)).prod* F (l.map (permute s)) := by
   -- ambiguity Actor.Shore Axis.Use leg projections.
   induction l generalizing F with
   | nil=> simp
   | cons a l ih=>
       unfold flagS at ih; obtain ⟨⟨⟨_|a,c⟩,u⟩,q⟩:=a; · rw [show flagS (m:=0) (hand s) G= Spin.leggo G.ColorIndex _ from rfl, Spin.fromG,ih]; change _ =( _ :: _).prod * _; simp only [List.prod_cons,negateField,one_mul, at_D]; rfl -- goal
       rw [show flagS (m:=0) (hand s) G= Spin.leggo G.ColorIndex _ from rfl, Spin.fromV]; rw [Finset.sum_eq_single (s.perm a), ih, hand_s s a (s.perm a), if_pos rfl]; simp only [List.map_cons, List.prod_cons, at_D, negateField]; rw [mul_assoc]; rfl; · intro j hj he; rw [hand_s s a j, if_neg he.symm, zero_mul];
       simp
lemma lane (h:Sturdy true K): SignedScope b (K 0):= by intro g l hl; rw [← hand_index]; exact congr_fun (h.turn 0 (hand g) fun i=> Bool.noConfusion i) l -- defeq type issue
lemma antSolid (h: Gang b n t J) (s:Clock ℝ): Solid b (four n J s) t := by
   obtain ⟨r,hr⟩:= h.price; obtain ⟨x,y⟩:= s; have h0:= ( Moony.toast (clockMoon hr)); let F:= hereZ n J y x; have hp: Collar t F:= valueC h.dost h0 _ need_col (fun i=> (hr i).fine.ghost); have hx:Sight F:= sees_some h.dost h0 _ need_eye (fun i=> (hr i).fine.sense)
   exact ⟨fun l i j k _=> hp.sym 0 l i j k, fun v _ hv=>hp.ghost 0 v hv,fun w _ p=> congr_fun ( hp.color 0 p ) w, fun w _=> hx 0 w⟩ -- disam
lemma fleet (hf: Gang true h t J)(s:Clock ℝ): SignedScope true (four h J s):= by obtain ⟨y,t⟩:= s; obtain ⟨r,hr⟩:= hf.price; exact Outlook.lane (just_bright hf.dost (clockMoon hr)).token
lemma bed (h: Gang b n t J): ∃ r:ℕ,∀ s, Upper b r ( four n J s ):= by
   obtain ⟨r,hr⟩:= h.price; refine ⟨ r.toNat,fun ⟨y,t⟩ w hw hp=>?_⟩; obtain he: Issue r (hereZ n J t y):= valueC h.dost ( Moony.toast (clockMoon hr)) _ need_tail (clockCap hr); exact he 0 w (by omega)
end YM.MS.Outlook
