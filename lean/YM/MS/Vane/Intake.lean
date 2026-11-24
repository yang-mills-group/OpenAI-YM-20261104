import YM.MS.Rake.Edict
/-!
# Weighted times.Window.Mid. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Vane
open Set Filter Function Finset MeasureTheory Metric Real
open Koszul Plane Landau Detect Tone Momentum Heat High Frame Wire Signal Flux Wind Garment Outlook Latch Job Belt Rake Geo
open Osc Fiddle Snap Book.Convolve
open scoped Topology ContDiff Interval
variable {G:Gauge}{I W J E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{P: Geo I}{x η:ℝ}{u t:ℤ}{a b s k m n h:ℕ}
local notation "℧"=> Gulf P
abbrev Stem (P:Geo I) := ( Gulf P ).time
abbrev barrier {K:Belt I}(p:K.time):= P.θ p.1 -- needs P explicit not infer in rhs? abbrev global p param invis
abbrev life (P:Geo I)(d k:ℕ)(a:ℝ)(p:Stem P): ℝ:= exp ((k-d-a:ℝ)*tstart p - k*(P.θ p.1))
abbrev Bud (P:Geo I)(h:ℕ)(α:ℝ)(F:Glade G I): Prop := ∀ k, Here false false (Gulf P) F (life P h k α)
lemma authority (p:Stem P): 0≤tstart p ∧ tstart p ≤ P.θ p.1:= p.2.property
lemma tilt (hp:m≤ n): life P h n x ≤ life P h m x:= by intro p; apply exp_monotone; nlinarith [ authority p|>.2, (show (m:ℝ)≤n from by exact_mod_cast hp)]
lemma raised (P:Geo I)(a:ℝ)(h n:ℕ): nn (life P h n a):= fun _=> exp_pos _ |>.le -- k unused
lemma near (i:Stem P): (Gulf P).price.length i = exp (tstart i):= rfl
lemma pulseβ (i:Stem P): (℧).price.length i / P.roots i.1 = exp (tstart i-P.θ i.1):= by rw [ exp_sub ]; rfl
lemma dotzero (k:ℕ): rateS ℧ k= life P k 0 0:= by ext i; simp only [ rateS,near, a_e,life,Nat.cast_zero, zero_sub,sub_zero, zero_mul, Int.cast_neg,Int.cast_natCast]; congr 1; ring
lemma accel (P:Geo I)(h:ℕ)(x:ℝ)(k:ℕ) (p:Stem P):life P h (k+1) x p= life P h k x p* ( (Gulf P).price.length p/P.roots p.1):= by rw [pulseβ]; unfold life; rw [← Real.exp_add]; push_cast; congr 1; ring
lemma stock (k n:ℕ)(p:Stem P): life P h ( k+n ) x p= life P h k x p*( (℧).price.length p/P.roots p.1 )^n:= by
    induction n with| zero=>simp | succ n ih=>rw [← add_assoc,accel,ih,pow_succ,mul_assoc] -- q removed
lemma roll (h n k m:ℕ)(p:Stem P): life P h k x p * life P n m η p= life P (h+n) ( k+m ) (x+η) p:= by unfold life; rw [← exp_add]; push_cast; congr 1; ring
lemma fertile (he:0<(k-n-x:ℝ)): Break (G:=G) false false ℧ (life P n k x) (life P n k x) := by
   apply breakWalk (εGulf _ ) _ he; refine ⟨ raised _ _ _ _,1,zero_lt_one,?_⟩; intro p q hq hu; unfold life; rw [show P.θ q.1=P.θ p.1 from congr_arg P.θ hq.symm, one_mul, ← exp_add]; apply le_of_eq; congr 1; unfold δf tstart; ring
-- transfer initial bound any. allows α∈ (0,1) or generic.
abbrev renew (P:Geo I) (i:I) (b:Bool) : (east P b).time:= ⟨ i,0, by exact (le_refl (0:ℝ)) ⟩
abbrev Early (P:Geo I) (X:Glade G I) (p:Stem P): Law G:= X p.1 0
def ride (P: Geo I)(b:Bool): Stem P→(east P b).time:= fun q=> renew P q.1 b
lemma σbill (P: Geo I) (b:Bool)(i:Stem P): (east P b).price.length (ride P b i)=1:= by cases b; rw [coldE]; exact exp_zero; exact unitE ..
lemma embassy (P:Geo I)(b:Bool): Bus ( Gulf P).price (east P b).price (ride P b):= by
    constructor; · refine ⟨1,zero_lt_one,1,fun i=>?_⟩; simp only [Function.comp_apply,one_mul,mul_one,Pi.one_apply,pow_one ]; change habitat P i.1*(1+|(0:ℝ)|) ≤ habitat P i.1*(1+|tstart i|); apply mul_le_mul_of_nonneg_left _ (by unfold habitat; positivity); simp
    exact ⟨ 1,zero_lt_one,fun i=>by rw [one_mul,near,σbill]; exact Real.one_le_exp (authority i|>.1)⟩
lemma tarStage (b:Bool)(i:Stem P): birthTar P k (ride P b i)=exp ( -(k:ℝ)*P.θ i.1 ) := by change exp 0* _ ^ k=_; rw [ exp_zero,one_mul,← Real.exp_nat_mul ]; congr 1; change ↑k*(-P.θ i.1)= _; ring
lemma Midland (hp:(0:ℝ)≤ m-n-x) (b:Bool) {F:Glade G I}(hx:Here false false (east P b) F ( birthTar P m )) : Lease false false (Gulf P).price ( Early P F ) ( life P n m x ):= by
   intro E _ _ w hw hk; apply Job.ticket ( P:=ride P b ) ( embassy P b ) ( hx E w hw hk ) ?_ ( pos_nn _ ( raised _ _ _ _ ) _ ); apply paidMono; intro i; dsimp only [comp]; rw [σbill, one_zpow,one_mul,tarStage]; apply le_trans _ ( le_mul_of_one_le_left ( (raised P x n m) i ) ?_ ); · apply Real.exp_monotone; nlinarith [hp,authority i|>.1]
   exact one_le_zpow₀ (by rw [near]; exact Real.one_le_exp (authority i|>.1)) (pitch_nn w) -- lemma name
end YM.MS.Vane
