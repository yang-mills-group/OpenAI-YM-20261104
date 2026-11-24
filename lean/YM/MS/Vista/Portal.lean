import YM.MS.Vista.Grades
/-!
# Passage by natural charge monotonicity and restriction
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Vista
open Set Filter Function Finset Metric MeasureTheory Real High
open Koszul Plane Landau Detect Tone Momentum Heat Osc Fiddle Osc.Snap Native Lattice City Latch Job Belt Rake Flux Wire Book Convolve Orbit
open Rake.Geo
open scoped Topology ContDiff Interval
variable {I W:Type}{G:Gauge}{P:Belt I}{M:Visa I}{a:I→ℝ}{F H: Glade G I}{ L:I→Side}{b c:Bool}{d:ℝ}{X:I→ Law G}{x:ℝ}{A:P.time→ℝ}
variable (h:Market P M a)
abbrev castdown (i:I): P.time:= ⟨ i,a i, h.acc.begin i ⟩
def Boot (h:Market P M a): Scale I:= borrow P.price (castdown h)
lemma up_port (ht: Lease b c ( Boot h ) ( fun i=> F i (a i) ) (A ∘ (castdown h)))(hv:nn A)(hp:Adjuster (G:=G) P b c A): Lease b c P.price (LaunchF P a F) A:= by
   let S:=Boot h; let K(x:P.time):= (x.1:I); let p:= castdown h∘ K; have he (x:P.time) : tstart (p x)≤tstart x:= h.acc.time x; have hS:Bus P.price S K:= by
      refine ⟨ ⟨1,zero_lt_one,1,fun i=>?_⟩,1,zero_lt_one, fun i=> ?_⟩; · simp only [pow_one, one_mul,Pi.one_apply,mul_one, Function.comp_apply]; exact h.acc.mon (p i) i rfl (he i)
      rw [one_mul]; exact h.acc.step (p i) i rfl (he i)
   intro E _ _ w hew hV; exact Job.ticket (P:=K) hS ( ht E w hew hV ) ( paidMono (fun i=> hp E w hew hV (p i) i rfl (he i))) (pos_nn _ hv _)
-- Source at τ=0 budget
omit h
abbrev arrival (M:Visa I) : Scale I:= ⟨1,fun _=>zero_lt_one,M.bank,M.here⟩
lemma A_receipt (P:Belt I)(h:Market P M 0)(hp:∀ i,(P.price.length ( castdown h i ))=1): Boot h=arrival M:= by
   unfold Boot borrow arrival; congr! 1; funext; exact hp _; funext i; have hv:= h.fund (castdown h i); change P.price.basic _ = _; rw [hv]; change _*(1+|(0:ℝ)|)=_; simp

lemma awake (F:Glade G I)(x:ℝ)(h:Market P M 0)(hp:∀ i,(P.price.length ( castdown h i ))=1)(hv:Adjuster ( G:=G) P b c (goodM P x))(he: Lease b c (arrival M) ( fun i=>F i 0 ) 1): Lease b c P.price ( LaunchF P 0 F ) ( goodM P x ):= by apply up_port h _ ( pay_m _ _) hv; rw [A_receipt _ h hp,show goodM P x ∘ castdown h=(1:I→ℝ) from funext (fun z=> by rw [ Function.comp_apply,goodM,hp,one_rpow ]; rfl )]; exact he
abbrev WarpHere (b c:Bool)(P:Belt I)(F:Glade G I):= fun A=> Here b c P (warp0 G I F) A
-- mid Mum.
local notation "Θ"=>midpoint M L
local notation "Ϋ"=>unbounded M
abbrev kick (x:(Θ).time): (Ϋ).time:= ⟨ x.1,x.2.val, by exact (midT x).1 ⟩ -- mem ICI defin
lemma unwrap (p:(Θ).time): (Θ).price.length p=(Ϋ).price.length ( kick p ) := rfl
lemma cup_to_v (hf:Here b c (unbounded M) F (goodM (unbounded M) d)): Here b c Θ F ( goodM Θ d ):= by
   let K:=kick (M:=M) (L:=L); have HE : Bus (Θ).price (Ϋ).price K:= ⟨ ⟨1,zero_lt_one,1, fun i=> by rw [one_mul,pow_one,Pi.one_apply,mul_one]; rfl ⟩,1,zero_lt_one,fun i=> (by rw [one_mul]; rfl ) ⟩; exact fun E _ _ w hw hV=> Job.ticket (P:=K) HE ( hf E w hw hV ) ( paidMono (fun _=> le_rfl) ) ( pos_nn _ ( pay_m _ _ ) _ ) -- d currently ℤ; generalize.
-- boundary t=logGate
abbrev curtain (p:I): (Θ).time := ⟨ p, until0 L p, by exact ( Set.right_mem_Icc.mpr (φ_day L p) ) ⟩
lemma myEnd (p:I): (midpoint M L).price.length (curtain p)= tickA L p:= by rw [ AmountMX ]; exact glowH ..
lemma station (h: Here b c Θ F ( goodM Θ x ))(hp:Adjuster ( G:=G) ( After M L ) b c ( goodM (After M L) x )): Lease b c (After M L).price (LaunchF (After M L) (until0 L) F ) (goodM (After M L) x ):= by
    apply up_port ( M:=M ) soonM _ ( pay_m _ _ ) hp; intro E _ _ w h1 h2; let V:=Boot (P:=After M L) (M:=M) soonM; let K:=curtain (M:=M) ( L:=L ); have he (i:I): (Θ).price.length ( K i )= V.length i := myEnd i; have hs: Bus V (Θ).price K := ⟨ ⟨1,zero_lt_one,1,fun i=>by rw [pow_one, one_mul,Pi.one_apply,mul_one]; rfl ⟩,1,zero_lt_one, fun i=> (by rw [he,one_mul])⟩; apply Job.ticket ( S:=V ) ( P:=K ) hs (h E w h1 h2) (paidMono fun i=> ?_) ( pos_nn _ (fun _=> pay_m .. ) _ ); unfold Function.comp goodM; dsimp only; rw [ he ]; rfl -- multiple he.Price
end YM.MS.Vista
