import YM.OPE.Compatible.Gum.Fancy
/-! # Brick algebra height test. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Libra.Shell
open Function Filter MeasureTheory Module
open scoped Topology BigOperators ComplexConjugate Classical ContDiff RealInnerProductSpace ENNReal
open Next.Free Bloch PertExtension Series Asymptotics GaussianScore Radial Finset Flock Coin Lattice Laurent RG Precision Flume Script Page Planned.PrimaryIntegral295.Carrier Matrix JetS ScriptJ
variable {I J E:Type} [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E] [MeasurableSpace E][BorelSpace E] (μ:Measure E)[μ.IsAddHaarMeasure] (L:Law E)
local notation "W"=> ScriptJ E
abbrev coin (x:ℝ):=JetS.plainJ x
def fair (l : W) (p:W): Token:= draw (p*l) L μ /draw l L μ -- greek parse
lemma Firmly (l:W)(h:l.B) {a b:W}(ha:a.B)(hb:b.B) : fair μ L l (a+b)=fair μ L l a+fair μ L l b:=by
    have hs :(a*l).B:=ScriptJ.height ha h; have ht :(b*l).B:=ScriptJ.height hb h; unfold fair; rw [add_mul, show draw (a*l+b*l) _ _=draw (a*l) L μ+draw (b*l) L μ from ?_,dv,dv,dv,add_mul]
    obtain ⟨h1,h2,h3⟩:=bondX hs; obtain ⟨h4,h5,h6⟩:=bondX ht; apply eta; exact sun _ _ h1 h4; exact sun _ _ h2 h5; exact sun _ _ h3 h6
lemma coastM (s:Token)(q:W)(h:q.B):draw (fun i=>s*q i) L μ=s*draw q L μ:=by
    obtain ⟨a,b,c⟩:= bondX h
    apply eta
    · exact scooted μ L s.s _
    · change L.average μ (fun i=> s.s*(q i).l+s.l*(q i).s)=_;rw [show (fun i=>_+_)= _ from (show (fun i=> s.s*(q i).l+s.l*(q i).s)=(s.s • (fun i=> (q i).l))+(s.l • fun i=> (q i).s) from rfl),sun _ _ (Bond.scale _ b) (Bond.scale _ a),scooted,scooted];rfl
    change L.average μ (fun i=> s.s*(q i).h+s.l*(q i).l+s.h*(q i).s)=_; erw [show L.average μ _= _ from sun _ _ ((Bond.scale s.s c).add (Bond.scale s.l b)) (Bond.scale s.h a),sun _ _ (Bond.scale _ c) (Bond.scale _ b), scooted,scooted,scooted];rfl
lemma coin_F (c:Token)(x y:W)(h:y.B)(hf:x.B): fair μ L x (fun i=>c*y i)=c*fair μ L x y:=by unfold fair; simp_rw [show (fun i=>c*y i)*x=fun i=>c*((y*x) i) from funext fun i=>mul_assoc ..,coastM μ L _ (y*x) (height h hf),dv]; ring
abbrev Ū:Token:=⟨0,1,0⟩
-- special probability kernel. choose Fin 5: S at 0,1; k3 at 2,3 V3,V2; reserved slot4. W formula uses.
abbrev Ask:=Fin 5
def rich (s:Finset Ask→ℝ):Token:= ⟨s ∅, s {0}, s {2}+s {3}+s {0,1}/2⟩
def brat (s t v:E→ℝ):W:=fun i=> flareTok (s i) ((t+v) i)
omit [FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E] in lemma bondW (s t v:E→ℝ)(h:Bond s)(hp:Bond t)(hh:Bond v): ScriptJ.B (brat s t v):=by
     apply Xbond; exact Bond.keep 1; exact h; convert! (hp.add hh).add (Bond.mul (h.pow 2) (v:=fun _=>(2:ℝ)⁻¹) (Bond.keep _)) using 1
omit [FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E] in lemma sty (p:E→ℝ)(hp:Bond p):ScriptJ.B (fun i=>coin (p i)):=Xbond hp (Bond.keep 0) (Bond.keep 0)
omit [μ.IsAddHaarMeasure] in
lemma rich0 (u:ℝ): flareTok 0 u=⟨1,0,u⟩:=by unfold flareTok;ring_nf
-- finite identity elimination
variable {w:Ask→ E→ℝ}
def Stell (w:Ask→ E→ℝ):W:= brat (w 0) (w 2) (w 3)
omit [FiniteDimensional ℝ E][BorelSpace E][μ.IsAddHaarMeasure] in
lemma payA {f:E→ℝ} (p:Ask→ E→ℝ)(a:Ask): Tap μ L p f {a}= L.average μ (f*p a)-L.average μ f*L.average μ (p a) :=by
     unfold Tap; rw [Tab_rec,show ({a}:Finset Ask).powerset.erase {a}= {∅} from ?_,Finset.sum_singleton]; swap
     · fin_cases a <;> decide
     rw [show Shell.Tab (drink μ L p 1) _ ∅= _ from salary μ L p f]; simp [drink,powr]
omit [FiniteDimensional ℝ E][BorelSpace E][μ.IsAddHaarMeasure] in
lemma payB (p: Ask→E→ℝ)(f:E→ℝ): Tap μ L p f {0,1} =
     L.average μ (f*(p 0*p 1))- ( Tap μ L p f {0}*L.average μ (p 1)+Tap μ L p f {1}*L.average μ (p 0)+ Tap μ L p f ∅* L.average μ (p 0*p 1)):=by
         let T(s:Finset Ask):= Tap μ L p f s * drink μ L p 1 ({0,1}\s); unfold Tap; rw [Tab_rec]; rw [show ({0,1}:Finset Ask).powerset.erase {0,1}={{0},{1},∅} from by decide]; change drink μ L p f {0,1}-(∑ i∈({{0},{1},∅}:Finset _), T i)=_;
         unfold T; unfold drink powr; simp only [Finset.prod_insert (by decide : (0:Ask) ∉ ({1}:Finset Ask)),Finset.prod_singleton, Finset.sum_insert (by decide : ({0}:Finset Ask) ∉ ({{1},∅}:Finset (Finset Ask))), Finset.sum_insert (by decide : ({1}:Finset Ask)∉({∅}:Finset (Finset Ask))),Finset.sum_singleton]; rw [show ({0,1}:Finset Ask)\{0}={1} from by decide, show ({0,1}:Finset Ask)\{1}={0} from by decide]; simp; unfold Tap drink powr;simp [add_assoc]
lemma rootC (p: Ask→ E→ℝ)(hp:p 0=p 1)(hs:∀ i,Bond (p i))(f:E→ℝ)(h:Bond f): fair μ L (Stell p) (fun i=> coin (f i))= rich (Tap μ L p f):=by
     let I(s:E→ℝ):= L.average μ s; let A:=I (p 0); let s:= p 0; let x:=p 2; let y:=p 3; let m:= x+y+(2:ℝ)⁻¹ • (s^2); let w:= Stell p; let v(i:E):= coin (f i); let H:=draw w L μ; have h₁:= hs 0; have h₂:= hs 2; have h₃:= hs 3; have heq:w=fun i=>⟨1,s i,m i⟩:=funext fun i=>by apply eta; rfl; rfl; change _+_=_+(2:ℝ)⁻¹*(s i)^2; change _+(s i)^2/2= _;ring
     have HE : H=⟨1,A, I x+I y+(2:ℝ)⁻¹*I (s^2)⟩:=by unfold H; rw [heq]; apply eta; exact singleConst ..; rfl; change I m=_; unfold m I; rw [sun μ L (h₂.add h₃) (Bond.scale _ (h₁.pow _)),sun μ L h₂ h₃,scooted]
     have hv : draw (v*w) L μ=⟨I f,I (f*s), I (f*x)+I (f*y)+(2:ℝ)⁻¹*I (f*s^2)⟩:=by
          rw [heq]; apply eta; · simp only [draw,Pi.mul_apply,ml_s]; change I (fun i=>f i*1)= _; simp
          · simp only [draw,Pi.mul_apply,ml_l];change I (fun x=> f x*s x+0*1)= I _; simp only [zero_mul, add_zero];rfl
          have hx:= h.mul h₂;have hy:= h.mul h₃; have hh:= h.mul (h₁.pow 2); simp only [draw, Pi.mul_apply,ml_h]; change I (fun i=> f i*m i+0*s i+0*1)= _; simp only [zero_mul,add_zero]; change I (f * m) = I _+I _+_* _; unfold m I; rw [mul_add,mul_add,mul_smul_comm,sun μ L (hx.add hy) (Bond.scale _ hh), sun μ L hx hy,scooted]
     unfold fair; change draw (v*w) L μ/H= _; rw [hv,HE]; apply eta <;>(simp only [dv,ml_s, ml_l,ml_h,sp_s,sp_l,sp_h,rich]; simp only [payB,payA,salary,←hp]; simp [A,s,x,y,I,pow_two] <;> ring)
 -- replace
end YM.OPE.Libra.Shell
