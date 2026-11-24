import YM.SignedWilsonExpansion.Belle.Lessons
/-! # Turn real W forcing price by pressure-calibration only after position.
 Proof on roster including arities=3 mask. No film of target contrast in calibration.
 Unit-cost controllers persistent all menus. Regular error o(...), orientation τ compatible.
-/
set_option autoImplicit false
set_option maxHeartbeats 640000
noncomputable section
namespace YM.SignedWilsonExpansion.Belle
open FVA2 FVA2.Dframe FVA2.Scale Dancer Dancer.Drawing Dancer.SeatsW
open Function Filter Asymptotics MeasureTheory Set XSpace XSpace.Structure1 Normalize
open MS MS.Menus MS.Puff MS.High MS.Land MS.Native MS.Fleet Maxwell Maxwell.Free Maxwell.Wick
open WilsonCoeffUV.Mer.Xa MarqueQ Crops PorchK PowerSeries Lesson Path Rose Commission
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge} {a b m n d:ℕ}{ι X:Type}{L:Filter ι}{t ν:ℝ}
namespace Buffet
variable (W:Initialize G){V: Normalize.Store G}(K: Rose.Pick V){Y:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))} {S:Prescription (Press.portDeck G)}(M:Speed.Quoted W K Y S)(s:G.Simple)
variable {τ ε:ι→ℝ}
variable {x x' y y':ι→ℂ}{f g:ι→ PS}
-- type0 ι intentionally. Moneyε.
local notation "A[" L "]" => @Path.Serves ι X ℂ _ L
lemma inCash (h:(fun i=> x i-y i)=o[L] ε) (w:y=O[L] (1:ι→ℝ))(p:ε=O[L] (1:ι→ℝ)): x=O[L] (1:ι→ℝ):= ( ( (h.trans_isBigO p).isBigO.add w ).congr_left (fun i=>sub_add_cancel ..) )
lemma muCash (h:y=O[L] (1:ι→ℝ))(k:x'=O[L] (1:ι→ℝ))(p:(fun i=> y i-y' i)=o[L] ε)(q:(fun i=> x i - x' i )=o[L] ε): (fun i=> x i*y i-x' i * y' i)=o[L] ε :=by
     let H:= q.mul_isBigO h; let Q:= k.mul_isLittleO p; exact ((H.congr_right (fun i=> (mul_one (ε i)))).add (Q.congr_right (fun i=> one_mul _ ))).congr_left (fun i=> by ring)
structure Basket (L:Filter ι)(b:ℕ)(t ε:ι→ℝ)(f:ι→PS)(x:ι→ℂ):Prop where
     purse : charge b L 1 1 f
     bound : x=O[L] (1:ι→ℝ)
     cost : (fun i=>x i-calcT (t i) b (f i))=o[L] ε
lemma unfoldW {s:ι→ℝ}{E:Type}[Norm E]{x:ι→ E}(p:Wage L 1 s x) : x=O[L] s :=by obtain ⟨i,hi⟩:=p; exact hi.congr_right (fun i=>by simp)
variable (paid:∀ᶠ i in L, |τ i|≤1)(tip:(fun i=> τ i^(b+1))=o[L] ε)
lemma awarded : Maxer L (1:ι→ℝ):= Eventually.of_forall fun _=>le_refl _
include paid in
lemma Basket.earns (q:charge b L 1 1 f): (fun i=> calcT ( τ i ) b (f i))=O[L](1:ι→ℝ):= unfoldW ( clockQ.chooseOne awarded paid (fun i=>(τ i:ℂ)) ( IsBigO.of_bound' ( Eventually.of_forall fun i=> (Complex.norm_real _).le )) f q b le_rfl )
variable (B : Basket L b τ ε f x)(D: Basket L b τ ε g y)
include paid tip B D in
lemma Basket.eggs : Basket L b τ ε (f*g) (x*y) :=by
     refine ⟨ (by simpa only[one_mul,show (fun i=> f i*g i)=f*g from rfl ] using MarqueQ.PorchK.charge.mul awarded B.purse D.purse), (B.bound.mul D.bound).congr_right (fun i=> one_mul _),?_⟩; -- charge namespace ?
     let a'(i:ι):=calcT ( τ i ) b; let Y(i):= a' i (g i); let X(i):= a' i ( f i ); have hu: (fun i=> X i * Y i- a' i (f i*g i))=O[L] (1*(1:ι→ℝ)*τ^(b+1)) := unfoldW ( clockQ.mulch awarded paid _ ( IsBigO.of_bound' (Eventually.of_forall fun i=> (Complex.norm_real _).le)) f g B.purse D.purse ); simp only [one_mul] at hu; refine ((IsLittleO.add ( muCash D.bound (Basket.earns paid B.purse) D.cost B.cost ) (hu.trans_isLittleO tip)).congr_left fun i=> by exact sub_add_sub_cancel .. )
include B D in
lemma Basket.plus : Basket L b τ ε (f+g) (x+y) := by
     constructor
     · intro i p; simp only [Pi.add_apply,map_add]; exact Wage.plus awarded (B.purse i p) (D.purse i p)
     · exact B.bound.add D.bound
     exact (B.cost.add D.cost).congr_left fun i=> by rw [Pi.add_apply,Pi.add_apply,map_add]; ring
include B in
lemma Basket.neg : Basket L b τ ε (-f) (-x):=by
     refine ⟨fun i p=> ?_, B.bound.neg_left, ?_⟩; · simp_rw [Pi.neg_apply,map_neg]; exact (B.purse i p).neg
     exact B.cost.neg_left.congr_left (fun i=> by rw [Pi.neg_apply,Pi.neg_apply,map_neg]; ring)
abbrev cumul (x:Badge→ℂ):ℂ:= x Finset.univ - (x {0,1}*x {2}+ x {0,2}*x {1}+x {1,2}*x {0})+2*(x {0}*x {1}*x {2})
omit B D in
lemma scheme (p:Badge→ι→PS)(x:Badge→ι→ℂ)(H:∀ t:Badge,Basket L b τ ε ( p t ) ( x t )) (paid:∀ᶠ i in L,|τ i|≤1)(tip:(fun i=> τ i^(b+1))=o[L] ε): Basket L b τ ε (fun i=> Rose.b3 (fun t=> p t i)) (fun i=> cumul (fun t=>x t i)) :=by
     let A:= Basket.plus (B:=H Finset.univ) (D:= Basket.neg ( B:=Basket.plus (B:=Basket.plus (B:= Basket.eggs paid tip (H {0,1}) ( H {2} )) (D:= Basket.eggs paid tip (H {0,2}) ( H {1} )) ) (D:= Basket.eggs paid tip (H {1,2}) (H {0}) ))) -- `include B` order :=
     let hx:=Basket.eggs paid tip (Basket.eggs paid tip (H {0}) (H {1})) (H {2}); refine Eq.mp (?_) (Basket.plus (B:=A) (D:=Basket.plus (B:=hx) (D:=hx)))
     congr 1
     · ext1 i; simp only[Pi.add_apply,Pi.mul_apply,Pi.neg_apply,b3,two_smul]; rw [sub_eq_add_neg]
     ext1 i; simp only [Pi.add_apply,Pi.mul_apply,Pi.neg_apply,cumul, sub_eq_add_neg,two_mul]
variable (X:ι→Badge→Points 3→ℂ)(v: Badge→ Tags G d 3)(U:Set (Points 3))(K0:Roi U)
local notation "D*"=> FVA2.Scale.Measure.start W K d
abbrev outlook (v:Tags G d 3)(x:Points 3): PS:=mk ( fun i=> Jury.fxt D* x i v )
include s M
include K0
lemma faceP (Φ:Badge)(vP: ε=O[L] (1:ι→ℝ))(h:Serves L (fun i=> X i Φ) (fun i z=> mote D* b z (τ i) (v Φ)) U ε)(t:Tendsto τ L (𝓝 0)) : Basket (diners L U) b (τ ∘ Prod.fst) (ε ∘ Prod.fst) (fun i=> Buffet.outlook W K (v Φ) i.2) (buys (fun i=> X i Φ)) :=by
    let D':= D*; let u:=v Φ; let f'(i:ι):= fun z=> mote D' b z (τ i) u; let p:= price W K M s K0 b u ( isBigO_const_of_tendsto t one_ne_zero ); let S:=banquet.mp h
    refine ⟨fun i _=>?_, inCash S p (vP.comp_tendsto plot_le), S.congr_left (?_) ⟩; · simp only [ Buffet.outlook,coeff_mk ]; exact Wage.enroll (Path.cost (L:=L) W K M s K0 _ u)
    intro i; change X i.1 Φ i.2 - mote D' b i.2 _ u=_; rw [timed]; unfold Buffet.outlook Path.mote; simp_rw [coeff_mk]; exact congr_arg (_ - ·) (Finset.sum_congr rfl fun j _=> mul_comm ..)
lemma paysB (vp:ε=O[L] (1:ι→ℝ))(h:∀ Φ,Serves L (fun i=> X i Φ) (fun i z=> mote D* b z (τ i) (v Φ)) U ε)(t:Tendsto τ L (𝓝 0))(tip:(fun i=> τ i^(b+1))=o[L] ε): Serves L (fun i y=> cumul (fun p=> X i p y)) (fun i y=> calcT (τ i) b (Rose.b3 (fun t=> Buffet.outlook W K (v t) y))) U ε :=by
     have hB:∀ᶠ i:ι×Points 3 in diners L U, |τ i.1|≤1:= plot_le.eventually ( by simpa using (t.norm.eventually_le_const (by simp: ‖(0:ℝ)‖<1)) ); exact banquet.mpr ( ( scheme (fun Φ (i:ι×Points 3)=>Buffet.outlook W K (v Φ) i.2) ( fun Φ i=> X i.1 Φ i.2 ) (fun Φ=> faceP W K M s X v U K0 Φ vp (h Φ) t ) hB (tip.comp_tendsto plot_le) ).cost )
end Buffet
end YM.SignedWilsonExpansion.Belle
