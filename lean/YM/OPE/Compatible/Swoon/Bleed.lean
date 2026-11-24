import YM.OPE.Compatible.Swoon.Nive
/-!
# Normalized cof parsed. all vertical signs. κ_{1}=0 this history
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Libra.Coin
open Function Filter Lattice Laurent Tree Woody Weir MeasureTheory Exterior Bloch Cascade Module
open scoped Topology BigOperators ComplexConjugate Classical ContDiff RealInnerProductSpace ENNReal
open RG Bid Pressure Precision FreeResolvent WithLp Next.Free Frequency
open PertExtension Series Asymptotics GaussianScore Radial Finset Matrix LinearMap Flock
variable {E F Y I:Type} [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
variable [MeasurableSpace E][BorelSpace E](μ:Measure E)[μ.IsAddHaarMeasure](L:Law E)
variable [NormedAddCommGroup F][NormedSpace ℝ F][FiniteDimensional ℝ F]
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma treeBond {n:ℕ} (T:Tensor.T F ℝ n)(p:E→F)(h:∀ ℓ:Dual' F, Bond (fun x=>ℓ (p x))): Bond (fun x:E=> T (fun _:Fin n=>p x)):=Bond.multiline T (fun _=>p) fun _ k=>h k
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma bondJets (p:E→F)(f:F→ℝ)(n:ℕ)(h:∀ ℓ:Dual' F, Bond (fun x=>ℓ (p x))): Bond (fun x=> jet f n (p x)):= (Bond.keep _).mul (treeBond _ _ h) -- omit
-- mean quadratic shift shared
lemma jetqu (W:F→ℝ)(x:F)(A:E→L[ℝ] F)(hv:ContDiffAt ℝ ω W 0): L.average μ (fun i=>jet W 2 (x+A i))=jet W 2 x+L.average μ (fun i=>jet W 2 (A i)):=by
        let p:= ((2:ℝ)⁻¹) • (iteratedFDeriv ℝ 2 W 0); have h(i):jet W 2 i=p ![i,i]:=by rw [njet]; change _= (2:ℝ)⁻¹*_;ring_nf;rfl
        simp_rw [h]; exact poundA μ L p x A fun v i=> congr_arg ((2:ℝ)⁻¹* · ) (Analysis.sym_Jet (hv.of_le le_top) v i)
lemma roy (s x:E→ℝ)(h:Bond s)(hp:Bond x): draw (fun i=>flareTok (s i) (x i)) L μ= flareTok (L.average μ s) (L.average μ x+(L.average μ (s^2)-(L.average μ s)^2)/2):=by
       apply JetS.eta; exact singleConst ..; rfl; change L.average μ (x+ fun i=>s i^2/2)=_+_; have hs : (fun i=> s i^2/2)= (2:ℝ)⁻¹ • (s^2):= funext fun i=> by simp only [Pi.smul_apply,Pi.pow_apply,smul_eq_mul];ring
       rw [hs,sun _ _ hp (Bond.scale _ (h.pow _)),scooted];ring
-- complete expression from Parser. f trivariate etc
variable (T:R3 F) (R:R4 F)(B:F→ℝ)(A:E→L[ℝ] F)
def Dome (p:F)(y:ℝ)(u:E):= let x:=p+A u; flareTok (-τ0 T x) (-τ4 R x+jet B 2 x+y)
section
variable (hs:Tensor.Sym T) (hp:Tensor.Sym R)(hh:ContDiffAt ℝ ω B 0)
include hs hp hh
omit hs hp hh μ [μ.IsAddHaarMeasure] [BorelSpace E] [MeasurableSpace E] [FiniteDimensional ℝ E] in
private lemma domeParts (p:F)(y:ℝ)(s:E→ℝ)(he: s=fun u:E=> τ0 T (p+A u))(q:E→ℝ)(hq: q=fun u:E=> τ4 R (p+A u)): Bond s∧Bond q∧ Bond (fun u=> jet B 2 (p+A u)+y):=by
       have ht(ℓ:Dual' F): Bond (fun u:E=>ℓ (p+A u)):= by simp only [map_add]; exact (Bond.keep (ℓ p)).add (Bond.glyph (ℓ.comp A.toLinearMap))
       have hA : ∀ (Q:F→ℝ)(hQ:Bond Q),Bond (fun u:E=> Q (p+A u)):= fun Q hQ=> hQ.comp ht; rw [he,hq]; refine ⟨hA (τ0 T) ?_,hA (τ4 R) ?_,?_⟩
       · unfold τ0; simp_rw [div_eq_mul_inv]; apply Bond.mul (v:=fun _=>(6:ℝ)⁻¹) _ (Bond.keep _); convert Bond.multiline T (fun (_: Fin 3)=> (id:F→F)) (fun _ l=> Bond.glyph l) using 1; funext i; apply congr_arg;ext1 j;fin_cases j<;>rfl
       · unfold τ4; simp_rw [div_eq_mul_inv]; apply Bond.mul (v:=fun _=>(24:ℝ)⁻¹) _ (Bond.keep _); convert Bond.multiline R (fun (_: Fin 4)=> (id:F→F)) (fun _ l=>Bond.glyph l) using 1; funext i; apply congr_arg;ext1 j;fin_cases j<;>rfl
       exact ((Bond.keep _).mul (Bond.multiline (iteratedFDeriv ℝ 2 B 0) (fun _ :Fin 2=> fun u:E=>p+A u) (fun _ ℓ=> ht ℓ))).add (Bond.keep y)
lemma coheres (p:F)(y:ℝ)(v:E)(ht:L.average μ (τ2 T p A)=0)(hx:τ1 T p A=(-2:ℝ)⁻¹ • L.P v):
       draw (Dome T R B A p y) L μ = flareTok 0 (- L.average μ (fun i=>τ4 R (A i))+L.average μ (fun i=>jet B 2 (A i))+(L.average μ ((τ3 T A)^2))/2) *
        flareTok (-τ0 T p) (-τ4 R p + jet B 2 p+y-L.average μ (τ21 R p A)+ L.P v v/8+L.average μ ((τ2 T p A)^2)/2 - L.average μ (τ2 T (A v) A)/2) :=by
       let s (i:E):=τ0 T (p+A i); let x(i:E):=τ4 R (p+A i); let d(i:E):= jet B 2 (p+A i); obtain ⟨h,hH,hC⟩:=domeParts T R B A p 0 s rfl x rfl; have ha:Bond d:=by simpa only [add_zero] using! hC
       rw [show Dome T R B A p y= _ from (show Dome T R B A p y=(fun i=> flareTok ((-s) i) ((-x+d+(fun _:E=>y):E→ℝ) i)) from rfl), roy μ L _ _ h.neg ((hH.neg.add ha).add (Bond.keep _)), sun _ _ (hH.neg.add ha) (Bond.keep _),sun _ _ hH.neg ha, blazeTok]; let g:= L.average μ (τ2 T (A v) A)
       have hv := τWool μ L T hs p A v hx; have hk:L.average μ s= τ0 T p:= (τav μ L T hs p A).trans (by rw [ht,add_zero]); rw [show ∀ i:E→ℝ,L.average μ (-i) = -L.average μ i from ?_,show L.average μ (-x)= -L.average μ x from ?_, hk,zero_add]; apply congr_arg; change -L.average μ x+L.average μ d+L.average μ (fun _=>y)+ _=_+_; rw [singleConst,show L.average μ x=_ from τAve μ L R hp p A,show L.average μ d=_ from jetqu μ L B p A hh, neg_sq]
       change L.average μ (s^2) - _ -_= _ at hv; rw [hk,ht] at hv; linarith only [hv]
       all_goals first | (intro i; rw [← neg_one_smul ℝ i,scooted];ring) | (rw [← neg_one_smul ℝ _,scooted];ring)
lemma nul : draw (Dome T R B A 0 0) L μ=flareTok 0 (- L.average μ (fun i=>τ4 R (A i))+ L.average μ (fun i=>jet B 2 (A i))+(L.average μ ((τ3 T A)^2))/2):=by
       have h: L.average μ (τ2 T 0 A)=0:=by rw [show τ2 T 0 A= fun _=>0 from funext fun i=> by unfold τ2; rw [T.map_coord_zero (i:= (0:Fin 3))]; exact zero_div _; rfl]; exact singleConst μ L 0
       have hf:τ1 T 0 A=0:=by ext i; change (2:ℝ)⁻¹ * T ![A i,0,0]=0; rw [T.map_coord_zero (i:= (1:Fin 3)),mul_zero]; rfl
       rw [coheres μ L T R B A hs hp hh 0 0 0 h (by simp [hf]), blazeTok]; congr 1 <;>simp [τ0,τ4] -- map zero
       · exact T.map_coord_zero (0:Fin 3) rfl
       rw [show R _= _ from (show R ![0,0,0,0]=0 from R.map_coord_zero (0:Fin 4) rfl), show τ21 R 0 A= fun _=>0 from funext fun i=>by unfold τ21; rw [R.map_coord_zero (i:=(0:Fin 4))];exact zero_div _; rfl, h, show τ2 T 0 A= (0:E→ℝ) from funext fun i=>by unfold τ2; rw [T.map_coord_zero (i:=(0:Fin 3))];exact zero_div _;rfl,zero_pow (by decide), show L.average μ 0= _ from singleConst μ L 0,singleConst,njet,show (iteratedFDeriv ℝ 2 B 0) ![0,0]=0 from ContinuousMultilinearMap.map_coord_zero _ (0:Fin 2) rfl];ring
end
end YM.OPE.Libra.Coin
