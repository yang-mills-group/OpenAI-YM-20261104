import YM.OPE.Compatible.Mason.Dawn
/-! # transfer budget Pu and Heavy projection through full normalized GP response. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Borealis
open Function Filter Set MeasureTheory Finset
open scoped Topology BigOperators Classical ContDiff ENNReal
open Silt Cloud PertExtension Series Libra GaussianScore Stranded Radial Jargon Cinders Spells
variable {G:Gauge}{I X Y:Type}{t s:ℝ}{i j k:ℕ}
section s
variable [NormedAddCommGroup X][NormedSpace ℝ X][FiniteDimensional ℝ X] -- no μ
abbrev Status (p:X→Token): Prop:=∀ i:Fin 3,Stature (skry p i) 0
variable {p q:X→Token}
lemma statusP (h:Carat p): Status p:= fun j=> (Stature.poly (h j).cost _)
omit [FiniteDimensional ℝ X] in
lemma statusH (h:Status p)(he:Status q): Status (p*q):=by intro i; fin_cases i; exact (h 0).mul (he 0); exact (((h 0).mul (he 1)).add ((h 1).mul (he 0))); exact (((h 0).mul (he 2)).add ((h 1).mul (he 1))).add ((h 2).mul (he 0))
omit [FiniteDimensional ℝ X] in
lemma statusF {Y:Type}[NormedAddCommGroup Y][NormedSpace ℝ Y](h:Status p)(L:Y→L[ℝ] X):Status (p ∘ L):= fun j=>(h j).blot _
end s
variable [NormedAddCommGroup X][NormedSpace ℝ X][FiniteDimensional ℝ X][MeasurableSpace X][BorelSpace X]
open Lav Flock Shift
section
variable (A:Law X)(μ:Measure X)[μ.IsAddHaarMeasure]
structure Weight (k:ℕ)(p:X→Token): Prop where
     color (i:Fin 3): GuardB μ A 0 (k+7-3*i.val) (skry p i)
variable {p q:X→Token}
lemma Weight.sure (h:Weight A μ k p)(hq: Carat q): Weight A μ k (p*q) := by
       let K(i:Fin 3):= k+7-3*i.val; have hv(i j l:Fin 3)(hh : K l + 3*j.val ≤ K i): GuardB μ A 0 (K l) (skry p i*skry q j):= (h.color i).stomp (hq j) hh
       refine ⟨fun i=>?_⟩; fin_cases i; exact hv 0 0 0 (Nat.le_refl _); exact (hv 0 1 1 (by dsimp[K];omega)).splices (hv 1 0 1 (Nat.le_refl _)); exact ((hv 0 2 2 (by dsimp[K];omega)).splices (hv 1 1 2 (by dsimp[K];omega))).splices (hv 2 0 2 (Nat.le_refl _))
section T
variable [NormedAddCommGroup Y][NormedSpace ℝ Y][FiniteDimensional ℝ Y][MeasurableSpace Y][BorelSpace Y]
variable (B:Law Y)(ν:Measure Y)[ν.IsAddHaarMeasure]
variable {g:X×Y→ℝ}
lemma SΓ (h:GuardB (μ.prod ν) (united A B) i k g): GuardB μ A 0 k (fun x=> B.average ν (fun y=>g (x,y))):=by
       refine ⟨decaf B ν h.hW, ⟨fun {j} hj p hp=>?_⟩⟩; let L:=LinearMap.fst ℝ X Y; have he:= hp.compLinear L; let f:=fun x:X=> B.average ν (fun y=>g (x,y)); have hh:=h.block.bill hj _ he
       rw[relays A μ B ν _ (h.hW.mul (Stature.poly he.cost i)),show (fun x:X=>B.average ν (fun y:Y=>(g * _) (x,y)))=f*p from ?_] at hh; exact hh
       ext1 x; change B.average ν (fun y:Y=>g (x,y)*p x)= _; rw [show (fun y:Y=>_)=p x • (fun y:Y=>g (x,y)) from funext fun _=>mul_comm .., scooted]; exact mul_comm ..
variable {p q:X×Y→Token}
local notation "Cr"=> crossT ν B
lemma Weight.house (h:Weight (united A B) (μ.prod ν) k p): Weight A μ k (Cr p):= by refine ⟨fun i=>?_⟩; fin_cases i; all_goals exact SΓ _ _ _ _ (h.color _)
lemma Weight.most (h:Weight (united A B) (μ.prod ν) k p)(hv:Carat q)(hp:∀ i,(q i).s=1): Weight A μ k (fun i=>Cr (p*q) i/Cr q i):=by
       apply Weight.sure A μ (p:=Cr (p*q)) (q:=fun i=>(Cr q i)⁻¹) (Weight.house A μ B ν (Weight.sure _ _ h hv)); exact tipC (casket hv) fun i=>headD ν B (fun y:Y=>q (i,y)) (fun y=> hp (i,y))
omit [FiniteDimensional ℝ X][MeasurableSpace X][BorelSpace X] in
lemma Salt (h:Status p): Status (Cr p):=by intro i; fin_cases i; exact decaf B ν (h 0); exact decaf B ν (h 1); exact decaf B ν (h 2)
omit [FiniteDimensional ℝ X][MeasurableSpace X][BorelSpace X] in
lemma Salt_add (h:Status p)(he:Status q): Cr (p+q)=Cr p+Cr q:=by
       ext1 x; have hf(f:X×Y→ℝ)(h:Stature f 0): RunsG B ν (fun i=>f (x,i)):=runsG _ _ (stat_slice h x);
       apply JetS.eta; exact duneAdd _ ν (hf _ (h 0)) (hf _ (he 0)); exact duneAdd _ ν (hf _ (h 1)) (hf _ (he 1)); exact duneAdd _ ν (hf _ (h 2)) (hf _ (he 2))
end T
variable [Fintype I]
open Adhesion Cascade.Paver RG Wilson Lattice MeasureTheory Precision
lemma Weight.clutch (V:Fiber X G I)(P:ChartRatio G)(h:LocalRatio P)(q:X×Keys G I→Token)(hz:Weight (united A V.Q) (μ.prod (Chart.tangent G I)) j (q ∘ Fiber.drape X _ V.M)): Weight A μ j (V.predicts P q):= Weight.most _ _ _ _ hz (atlasH V P) fun _=> curT (V.signPay h) _
omit [BorelSpace X] in
lemma SaltV (V:Fiber X G I)(P:ChartRatio G)(h:LocalRatio P)(q:X×Keys G I→Token)(he:Status (q ∘ Fiber.drape X _ V.M)): Status (V.predicts P q) :=by
      let μ:=Chart.tangent G I; let p:=V.cloth P; have hP:=atlasH V P; let q':= q ∘ Fiber.drape X _ V.M; let f:= crossT μ V.Q p; exact statusH (Salt _ _ (statusH he (statusP hP))) (statusP (p:=fun x=>(f x)⁻¹) (tipC (casket hP) (fun x=> headD μ V.Q (fun i:Keys G I=>p (x,i)) (fun _=>curT (V.signPay h) _)))) -- tc
omit [BorelSpace X] in
lemma SaltPeg (V:Fiber X G I)(P:ChartRatio G)(p q:X×Keys G I→Token)(hx:Status (p ∘ Fiber.drape X _ V.M))(hv:Status (q ∘ Fiber.drape X _ V.M)): V.predicts P (p+q)=V.predicts P p+V.predicts P q:=by
       let D:= Fiber.drape X (Keys G I) V.M; let b:=V.cloth P; let μ:= Chart.tangent G I; let A:= crossT (F:=X) μ V.Q; have hp:= statusP (atlasH V P); have ht:= Salt_add V.Q μ (statusH hx hp) (statusH hv hp); ext1 x; change (A (((p+q) ∘ D)*b) x)/ _= _/_+_/_; rw [show ((p+q)∘ D)* b=(p ∘ D)*b+(q∘D)*b from by rw [show (p+q) ∘ D=p ∘ D +q ∘D from rfl]; exact (add_mul ..)]; rw [show A _ x= _ from congr_fun ht x]; exact show (A ((p ∘ D)*b) x+A ((q ∘ D)*b) x)/ A b x=_ from by rw [JetS.dv,add_mul]; rfl
end
end YM.OPE.Borealis
