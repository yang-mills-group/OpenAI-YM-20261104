import YM.OPE.Compatible.Whet.Lend
/-!
# H.Launch supplies.Born.Cumul integrations at Mark. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Quit.PriceZ
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Cascade.Paver Cascade.Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion Drift Prairies
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Silt.Float Votive Alps Roles
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{P:Patch}{R:ChartRatio G}{C:KernelChoices}{p:Clip}
variable {W:Type}{X:W→Type}[∀ i,NormedAddCommGroup (X i)][∀ i,NormedSpace ℝ (X i)]
variable (n:W→Side)(H:∀ i,Even (n i).val)(Y:∀ i,Plot (H i))
local notation "C'" i=> Libra.Keys G (Stand.Free (Y i))
-- budget ≥4
variable {v v' b b':W→ℝ}(A:(j:W)→Alps K T i (v j))(Z:(l:W)→Alps K T j (v' l))
variable (L:∀ i,Bor (H i) (A i) (b i))(V:∀ i,Bor (H i) (Z i) (b' i))
variable {q s:W→ℝ}
local notation "AΞ"=>vL n H Y A L
local notation "DΞ"=>vL n H Y Z V
local notation "Wµ" i=>Chart.tangent G (Stand.Free (Y i))
abbrev ToughZ (b: W→ Script (Shade G) m)(s:W→ℝ) :Prop:=∃ c:ℝ,0≤c ∧∀ i,soot 0 (b i) (c*s i)
lemma Sunder {X Y:W→ Script (Shade G) m}(hp:ToughZ (X-Y) s)(hx:0 ≤ s)(U:∀ i,Plot (H i))(hz:∀ i,Summable (X i))(hh:∀ i,Summable (Y i)):
   WindZ n 4 m s ((fun i x=> TokenV (X i) (H i) (U i) x)-(fun i x=>TokenV (Y i) (H i) (U i) x)):=by
      obtain ⟨c,hc,W⟩:=hp; convert! parentArt n H U _ c hc hx W using 1; ext i x; simp only [Pi.sub_apply]; unfold TokenV; rw [←mul_sub]; apply congr_arg; unfold narrate; rw [sub_eq_add_neg (X i),libAdd (X i) (-Y i) (hz _) (hh i|>.neg),show -Y i=(-1:ℝ) • (Y i) from (neg_one_smul ℝ _).symm,libScale];ring
local notation "D!"=> fun i=> Impact (AΞ i) (DΞ i)
abbrev ScribeG (v':W→ℝ)(p:ℕ)(U:(i:W)→Alps K T p (v' i))(i:W):= fun k x=> jet (swornV (U i).clip (U i).live) k (rayS (H i) (Y i) G x)
lemma portPay (u:ℕ)(hs:0 ≤ s)(h:ToughZ (fun i=>(A i).word u - (Z i).word u) s): WindZ n 4 u s (fun l x=> ScribeG n H Y v i A l u x- ScribeG n H Y v' j Z l u x):=by -- i shadow idx
    unfold ScribeG; simp_rw [fun i x=> (S_jet A n H Y i x u).1, fun i x=> (S_jet Z n H Y i x u).1]; apply (show _ from Sunder n H (X:=fun i=>(A i).word u) (Y:=fun i=>(Z i).word u) h hs Y (fun l=> folk_whole (((A l).fullK u).here u)) (fun l=>folk_whole (((Z l).fullK u).here u)))
lemma topSkin (hs:0 ≤ s)(h:ToughZ (fun i=>(A i).word 2 - (Z i).word 2) s): WindZ n 4 2 s D! :=by
      have hh:= portPay n H Y A Z 2 hs h
      convert! hh.smul ((-1:ℝ)/4) using 1; funext p x; simp only [Pi.smul_apply,smul_eq_mul]; unfold Impact ScribeG vL; rw [neg_div,neg_div,←penon_shape, ←penon_shape, cargo _ _ (L p) _ 2 (by decide),cargo _ _ (V p) _ 2 (by decide)]; ring
abbrev crownV(i:W):= (L i).L (Y i)
abbrev LoansV (k:ℕ)(z:(i:W)→Alps K T k (v i))(w B:ℝ)(p:Clip) : Prop:=PathL B v ∧ ∀ i,(z i).clip=p∧0 ≤ v i∧v i≤w
lemma secondPay (h':0≤s)(h:ToughZ (fun i=>(A i).liftZ 2 - (Z i).liftZ 2) s):
   WindZ n 4 2 s (fun i x=> jet (swornY (A i).live) 2 (rayS (H i) (Y i) G x) - jet (swornY (Z i).live) 2 (rayS (H i) (Y i) G x)):=by
        simp_rw [fun i x=> (S_jet A n H Y i x 2).2, fun i x=> (S_jet Z n H Y i x 2).2]; apply (show _ from Sunder n H (X:=fun i=>(A i).liftZ 2) (Y:=fun i=>(Z i).liftZ 2) h h' Y (fun l=> folk_whole (((A l).fullL 2).here 2)) (fun l=>folk_whole (((Z l).fullL 2).here 2)))
-- β zero
lemma tickZ_0 (hs:G.Simple)(hr:LocalRatio R)(ht:b=0) (j:W) (x:C' j): ((L j).L (Y j)).hat R x=flareTok ( - ScribeG n H Y v i A j 3 x /4) (- ScribeG n H Y v i A j 4 x /4 - jet (swornY (A j).live) 2 (rayS (H j) (Y j) G x)/4+ jet (looper R) 2 x):=by subst b; rw [SwiftD (H j) (Y j) (L j) hr hs]; dsimp only; rw [receipt (H j) (Y j) (L j)]; unfold ScribeG; simp only [Pi.zero_apply]; ring_nf
lemma BoolHat {C'':Clip}(hp:∀ i,(A i).clip=p)(hp':∀ i,(Z i).clip=C'')(hs:G.Simple)(hr:LocalRatio R)(hz:b=0)(hz':b'=0)
   (he:0≤s)(h₃:ToughZ (fun i=>(A i).word 3 - (Z i).word 3) s)(h₄:ToughZ (fun i=>(A i).word 4 - (Z i).word 4) s)(h₂:ToughZ (fun i=>(A i).liftZ 2 - (Z i).liftZ 2) s):
    WindT n 8 6 s (fun i=> ((L i).L (Y i)).hat R - ((V i).L (Y i)).hat R):=by
       let a(l:W)(x:C' l):= - ScribeG n H Y v i A l 3 x /4; let t(l:W)(x:C' l):= - ScribeG n H Y v' j Z l 3 x/4
       let D(l:W)(x:C' l):= (ScribeG n H Y v i A l 4 x)-(ScribeG n H Y v' j Z l 4 x); let B(l:W)(x:C' l):= jet (swornY (A l).live) 2 (rayS (H l) (Y l) G x)-jet (swornY (Z l).live) 2 (rayS (H l) (Y l) G x)
       have hD: WindZ n 8 6 s D:= (portPay n H Y A Z _ he h₄).gauge he le_rfl (by omega) (by omega); have hB:WindZ n 8 6 s B:=(secondPay n H Y A Z he h₂).gauge he le_rfl (by omega) (by omega); have hx:WindZ n 4 3 1 a:= by convert! ((pegV A n H Y hp 3).neg).smul (4:ℝ)⁻¹ using 1; funext i x; unfold a ScribeG; simp only [Pi.smul_apply,Pi.neg_apply,smul_eq_mul];ring
       have hv: WindZ n 4 3 1 t:=by convert! ((pegV Z n H Y hp' 3).neg).smul (4:ℝ)⁻¹ using 1; funext i x; unfold t ScribeG; simp only [Pi.smul_apply,Pi.neg_apply,smul_eq_mul];ring
       have hW:WindZ n 4 3 s (a-t):=by convert! ((portPay n H Y A Z _ he h₃).neg).smul (4:ℝ)⁻¹ using 1; funext i x; unfold a t; simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Pi.neg_apply];ring
       have hK: WindZ n 8 6 s ((a-t)*(a+t)):=by simpa only [mul_one] using hW.mul (hx.add hv) he
       -- Wind using eq.L.St avoid conversion + simplify loops
       let T:=(fun i=> ((L i).L (Y i)).hat R); let P:=(fun i=> ((V i).L (Y i)).hat R)
       have eA(i x): (T i x).l= a i x:=by rw [show T i x= _ from tickZ_0 n H Y A L hs hr hz i x]
       have eB(i x): (P i x).l=t i x:=by rw [show P i x=_ from tickZ_0 n H Y Z V hs hr hz' i x]
       let Q:=((-1:ℝ)/4) • (D+B)+ ( (2:ℝ)⁻¹) • ((a-t)*(a+t))
       have e(i x): (T i x).h-(P i x).h= Q i x :=by
           rw [show T i x= _ from tickZ_0 n H Y A L hs hr hz i x, show P i x=_ from tickZ_0 n H Y Z V hs hr hz' i x]; simp only [Q,Pi.add_apply,Pi.smul_apply,Pi.sub_apply, smul_eq_mul,Pi.mul_apply,a,t,D,B];ring
       intro j; change WindZ _ _ _ _ (fun i x=> ((T i x)-(P i x)).seq j.val)
       fin_cases j
       · change WindZ _ _ _ _ (fun i x=> (T i x).s-(P i x).s); rw [show (fun i x=>(T i x).s-(P i x).s)=0 from funext fun i=>funext fun x=> by rw [show (T i x).s=1 from Lid.hat_full _ hr x, show (P i x).s=1 from Lid.hat_full _ hr x]; exact sub_self (1:ℝ)]; exact WindZ.zero ..
       · change WindZ _ _ _ _ (fun i x=> (T i x).l-(P i x).l); rw [show (fun i x=>(T i x).l-(P i x).l)=a-t from funext fun i=> funext fun x=>congrArg₂ (·-·) (eA i x) (eB i x)]; exact hW.gauge he le_rfl (by omega) (by omega)
       change WindZ _ _ _ _ (fun i x=> (T i x).h-(P i x).h); rw [show (fun i x=>(T i x).h-(P i x).h)=Q from funext fun i=> funext (e i)]; exact ((hD.add hB).smul ((-1:ℝ)/4)).add (hK.smul (2:ℝ)⁻¹)
end YM.OPE.Quit.PriceZ
