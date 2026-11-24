import YM.OPE.Compatible.Loire.Card
/-!
# Hermitian pair estimate at one annotated evaluation
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Shrew
open Function MeasureTheory Set Topology Metric Filter Lattice Laurent Wilson Exterior Cascade PertExtension Series Score Next.Foundations Matrix
open Next.Free Frequency Bloch MSbar.Tree MSbar.Tree.Resolvent Terp Stubble Weir
open GaussianScore Libra WithLp RG Precision Votive Glass Radial Flume.Script Flock StageLight Balsam
open scoped BigOperators Classical ContDiff Matrix.Norms.Frobenius RealInnerProductSpace
attribute [local instance] Gauge.frobInner
variable {n:Side}{G:Gauge}{C:RG.KernelChoices}{P:ChartRatio G}{U:Gloam}
variable {i:ℕ}{l b:ℝ}{B:Sponsor G} {Q:Seasons B}{A:Alps B Q i l}
section full
variable {T:Type}[LinearOrder T](H:∀ p,Even (U.M p).val)(α:T→Match U G)(h:4 ≤ i)
local notation "W"=> (fun p:ℕ=>Chart.tangent G (Limb (H p)))
local notation "Θ"=> (fun p:ℕ=>boost (H p) (Train.top i) h B.K (G:=G))
local notation "Λ"=> (fun p i => ps (α i) p (H p))
-- average anti
abbrev Timeless (x:Match U G)(p:ℕ):= ((Θ) p).inverse (ps x p (H p)) -- add harps
local notation "Bp"=>fun p:ℕ=> anthem G (H p)
local notation "Ps!"=>fun (x:T) i=> Timeless (B:=B) H h (α x) i
omit [LinearOrder T] in
lemma nutmeg (x y z:T): Fruit U ((α x).P.heat+(α y).P.heat+(α z).P.heat) (fun p=> bishops ((Bp) p) ((Ps!) x p) ((Ps!) y p) ((Ps!) z p)) 0:=by
    let m(a:T):=(α a).P.heat; let f(x y z:T)(i:ℕ):= anthem G _ ((Ps!) x i) ((Ps!) y i) ((Ps!) z i)
    have he(u v w:T): Fruit U (m u+m v+m w) (f u v w) 0:= by
         let c:=(G.colorScale^2*8)⁻¹; let k:= α; simpa only [mul_zero] using! (Nestle.payScalar c (ledge_Fruit H ((k u).sit) ((k v).sit) ((k w).sit) ((k u).P) ((k v).P) ((k w).P) ((k u).a) ((k v).a) ((k w).a) h (C:=B.K)))
    change Fruit U (m x+m y+m z) (f x y z+f x z y+f y x z+f y z x+f z x y+f z y x) 0
    have U (a b c:T)(hg:m x+m y+m z=m a+m b+m c): Fruit U (m x+m y+m z) (f a b c) 0:= hg.symm ▸ he a b c
    simpa only [add_zero] using (((((U x y z rfl).sum (U x z y (by omega))).sum (U y x z (by omega))).sum (U y z x (by omega))).sum (U z x y (by omega))|>.sum (U z y x (by omega)))
abbrev wool (α:T→Match U G)(x:T):=(α x).P.heat
abbrev Wood (α:T→Match U G)(s:Finset T):=∀ i∈s,∀ j∈s,i≠j→ SpareW (α i).sit (α j).sit
abbrev ship (α:T→Match U G)(x y:T):=rootW (α x) (α y)
lemma wick_quill (p:Finset T)(hv:Wood α p)(hG:G.Simple)(hp:A.gear=Train.top i)(ht:∀ i, Track A (U.M i)): Quill W Θ Λ (ship α) U p (wool α) (fun p=>Trill (anthem G (H p))) 0:=by
   let C:=Ced p U Λ Θ (wool α) (ship α); have he:C:=fun a h b hh hn=>embark H _ _ (hv _ h _ hh hn) _
   let f(j):=Trill ((Bp) j); let A'(a:T):=twist Θ (fun p=>(Λ) p a) f; let D(a b:T):= twist Θ (fun p=>(Λ) p b) (A' a)
   apply quill _ p he (fun i=> anthemBond (ht i)) (fun j=> colorful ((W) j) ((Θ) j) (f j) (anthemBond (ht _)) (trill_neg _)); intro a ha; apply quill _ p he (fun i=> (anthemBond (ht i)).amount _) (fun i=>tideD hp h (ht _) _ hG); intro b hb; apply quill _ p he (fun i=> ( (anthemBond (ht i)).amount _ |>.amount _)) (fun i=>?_)
   · intro c hc
     let k:=fun j=>bishops ((Bp) j) ((Ps!) a j) ((Ps!) b j) ((Ps!) c j)
     let C'(j):=ps (α c) j (H j)
     change Quill W Θ Λ (ship α) U p (wool α) (twist Θ C' (D a b)) (0+ _+_+_); rw [show twist Θ C' (D a b)=(fun i _=>k i) from funext fun i=> poke_hr _ _ _ _ (anthemBond (ht _)), zero_add]; exact gavel _ _ he (nutmeg H α h a b c)
   let φ:= f i
   apply colorful ((W) i) ((Θ) i) _ (show Bond (D a b i) from ((anthemBond (ht i)|>.amount ((Ps!) a i)).amount ((Ps!) b i)))
   intro x; change poke ((Ps!) b i) (poke ((Ps!) a i) φ) (-x)= -poke ((Ps!) b i) (poke ((Ps!) a i) φ) x; rw [show poke ((Ps!) b i) (poke ((Ps!) a i) φ)=_ from pokes_two _ _ _ (anthemBond (ht _) (H:=H i))]; dsimp only; unfold bishops; simp only [map_neg,LinearMap.neg_apply]; ring
end full
end YM.OPE.Shrew
