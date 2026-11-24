import YM.OPE.Compatible.Loire.Land
/-!
# No first order logarithmic dilation! Stage for any Ward pol certificate at arbitrary weight. Ratios and ell purchased once, within the chosen geometric orbit.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Shrew
open Function MeasureTheory Set Topology Metric Filter Lattice Laurent Wilson Exterior Cascade PertExtension Series Score Next.Foundations Matrix
open Next.Free Frequency Bloch MSbar.Tree MSbar.Tree.Resolvent Terp Stubble Weir
open GaussianScore Libra WithLp RG Precision Votive Glass Radial Flume.Script Flock StageLight Balsam Nestle
open scoped BigOperators Classical ContDiff Matrix.Norms.Frobenius RealInnerProductSpace
attribute [local instance] Gauge.frobInner
variable {n:Side}{G:Gauge}{C:RG.KernelChoices}{P:ChartRatio G}{U:Gloam}{d:ℕ}
variable {i:ℕ}{l b:ℝ}{B:Sponsor G} {Q:Seasons B}{A:Alps B Q i l}
variable {h:4 ≤ i}
lemma payoff {M:Even n.val}(p:ScriptJ (Keys G (Limb M))) (X:Lit M A b)(ht:A.gear=Train.top i)(hp:Track A n)(V:LocalRatio P)(hG:G.Simple)(B₀:Bond (fun x=>(p x).s))(B₁: Bond (fun x=>(p x).l)):
     let f:=fun x=>(p x).s; let w:=fun x=>(p x).l
     let W:=Chart.tangent G (Limb M); let L:= boost M (Train.top i) h B.K (G:=G)
     (X.s.pay P p).s=L.average W f∧ (X.s.pay P p).l=L.average W w-L.average W (f*Trill (anthem G M)) := by
   intro f w W L
   have hs(u:Keys G (Limb M)): jet X.s.f 2 u= L.P u u/2:=by
       rw [show jet X.s.f 2 u= _ from (by unfold jet; rw [(X.uplift.iteratedFDeriv ℝ 2).eq_of_nhds] : jet X.s.f 2 u = jet (mural M A-(fun _=>mural M A 0)+hippie M) 2 u), Lit.lip M A u h, ht] -- ht dependent
   let Θ:=Trill (anthem G M); have hu:Bond Θ:= anthemBond hp; rw [Lid.cutOut X.s V _ _ hs]; let a:=X.s.hat P; change (Libra.draw (p*a) L W / Libra.draw a L W).s= _∧ (Libra.draw (p*a) L W/Libra.draw a L W).l=_
   have hg(x):(a x).s=1:=X.s.hat_full V _; have hy(x):(a x).l= -Θ x:=by rw [show _=_ from price_ink X hG V hp x]; change _= -( (G.colorScale^2*8)⁻¹ * scribeX (exclaim M x) (exclaim M x) (exclaim M x)); ring
   have hh:(Libra.draw a L W).s=1:=by change L.average W (fun x=> (a x).s)=1; simp_rw [hg]; exact L.empty _
   have ha:(Libra.draw a L W).l=0:=by change L.average W (fun x=>(a x).l)= _; simp_rw [hy]; rw [show (fun x=> -Θ x)=(-1:ℝ) • Θ from funext fun x=>by simp,scooted, colorful W L Θ hu (trill_neg (anthem G M))];ring
   have hf:(Libra.draw (p*a) L W).s=L.average W f:=by unfold Libra.draw;dsimp only; simp_rw [Pi.mul_apply,JetS.ml_s,hg,mul_one];rfl
   simp only[JetS.dv,JetS.ml_s,JetS.ml_l,JetS.sp_s,JetS.sp_l,hh,ha,inv_one,hf]; simp only [mul_one,neg_zero,mul_zero,zero_div,zero_add,true_and];
   change L.average W _=_; rw [← snow W L (f:=w) (g:=f*Θ) B₁ (B₀.mul hu)]; congr 1; ext x; simp_rw [Pi.mul_apply,JetS.ml_l, hy,hg]; rw [Pi.sub_apply]; unfold w f Θ; rw [Pi.mul_apply]; ring
section
variable (H:∀ p,Even (U.M p).val)
local notation "W"=> (fun p:ℕ=> Chart.tangent G (Limb (H p)))
local notation "Θ"=> (fun p:ℕ=> boost (H p) (Train.top i) h B.K (G:=G))
local notation "Vp"=> IpT H G
-- I chosen existentially: restrict Type
inductive Vine (d:ℕ): Vp→ Prop where
| herm {I:Type}[LinearOrder I] (s:Finset I) (A:I→Match U G)(h:Wood A s)(hk:bud s (wool A)=d): Vine d (fun i=> fauna (ship A) (fun j=>ps (A j) i (H i)) s)
| smul {f} : ∀ c:ℝ, Vine d f→ Vine d (c•f)
| add {f g} : Vine d f → Vine d g → Vine d (f+g)
lemma vineCharge {f:Vp}(hp: Vine H d f)(j:ℕ):Bond (f j):=by induction hp with | herm=>exact incense ..| smul c _ h=>exact h.scale _| add _ _ I O=>exact I.add O
lemma leadingPull {f:Vp}(hf:Vine H d f):∃ c,Bloom U d (fun i=> (Θ i).average (W i) (f i)) c:=by
    apply fromCore; induction hf with
    | @herm I _ s A hA hk=>
       obtain ⟨C,h'⟩:=grime (μ:=W) (L:=Θ) (d:=wool A) (K:=ship A) (A:=fun i a=> ps (A a) i (H i)) (U:=U) s (fun a ha b hb h'=>embark H _ _ (hA a ha b hb h') h)
       rw [← hk]; exact h'.2.1
    | smul c hb ih=> convert! (ih.glu (c • ContinuousLinearMap.id ℝ ℝ)) using 2 with i; rw [Pi.smul_apply,scooted]; simp ;ring
    | add hf hg Ih Ip=> convert! Ih.fuse Ip using 2 with j; rw [Pi.add_apply,sun (W j) (boost (H j) (Train.top i) h B.K) (vineCharge H hf j) (vineCharge H hg j),mul_add];rfl
lemma bodyP {f:Vp}(ht:Vine H d f)(hs:A.gear=Train.top i)(hG:G.Simple)(hp:∀ i,Track A (U.M i)): Fruit U d (fun i=>(Θ i).average (W i) (f i*Trill (anthem G (H i)))) 0:=by
    induction ht with
    | @herm I inst s X he hk=>
       have hh:= wick_quill H X h s he hG hs hp s (Finset.Subset.refl ..); rw [zero_add,hk] at hh; exact hh
    | @smul f c hs1 ht=> have he:=Nestle.payScalar c ht; rw [mul_zero] at he; convert! he using 2 with j; rw [Pi.smul_apply,smul_mul_assoc,scooted]
    | @add f g hf hg hh hu=> have he:=hh.sum hu; rw [add_zero] at he; convert! he using 2 with j; change (boost (H j) (Train.top i) h B.K).average _ ((f j+g j)*_)= _; rw [add_mul,sun ((W) j) (boost (H j) (Train.top i) h B.K) ((vineCharge H hf j).mul (anthemBond (hp j))) ((vineCharge H hg j).mul (anthemBond (hp j)))]; rfl
lemma apt (S:(i:ℕ)→ Lit (H i) A b)(x:(i:ℕ)→ScriptJ (Keys G (Limb (H i))))(hk:Vine H d (fun i v=>(x i v).s))(hx:Tar H (fun i v=>(x i v).l))(hs:A.gear=Train.top i)(hp:∀ i,Track A (U.M i))(ht:LocalRatio P)(hg:G.Simple)(h:4≤ i) :
    (∃ c,Bloom U d (fun i=> ((S i).s.pay P (x i)).s) c) ∧ Fruit U d (fun i=> ((S i).s.pay P (x i)).l) 0 :=by -- power demand k etc
    have he j:=payoff (h:=h) (x j) (S j) hs (hp j) ht hg (vineCharge H hk j) (Tar_bond H hx j)
    constructor
    · simp_rw [fun i=> (he i).1]; exact leadingPull H hk
    let Γ(j):= boost (G:=G) (H j) (Train.top i) h B.K; let g i:=(Γ i).average (W i) (fun y=>(x i y).l); let f i:= (Γ i).average (W i) ((fun y=>(x i y).s)*Trill (anthem G (H i))); have hp:Fruit U d f 0:=bodyP H hk hs hg hp; have hv:Fruit U d g 0:= (taxes H h hx).sap
    rw [show (fun i=> ((S i).s.pay P (x i)).l)=g+(fun i=> -1*f i) from funext fun i=>by rw [(he i).2];change _-f i=g i+ _; change g i-_= _;ring, ← add_zero (0:ℝ)]; exact hv.sum (by simpa only[mul_zero] using (Nestle.payScalar (-1) hp))
end
end YM.OPE.Shrew
