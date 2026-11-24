import YM.OPE.Compatible.Gables.Live
/-!
# polynomial conditional μ. display beams
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Libra.Shift
open Function Filter MeasureTheory Module
open scoped Topology BigOperators ComplexConjugate Classical ContDiff RealInnerProductSpace ENNReal
open Next.Free Bloch PertExtension Series Asymptotics GaussianScore Radial Finset Flock Coin Lattice Laurent RG Precision Flume Script Page Planned.PrimaryIntegral295.Carrier Matrix JetS ScriptJ Shell
variable {I J E F:Type} [Fintype I] [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E](μ:Measure E)[μ.IsAddHaarMeasure](L:Law E)
section pair
variable [NormedAddCommGroup F][NormedSpace ℝ F][FiniteDimensional ℝ F][MeasurableSpace F][BorelSpace F] (ν:Measure F)[ν.IsAddHaarMeasure] (Q:Law F)
omit [FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E][FiniteDimensional ℝ F][MeasurableSpace F][BorelSpace F] in lemma leanB (p:F×E→ℝ)(h:Bond p)(x:F):Bond (fun v:E=> p (x,v)) := h.comp fun f=>by
    let A:=LinearMap.inr ℝ F E; have hp (v:E): f (x,v)= f (x,0)+(f.comp A) v:=by rw [show (x,v)=(x,0)+(0,v) by simp,map_add]; rfl
    exact (funext hp).symm ▸ (Bond.add (Bond.keep (f (x,0))) (Bond.glyph (f.comp A)))
-- marginal polynomial in F. induction factoring exponent
omit [MeasurableSpace F][BorelSpace F] in
lemma retake (p: F×E→ℝ)(h:Bond p): Bond fun x:F=> L.average μ (fun y:E=> p (x,y)):=by
       apply Quilting.everything _ p h (g:=fun p=>Bond fun x:F=> L.average μ (fun y:E=>p (x,y))); refine ⟨fun s=> ?_,fun p hp hx c=>?_, fun p q hp ht hx he=>?_⟩
       · -- multiply by anything of y
         suffices H:∀ (h:E→ℝ),Bond h→Bond (fun x:F=>L.average μ (fun y:E=>dotV s (x,y)*h y)) by simpa only [Pi.one_apply,mul_one] using! H 1 Bond.one
         induction s with
         | nil=>intro h hh; exact (Bond.keep (E:=F) (L.average μ (fun y:E=> 1*h y)))
         | cons a s ih=>
           intro p hp; let A:= a.comp (LinearMap.inl ℝ _ _); let B:= a.comp (LinearMap.inr ℝ _ _); have hz (x:F)(y:E): a (x,y)=A x+B y:=by rw [show (x,y)=(x,0)+(0,y) by simp, map_add];rfl
           let U(x:F)(y:E):=dotV s (x,y)*p y; let V:= (B:E→ℝ)*p; let T(x:F)(y:E):=dotV s (x,y)* V y; have ha:Bond V:=(Bond.glyph B).mul hp; have hv(x): Bond (fun y:E=>dotV s (x,y)):=leanB _ (bonded s) x
           have hh(x:F) : L.average μ (fun y:E=>dotV (a::s) (x,y)*p y)= A x*L.average μ (U x)+L.average μ (T x):=by rw [show (fun y:E=> _)=(A x • (U x)+(T x)) from ?_,sun μ L (u:=A x • U x) (v:=T x) (Bond.scale _ ((hv x).mul hp)) ((hv x).mul ha),scooted];funext i; rw [dot_cons,Pi.mul_apply,hz]; simp only [T,U,V,Pi.add_apply,Pi.smul_apply,Pi.mul_apply,smul_eq_mul]; ring
           exact (funext hh).symm ▸ (((Bond.glyph A).mul (ih p hp)).add (ih V ha))
       · simp_rw [show ∀ f:F,L.average μ (fun y:E=>(c • p) (f,y))= c* L.average μ (fun y:E=>p (f,y)) from fun i=>scooted ..]; exact Bond.scale _ hx
       simp_rw [show ∀ f:F, L.average μ (fun y:E=>(p+q) (f,y))= _ from fun i=>(show L.average μ (fun y:E=>(p+q) (i,y))= L.average μ (fun y:E=>p (i,y))+L.average μ (fun y:E=>q (i,y)) from sun μ L (leanB p hp i) (leanB q ht i))]; exact hx.add he
-- Token average
abbrev crossT (p:F×E→ Token)(x:F): Token:= draw (fun y:E=>p (x,y)) L μ
omit [MeasurableSpace F][BorelSpace F] in
lemma crossB (p:ScriptJ (F×E))(h:p.B): ScriptJ.B (crossT μ L p):=by obtain ⟨a,b,c⟩:= bondX h; exact Xbond (retake μ L _ a) (retake μ L _ b) (retake μ L _ c)
lemma guest (p:ScriptJ (F×E))(h:p.B): draw p (united Q L) (ν.prod μ)= draw (crossT μ L p) Q ν:=by obtain ⟨a,b,c⟩:= bondX h; apply eta; exact harvested ν μ Q L _ a; exact harvested ν μ Q L _ b; exact harvested ν μ Q L _ c
end pair
omit [FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E] in
lemma mintInv (p:ScriptJ E)(h:p.B)(hp:∀ i,(p i).s=1): ScriptJ.B (fun i=>(p i)⁻¹):=by
     obtain ⟨ha,hV,hh⟩:= bondX h; apply Xbond
     · simp_rw [sp_s,hp,inv_one]; exact Bond.keep 1
     · simp_rw [sp_l,hp]; simpa using! hV.neg
     simp_rw [sp_h,hp]; simpa only [one_pow, div_one] using! ((hV.pow 2).sub hh)
lemma headD (x: E→Token)(hp:∀ i,(x i).s=1):(draw x L μ).s=1:=by unfold draw; dsimp only; simp_rw [hp];exact singleConst ..
end YM.OPE.Libra.Shift
