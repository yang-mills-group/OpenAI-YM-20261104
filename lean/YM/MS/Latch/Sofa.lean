import YangMills.WilsonProof.NativeSupport.YM.MS.Mach.Land
import YM.MS.Fiddle.Tow
/-!
# Line & vertex assembly costs with arbitrary infrared weights and multiple mark number
We do not require periodicity for these estimates, since unfolded momenta proofs later.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Latch
open Set Function Filter Finset Metric Real MeasureTheory
open Plane Koszul Heat Tone Momentum Landau Detect Book High Frame Flux Osc Fiddle Snap City Wire Wind Signal
open scoped Topology ContDiff
variable {G:Gauge}{b c:Bool}{s t h:ℤ}{ι E F J:Type}[NormedAddCommGroup E][NormedSpace ℝ E]
 [NormedAddCommGroup F][NormedSpace ℝ F] {S:Scale ι}{n m:ℕ}{a x v:ι→ℝ}
abbrev Edge (G:Gauge):= Flux (BH G) QP ℂ
abbrev pitch (l:Legs (Mode (BH G) J)): ℤ:= fieldDim wfield l
lemma w_mass {l v w:Legs (Mode (BH G) J)}(h:Split l v w): pitch l+pitch v=pitch w:= split_sum _ h
abbrev Cape (S:Scale ι)(f:ι→Law G)(a:ι→ℝ)(w: Wire (BH G) E QP):= Bound S (Plane.Chart f w) fun i=> S.length i^pitch w*a i
abbrev Sheet (S:Scale ι)(a:ι→ℝ)(K:ι→Edge G): Prop:= ∀ (i j:BH G), Line S (fun _=>Set.univ) (fun t=> K t i j ) fun t=> S.length t ^ ( (4:ℤ)-wfield i-wfield j )* a t
abbrev CourseK (S:Scale ι)(a:ι→ℝ)(K:ι→Edge G): Prop := ∀ (i j:BH G), Bound S (fun t=> K t i j) fun t=> S.length t^( (4:ℤ) - wfield i-wfield j)*a t
-- env all positive w. Course b condition: if c=true require $r>0 irrespective b; c=false include all.
def Lease (b c:Bool)(S:Scale ι)(F:ι→Law G)(a:ι→ℝ): Prop:= ∀ (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E],∀ w:Wire (BH G) E QP, Course b w→ fig c w.length→ Cape S F a w
-- standard constants
variable {w:Wire (BH G) E QP}{f g:ι→Law G}
lemma length_p (t:ℤ)(i:ι):0≤ S.length i^t := zpow_nonneg (S.pos i|>.le) _
lemma Cape.plus (h: Cape S f a w)(hp:Cape S g a w): Cape S (f+g) a w:= Costs.add h hp
lemma Cape.minus (h:Cape S f a w)(hp:Cape S g a w): Cape S (f-g) a w:= Costs.sub h hp
lemma Cape.mote (g:ℂ)(h:Cape S f a w): Cape S (g • f) a w:= h.L ( ContinuousLinearMap.mul ℝ ℂ g )
lemma Cape.zero (h:∀ i,0≤a i): Cape S (0:ι→Law G) a w:= Costs.zero fun i _ _=>mul_nonneg (length_p ..) (h i)
lemma Cape.up (h:Cape S f a w)(ht:∀ i,a i≤x i): Cape S f x w:= h.raise ( Cost.of_le fun i _ _=>mul_le_mul_of_nonneg_left (ht i) (length_p ..))
lemma Cape.sum {f:J→ι→Law G}(U:Finset J)(h:∀ i∈U,Cape S (f i) a w)(ht:∀ i,0≤a i): Cape S (fun i=>∑ j∈U,f j i) a w := by
    classical
    induction U using Finset.induction with| empty=> simp_rw [ Finset.sum_empty ]; exact Cape.zero ht| insert i t hi ih=> simp_rw [Finset.sum_insert hi]; exact Cape.plus (h _ (by simp)) (ih fun j hj=> h j (Finset.mem_insert_of_mem hj)) -- empty under lam needs simp
namespace Lease
lemma zero (h:∀ i,0≤a i): Lease b c S (0:ι→Law G) a:= fun _ _ _ _ _ _=> Cape.zero h
lemma sum (U:Finset J){F:J→ι→ Law G}(h:∀ i∈U,Lease b c S (F i) a)(he:∀ i,0≤a i): Lease b c S (fun i=>∑ j∈U,F j i) a:= fun E _ _ w h1 h2=> Cape.sum _ (fun i ht=> h i ht E w h1 h2) he
lemma plus (h:Lease b c S f a)(he:Lease b c S g a): Lease b c S (f+g) a:= fun E _ _ w h1 h2=> Cape.plus (h E w h1 h2) (he E w h1 h2)
lemma minus (h:Lease b c S f a)(he:Lease b c S g a): Lease b c S (f-g) a:= fun E _ _ w h1 h2=> Cape.minus (h E w h1 h2) (he E w h1 h2)
lemma cash (g:ℂ)(h:Lease b c S f a): Lease b c S (g • f) a:= fun E _ _ w h1 h2=> Cape.mote g (h E w h1 h2)
lemma sticks (h:Lease b c S f a)(ht:∀ i,a i≤x i): Lease b c S f x:= fun E _ _ w h1 h2=> Cape.up (h E w h1 h2) ht
lemma highp (h:Lease b false S f a): Lease b true S f a:= fun E _ _ w h1 _=> h E w h1 (fun z=> Bool.noConfusion z)
lemma snow (h:Lease false c S f a): Lease true c S f a:= fun E _ _ w _ h1=> h E w (fun z=> Bool.noConfusion z) h1
end Lease
lemma polar {f':ι→E→F} (h:Line S (fun _=>Set.univ) (E:=E) (F:=F) f' a): Bound S f' a:= by
   obtain H:= h 0; simp only [pow_zero,div_one] at H; refine ⟨ H.smooth, fun j=>?_⟩; obtain ⟨C,hC,k,hk⟩:= H.quoted j; refine ⟨ C,hC,k,fun i p ht=>( hk i p ht ).trans ?_⟩; have hv := H.nonneg i p ht; have hu:= S.pos i; simp only [ Scale.strict ]; have ht := S.basic_pos i; gcongr; exact le_mul_of_one_le_right ht.le ( S.one_le_weight i p )
end YM.MS.Latch
