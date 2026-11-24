import YM.SchemeRG11.Outer.Educe
/-! Budget through one nonadjacent weighted (infinite radius) sector. -/
noncomputable section
set_option autoImplicit false
namespace YM.SchemeRG11.Dock
open Function Filter Asymptotics Topology MeasureTheory Metric
open Flock Lattice Pert Align Full Maxwell Haze Pile Catch World Atoll Tree Acorn Outlook Banner
open Labels Long MvPolynomial Air North Wolt Sew
open scoped Classical Pointwise
variable {I:Type*}{G:Gauge} {T: Align.Itinerary}
local notation "D₁"=> Atoll.land G
variable (s:Finset I)(t:Landmarks I)(p:I→ pLabel G)(B:Window){R:ℝ}{z:I→E4}
lemma feed (S:ℕ→ Cover→Prop)(r:ℝ)(ρ:Crawl→ℝ)(V:Crawl→ Cover)(hr: r>0)(h:∀ i∈s, Sew.hops T S r V (fun k=>t i k.1))(he:∀ i∈s,∃ C>0,∀ᶠ j in atTop,∀x,S j x→ |ρ (j,x)| ≤ C * baseU T j (V (j,x)-t i j) ^ 2): Gate.Lots T Prod.fst V ρ (S:=Funds S) (Z:=spanX (G:=G) s (cords T t)):=by
 rintro n a ha w ⟨i,hi,k,hk⟩; subst w; exact spending hr (t i) (fun _=>rfl) (h i hi) ρ ha _ (he i hi)
lemma meal(x:ℕ → Cover)(y:E4)(h:Footpath T t s z)(H:∀i∈s,y ≠ z i)(he:Along T x y): Gate.Lots T _root_.id x (fun _=>1) (S:=Sew.Home) (Z:=spanX (G:=G) s (Scores T t)):=by
 rintro m a hV w ⟨i,hi,q,rfl⟩
 have hx:= intact he (h i hi) (H i hi) hV (Long.high_probe q)
 simp only [one_mul,Scores,lens_l]; exact hx
abbrev directV (i j:Axis)(k:ℕ)(v:Cover):ℝ:= (T.gap k)^(-4:ℤ)*(D₁).avg (Tree.cost v i j * aerial s (fun a=>castZero (T.gap k) (p a)) (fun a=>t a k))
def external (i j:Axis)(T:Align.Itinerary):Slate:=rest T B s t * directV s t p i j (T:=T)
variable [DecidableEq I]
lemma jugP (h:Footpath T t s z)(hp:Spaced R z s)(hR:R>0)(j k:Axis) (S:ℕ→ Cover→Prop)(ρ:Crawl→ℝ)(H:Gate.Lots T Prod.fst Prod.snd ρ (S:=Funds S) (Z:=spanX (G:=G) s (cords T t))) : (fun x:Crawl=> ρ x^3*directV s t p j k (T:=T) x.1 x.2)∈ Funds S:=by
 have he:= sailgate (D₁) (cords T t) (Funds S) (spanX s (cords T t)) s (fun i hi u=> ⟨i,hi,u,rfl⟩) (chair t s z h (hp.distinct hR)) p _ (Gate.crust T j k _ _ ρ H Gate.unitG)
 convert he using 1; funext x; rw [directV,rocket, mul_one,map_smul, smul_mul_assoc, map_smul, show (D₁).neg.heat (Tree.cost x.2 j k)=Tree.cost x.2 j k from Acorn.vapid _ _ _ _ (fun i b e=> by simp only [Haze.Dose.neg,Atoll.land,not_and_of_not_left _ e,↓reduceIte,neg_zero])]; simp only [smul_eq_mul,mul_assoc];rfl
lemma jars (h:Footpath T t s z)(hp:Spaced R z s)(hR:R>0)(j k:Axis)(x:ℕ → Cover){y:E4}(H:∀i∈s,y ≠ z i)(he:Along T x y): Finishes (fun i=>directV s t p j k (T:=T) i (x i)):=by
 have hx:= sailgate (D₁) (Scores T t) Sew.Home (spanX s (Scores T t)) s (fun i hi u=>⟨i,hi,u,rfl⟩) (reachPrice s t z h (hp.distinct hR)) p _ (Gate.crust T j k _ _ _ (meal s t x y h H he (G:=G)) Gate.unitG)
 change Finishes _ at hx; convert hx using 1 -- Prop issue
 funext i; rw [directV,rocket,mul_one,map_smul,smul_mul_assoc,map_smul]; have hh: (D₁).neg.heat (Tree.cost (x i) j k)=Tree.cost (x i) j k:=Acorn.vapid _ _ _ _ (fun i b e=> by simp only [Haze.Dose.neg,Atoll.land,not_and_of_not_left _ e,↓reduceIte,neg_zero]); rw [hh]; simp
lemma ship (h:Footpath T t s z)(hp:Spaced R z s)(hR:B.rOut<R)(j k:Axis): ∃ C>0,∀ᶠ i in atTop,∀ x, |external s t p B j k T i x| * (baseU T i x+1)^6 ≤ C:=by
 let r:=B.rIn/2; have hr:r>0:=half_pos B.rIn_pos
 let S(i:ℕ)(x:Cover):Prop:=rest T B s t i x≠0
 let ρ(x:Crawl):=(baseU T x.1 x.2+1)^2
 have hv(i:I)(hi:i∈s): hops T S r Prod.snd (fun x=>t i x.1):=(away_h B s t h hp hR).mono (fun a H x hx=> by contrapose! hx; exact H _ _ hi hx.le) -- hx.le near
 have H:Gate.Lots T Prod.fst Prod.snd ρ (S:=Funds S) (Z:=spanX (G:=G) s (cords T t)):=by
    apply feed s t S r ρ Prod.snd hr hv; intro i hi; obtain ⟨C,hC,H⟩:=sidecar (h i hi)
    let E:= C+1; refine ⟨(1+E/r)^2,by unfold E; positivity,?_⟩; filter_upwards [hv i hi,H] with j hh hk x hp; unfold ρ; rw [abs_of_nonneg (sq_nonneg _),← mul_pow]; have hc : r ≤ baseU T j (x-t i j):= hh x hp; have ht:= abs_z T j x (t i j); dsimp only
    have hm :0< baseU T j x:= mul_pos (T.positive _) (World.d_pos _)
    gcongr
    calc _≤ baseU T j (x-t i j)+E:=by unfold E;linarith only [ht,hk]
         _≤ _:=by rw [add_mul,one_mul]; gcongr; rw [div_mul_eq_mul_div];apply (le_div_iff₀ hr).mpr; unfold E; gcongr
 have hr' : (fun x:Crawl=> rest T B s t x.1 x.2)∈ Funds S:=by obtain ⟨C,hC,H⟩:= (show Worth (fun i p=>True) (fun v=>rest T B s t v.1 v.2) from rest_pow B s t T); exact ⟨C,hC,H.mono fun i hi x _=> hi x trivial⟩ -- implicit
 obtain ⟨C,hC,H'⟩:= (Funds S).mul_mem hr' (jugP s t p h hp (B.rOut_pos.trans hR) j k S ρ H) -- expand Worth
 refine ⟨C,hC,?_⟩; filter_upwards [H'] with i hx x; by_cases hv:S i x
 · apply le_trans _ (hx _ hv); refine le_of_eq ?_; unfold external; simp only [Pi.mul_apply,abs_mul,ρ]; have hf:0≤ (baseU T i x+1)^2:=sq_nonneg _; simp only [abs_of_nonneg (pow_nonneg hf 3)]; ring
 unfold external; change |rest T _ _ _ _ _ * _| * _ ≤ _; rw [show rest T B s t i x=0 from not_ne_iff.mp hv,zero_mul,abs_zero,zero_mul]; exact hC.le
lemma ready(j k: Axis)(X:ℕ → Cover)(y:E4)(h:Footpath T t s z)(e:Spaced R z s)(hp:B.rOut<R)(hx:Along T X y): Finishes (fun i=> external s t p B j k T i (X i)):=by
 by_cases H: ∀i∈s,y≠ z i
 · exact (far_finish B s t X h hx).mul (jars s t p h e (B.rOut_pos.trans hp) j k X H hx)
 push Not at H; obtain ⟨a,ha,rfl⟩:=H
 apply (Finishes.const 0).same; filter_upwards [far_cove B s t X h e hp a ha hx] with i hi; unfold external; simp [hi]
end YM.SchemeRG11.Dock
