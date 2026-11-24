import YM.X.Bend.Motto
/-!
# realness of geometric PT prescriptions with any Buffer (itself commutes by assumption). Endpoint at every k and coeff order, conjugation on real tests.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Bend
open Lattice Wilson Next.Rank Normal LiftMark Crate Porch Rays Shelf Tot Fund
open Maxwell Maxwell.Free Extra.FD MvPolynomial Labels Pert.Position Pert.RawLabels
open Interval Size Filter Function MeasureTheory Set Reed Stems Haze Fielding PertExtension LatticePT Chir Sage Bare Tri Pulse
open Ribbon
open scoped Topology BigOperators Classical
variable {G:Gauge}{F:Labels.Frames G} {d k m:ℕ} {q:ℕ+} {V I:Type*} {r R s:ℝ}
local notation "K"=>(atTop:Filter ℕ)
variable (B:Bare.Shop F) (hq:1<q.val)(hg:G.Simple)
local notation "L"=>Bank F d
local notation "T"=>Test m
variable (t: Test m)
abbrev moral (x:ℂ):Prop:= star x=x
abbrev RealT (t:Test m):Prop:=∀x,moral (t x)
def House (V:Bank F d):Prop:= ∀ {m:ℕ}(t:Test m), RealT t→ ∀ p:Fin m→ E F d,(∀i, (Model F).conj (hierarchy F).spin _ (p i)=p i)→ moral (V m t p)
lemma zero_im {x:ℂ}(h:moral x): x.im=0:= congr_arg Complex.im (Complex.conj_eq_iff_re.mp h)|>.symm -- defeq
lemma lunar (h:RealT t)(F:Fin m→LatticePT.Word G)(q:ℕ+)(n i:ℕ) : moral (Bare.Shop.series F q n t i):= by
    unfold Bare.Shop.series; rw [show Complex.im ∘ ⇑t = (fun _=>0) from funext (fun x=> zero_im (h x)), show Subcell.sweep (fun _ : Points m=>0) (epsilon q n) ∘ points =(fun _=>0) from funext (fun _=> by simp [Subcell.sweep])]; unfold moral; rw [show Mixed.polynomialTop F q n (fun _=>0) i=0 from by simp [Mixed.polynomialTop,Mixed.price]]; simp
lemma ray_coords (i:(F.level d).Index)(x:Label G d)(hx:Labels.realBar x=x): moral ((F.level d).basis.coord i x):= by
    let H:=F.level d; have ht:= Frame.conj_basis H (H.coords x) i; rw [LinearEquiv.symm_apply_apply,hx] at ht; exact ht.symm
lemma venue (d k n:ℕ): House (B.bank q k d n):= by
    intro m t ht p hp; unfold Shop.bank adopt; rw [MultilinearMap.compLinearMap_apply]; unfold offspring; rw [spread_value]; unfold moral;
    simp_rw [star_sum,star_mul,star_prod, show ∀ v:Fin m→LatticePT.Word G, star (Bare.Shop.series v q k t n)=_ from fun w=> lunar t ht ..]; apply Finset.sum_congr rfl; intro i hi; rw [mul_comm (Bare.Shop.series _ _ _ t _)]; apply congr_arg (·* _); apply Finset.prod_congr rfl; intro j _; apply ray_coords; rw [← physical_real (H:=(hierarchy F).spin),hp] -- inspect
lemma motor_house (X : Bank F d)(h:House X)(s:Buffer F d):House (market F s X):= by
     intro m t ht p hp; exact h t ht (frameC F s ∘ p) (fun i=> by simp only [Function.comp_apply]; unfold frameC; simp only [LinearMap.add_apply, LinearMap.id_apply,map_add,bufferL_eq,s.property.2.2.1,hp])
lemma Hcollect : House (0:Bank F d):= fun _ _ _ _=> by exact star_zero ℂ
lemma Hplus (a b:Bank F d)(h:House a)(hb:House b): House (a+b):= by intro m t ht p hp; change star (a m t p+b m t p)=a m t p+b m t p; rw [star_add,show star (a m t p)=_ from h t ht p hp, show star (b m t p)=_ from hb t ht p hp]
lemma Hscale (a:Bank F d)(h:House a) (c:ℝ): House (c • a):= by intro m t ht p hp; change star (c • a m t p)=_; rw [StarModule.star_smul,show star (a m t p)= _ from h t ht p hp, star_trivial];rfl
open Jet hiding Word
lemma sighs (s:ℝ)(w:ℕ→ L)(h:∀ i, House (w i)) : House (delay w k s):= by
   suffices H:∀ T': Finset ℕ,House (∑ i∈T',s^i • w i) by exact @H (Finset.range (k+1))
   intro t; induction t using Finset.induction_on with|empty=>rw [Finset.sum_empty];apply Hcollect|insert i a he hh=> rw [Finset.sum_insert he]; exact Hplus _ _ (Hscale _ (h i) _) hh
lemma morale {a:ℕ→L}{f:ℝ→Bank F d}(h:Appears k f a)(hh:∀i,House (f i)): House (a k):= by
    intro m t ht p hp; let T':Pert.Position.Section F d:= ⟨m,p,t⟩; let C:= (starL' ℝ (A:=ℂ)).toContinuousLinearMap; let g:= lookie F T'; have hk:=h.writes T'; change Act k (g ∘ f) (g ∘ a) at hk; have he := hk.linear («L»:=C); rw [show C ∘ (g ∘ f)=g ∘ f from ?_] at he; -- rw let.Bug
    change C (g (a k))=g (a k); exact he.trans_at hk le_rfl; exact funext fun i=>hh i t ht p hp
lemma θhouse (w:ℕ→Bank F d)(h: ∀ i, House (w i))(b:ℕ→Buffer F d): House (predMarket b w k):= by
   refine morale (f:=fun t=> market F (delay b k t) (delay w k t)) (appears_market (appears_delay w k) (Act.swell b (show k≤k from le_rfl))) ?_; intro t; exact motor_house _ (sighs (k:=k) t w h) _
lemma layout_real (i:ℕ): House (B.uncut hg q k d i):= θhouse _ (venue B d k) _
end YM.PositionX.Bend
