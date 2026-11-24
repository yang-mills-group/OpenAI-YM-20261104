import YM.SchemeConversionRG11.FirstW.Fold.Chip
/-! Covariance imaging and CT local-algebra evaluation. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW.Deck
open Function MeasureTheory Filter Set Lattice Pert Align Position Maxwell RawLabels MvPolynomial Warp SchemeConversionRG11
open scoped BigOperators Classical Topology Matrix
variable {G:Gauge}{F:Labels.Frames G}{n:Side}{r:ℕ} {T:Itinerary}
def radar (o:Full.Grid n r)(t:ℝ)(a b:At G r 6): ℝ:= tape a.2.val t (o a.1) (arise t o b)
-- use the cover patch pull form at height m without rounding boundary breaking. equality eventually to tor pointwise soft budgets.
def deckP (n : Side)(v : Site n)(P:Sky G ℤ) : Sky G (Per n) where
 toFun A:= ((P (terms v A)).compl₂ (terms v)).comp (terms v)
 map_add' A B:= by apply LinearMap.ext; intro x; apply LinearMap.ext; intro y; simp
 map_smul' t x:= by apply LinearMap.ext; intro y; apply LinearMap.ext; intro z; simp
lemma floor_at (n:Side)(x:Site n)(k:Who G 6) : terms x (canal k.val x)= tin G n k:=by
 have ha:= consumes x x k.val
 rw [sub_self] at ha; unfold tin; rw [← ha]; apply _root_.funext; intro t; simp only [terms,tracing,LinearMap.pi_apply,LinearMap.proj_apply,add_zero]
lemma sector_cut (x:Site n)(a b:Who G 6)(R:Sky G ℤ)(t:ℝ)(T:FullT G n) :
    sectorA (torT n 6 t x) t x (deckP n x R) a b T = (t^fee a)⁻¹*(t^fee b)⁻¹ * sectorA (tin G n) 1 0 R a b (terms x T) := by
 let f(s:Who G 6):= (t^fee s)⁻¹; let A:=canal a.val x; let B:=canal b.val x
 have hv : deckP n x R A B T=R (tin G n a) (tin G n b) (terms x T) := by change R (terms x A) (terms x B) (terms x T)=_; rw [show terms x A = _ from floor_at n x a, show terms x B=_ from floor_at n x b]
 have hh : echoAt x a.val B T= echoLeg 1 0 a.val (tin G n b) (terms x T):=by rw [echoLeg,one_pow,inv_one,one_smul,← floor_at n x b,echo_wrap,map_zero,zero_add]
 rw [sector_eq,sector_eq]; unfold torT river A B at *
 simp only [map_smul,LinearMap.smul_apply,smul_eq_mul,hv]; rw [←hh,echoLeg]; simp only [LinearMap.smul_apply,smul_eq_mul]; unfold fee; ring
variable (s: Fin r)(o:Full.Grid n r)(h:ℝ)
def radX (d:ℕ)(t:At G r d) := terms (o s) (arise h o t)
lemma radar_val (a:Who G 6)(b:At G r 6): radar o h (s,a) b = (h^fee a)⁻¹ * native a.val 0 (radX s o h 6 b) := by
 unfold radar; rw [tape_scales]; unfold radX; rw [native_wrap,map_zero,zero_add]; simp only [fee,LinearMap.smul_apply,smul_eq_mul]
-- substitution evaluated in *each bond* inside actual galaxy, other cutoff series needs compatibility later
lemma glist_city (k:E F 6)(i:ℕ)(o:Full.Grid (T.period i) r)(a b:At G r 6)(Q:Wash):
    glist k o (T.gap i) (deckP _ (o s) (wheelS G T i Q)) (radar o (T.gap i)) s a b=(T.gap i)^(-6:ℤ) • saleF T i Q k (radX s o (T.gap i) 6 a) (radX s o (T.gap i) 6 b):=by
 unfold glist saleF; rw [burn_eq]; simp only [Finset.smul_sum]; apply Finset.sum_congr rfl; intro u _; apply Finset.sum_congr rfl; intro w _; apply Finset.sum_congr rfl; intro z _
 rw [sector_cut, radar_val]; by_cases ht:root3 (cloak F k) u w z=0; · simp [ht]
 obtain ⟨hx,hB,H⟩:=top_six F k u w z ht; simp only [hx,H,hB,Complex.real_smul];
 rw [show T.gap i^(-6:ℤ)=(T.gap i^2)⁻¹*((T.gap i^2)⁻¹*(T.gap i^2)⁻¹) from by have he:=T.positive i; field_simp]; unfold native radX; push_cast; ring
private lemma swivel {I:Type*}(S:Finset I)(H f:I→I→ℂ)(v:ℝ)(h:∀ a b,H a b=H b a): ∑ a∈S,∑ b∈S,(v • f a b)*H a b = ∑ a∈S,∑ b∈S,(v • ((2:ℂ)⁻¹*(f a b+f b a)))*H a b := by
 let A a b:= (v • f a b)* H a b; let B:=∑ a∈S,∑ b∈S,A a b
 have e(a b): (v • ((2:ℂ)⁻¹*(f a b+f b a)))*H a b = (1/2:ℂ)*(A a b+A b a):=by unfold A; rw [h a b]; simp only [Complex.real_smul]; ring
 change B=_; simp_rw [e, ←Finset.mul_sum, Finset.sum_add_distrib]
 have hv : (∑ a∈S,∑ b∈S,A b a)=B:=Finset.sum_comm
 rw [hv,show (∑ a∈S,∑ b∈S,A a b)=B from rfl]; ring
lemma trestle_city (p:Players G r 6)(k:E F 6)(i:ℕ)(o:Full.Grid (T.period i) r)(Q:Wash):
    trestle k o (T.gap i) (deckP _ (o s) (wheelS G T i Q)) (radar o (T.gap i)) s p=∑ a∈apart G 6 s,∑ b∈apart G 6 s,((T.gap i)^(-6:ℤ) • dew T i Q k (radX s o (T.gap i) 6 a) (radX s o (T.gap i) 6 b))*ZeroR o (T.gap i) (dict b (dict a (air p s))) := by
 let f:= fun a b=> saleF T i Q k (radX s o (T.gap i) 6 a) (radX s o (T.gap i) 6 b)
 let H:= fun (a b:At G r 6)=>ZeroR o (T.gap i) (dict b (dict a (air p s)))
 unfold trestle; simp_rw [glist_city s k,dew_val]
 have he(a b:At G r 6): H a b=H b a:=by unfold H; rw [dict_comm]
 have hx:=swivel (apart G 6 s) H f (T.gap i ^(-6:ℤ)) he
 unfold H f at hx; exact hx
lemma echo_rows (p:Players G r 6)(K:E F 6)(h0:0<h)(q: Pack F): echoesP p o h s (cloak F ((twistC h q).val K)) (radar o h)=∑ a∈apart G 6 s,∑ b∈apart G 6 s,(h^(-6:ℤ) • chord (radX s o h 6 a) (radX s o h 6 b) (Full.sections _ _ (q.val K)))*ZeroR o h (dict b (dict a (air p s))) := by
 unfold echoesP; apply Finset.sum_congr rfl; intro a _; apply Finset.sum_congr rfl; intro b _; apply congrArg (· * _)
 rw [← stretch, ballots _ (by rw [stretch]; exact (suitsP q).sees K),ball_val]; simp only [Finset.smul_sum]; apply Finset.sum_congr rfl; intro x _; apply Finset.sum_congr rfl; intro y _; rw [copaid,radar_val,radar_val]; simp only [Complex.real_smul,Complex.ofReal_mul]; change _ = _ * ((1/2*loot _ x y) * (↑(native x.val 0 (radX s o h 6 a)) * ↑(native y.val 0 (radX s o h 6 b))))
 push_cast; have hx : (h:ℂ) ≠ 0:= Complex.ofReal_ne_zero.mpr h0.ne'; field_simp
end YM.RG11.FirstW.Deck
