import YM.SchemeRG11.Plate.Total
import YM.SchemeRG11.Cover.Value
/-! Volume near contribution at joint offsets. -/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeRG11.Acorn
open Lattice Function Filter Haze Pert Bare Labels Bark MvPolynomial Tree Catch Cellular Full Atoll Pile Align Tile
open MeasureTheory ProbabilityTheory
open scoped Classical ContDiff Topology
variable {G : Gauge} {N : Side}
lemma medium_add {T:Itinerary} {p q : ℕ→Cover}(hp:Medium T p)(hq:Medium T q): Medium T (fun i=> p i+q i):=by
 obtain ⟨s,hs⟩:=hp; obtain ⟨t,ht⟩:=hq; refine ⟨s+t+1,?_⟩
 filter_upwards [hs,ht,T.cutoff.eventually (gt_mem_nhds (show (0:ℝ)<1/2 from by norm_num))] with i hi hj hx
 simp only [zpow_neg,zpow_natCast] at *
 have ha:= T.positive i
 have hu (s:ℕ): 1≤(T.gap i ^s)⁻¹:= one_le_inv_iff₀.mpr ⟨pow_pos ha _,pow_le_one₀ ha.le (by linarith)⟩
 have hv :2≤ (T.gap i)⁻¹ := by have := (inv_le_inv₀ (show (1/2:ℝ)>0 from by norm_num) ha).mpr hx.le; norm_num at this; exact this
 rw [pow_succ,pow_add,mul_inv,mul_inv]
 let B := (T.gap i ^s)⁻¹*(T.gap i ^t)⁻¹
 apply le_trans (add_le_add_left (show (diam (p i+q i):ℝ)≤diam (p i)+(diam (q i):ℝ) by exact_mod_cast diam_add (p i) (q i)) (1:ℝ))
 have he1 : (T.gap i ^ s)⁻¹ ≤ B:=by unfold B; nlinarith only [hu s,hu t]
 have he2 : (T.gap i ^ t)⁻¹ ≤ B:=by unfold B;nlinarith only [hu t,hu s]
 nlinarith only [he1,he2, hu s, hi,hj,hv]
lemma medium_sub {T:Itinerary} {p q : ℕ→Cover}(hp:Medium T p)(hq:Medium T q): Medium T (fun i=> p i-q i):=by simpa only [sub_eq_add_neg] using medium_add hp (show Medium T (fun i=>-(q i)) from (by simpa only [Medium,diam_neg] using hq))

def Interior(T:Itinerary)(o:StepPath T):Prop:=∃ c> (0:ℝ),∀ᶠ i in atTop,c*((T.period i).val:ℝ) ≤ (pdist (o i+o i):ℝ)
lemma ocells {T:Itinerary}{o:StepPath T}(hi:Interior T o){p:ℕ→Cover}(hp:Medium T p): Flat T (fun i=> thread (wrap _ (p i)+(o i+o i))) :=by
 obtain ⟨c,hc,H⟩:=hi
 let N i:ℝ:=(T.period i).val
 let z (i:ℕ):= wrap _ (p i)+(o i+o i)
 have ha :∀ᶠ i in atTop,(c/2)*N i ≤ pdist (z i):=by
   have hh:=hp.unwrap
   obtain ⟨j,hj⟩ :=hp
   filter_upwards [H,hj,(T.huge j).eventually (eventually_gt_atTop (2/c)),hh] with i hS hP hT hu
   let p':= wrap (T.period i) (p i)
   have e : pdist (p':Site _)=diam (p i):=by unfold p'; rw [← diam_lift,hu]
   have hw : pdist (o i+o i) ≤ pdist (z i)+diam (p i):= calc
    _ = pdist (z i + -p'):=by unfold z p'; congr 1; abel
    _ ≤ _ := by simpa only [pdist_neg,e] using pdist_triangle (z i) (-p')
   have hb : (diam (p i):ℝ) ≤ (c/2)*N i:=by
     let b := (T.gap i)^j
     have hb:0<b:=pow_pos (T.positive _) _
     have hd:(diam (p i):ℝ)≤ b⁻¹:=by rw [zpow_neg,zpow_natCast] at hP; exact le_trans (by linarith : _ ≤ diam (p i) + (1:ℝ)) hP
     have he: (2/c) < N i*b:=hT
     apply hd.trans; apply le_of_mul_le_mul_right _ hb; rw [inv_mul_cancel₀ hb.ne']; have hh:=(div_lt_iff₀ hc).mp he; linarith only [hh]
   have hJ : (pdist (o i+o i):ℝ) ≤ pdist (z i)+(diam (p i):ℝ) :=by exact_mod_cast hw
   change c*N i≤_ at hS
   linarith
 obtain ⟨K,hK,H⟩:= far []
 intro d
 let r i := T.gap i ^d
 apply tendsto_zero_iff_norm_tendsto_zero.mpr
 refine squeeze_zero' (Eventually.of_forall fun i=>norm_nonneg _) (g:=fun i=> K*(c/2)⁻¹^2 * ((N i)*(r i))⁻¹*(N i)⁻¹) ?_ ?_ -- replace
 · filter_upwards [ha] with i hh
   specialize H (z i); change |thread (z i)| * ((pdist (z i)+1:ℝ))^2 ≤ K at H
   have hp:0<N i:=by unfold N; positivity
   have ht:=T.positive i
   have hx: |thread (z i)| * ((c/2)*N i)^2 ≤ K:= le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith only [hh]) _) (abs_nonneg _)) H
   simp only [zpow_neg,zpow_natCast,norm_mul,Real.norm_of_nonneg (by positivity:0≤ (T.gap i ^ d)⁻¹)]; change _ * |thread (z i)| ≤ _
   apply (mul_le_mul_of_nonneg_left ((le_div_iff₀ (show 0<((c/2)*N i)^2 by positivity)).2 hx) (show 0≤ (T.gap i ^ d)⁻¹ by positivity)).trans_eq
   unfold r; field_simp
 have hb : Tendsto (fun i=> ((N i)*(r i))⁻¹) atTop (𝓝 0):=tendsto_inv_atTop_zero.comp (T.huge d)
 have ht : Tendsto (fun i =>(N i)⁻¹) atTop (𝓝 0):=tendsto_inv_atTop_zero.comp (unitPeriod T)
 simpa using (hb.const_mul (K*(c/2)⁻¹^2)).mul ht
lemma capLand(a b:ℕ→Shaft G):Capped (fun i=> (land G).pulse (a i) (b i)):=by
 obtain ⟨C,hC,H⟩:=Catch.payment (D:=[]) -- name conflict?
 refine ⟨C,Eventually.of_forall ?_⟩; intro i
 unfold land; dsimp only; split
 · next he=> specialize H ((a i).1.1-(b i).1.1); exact le_trans (le_mul_of_one_le_right (abs_nonneg (coverLine _)) (one_le_pow₀ (show 1≤(diam _+1:ℝ) from by have := Nat.cast_nonneg (α:=ℝ) (diam ((a i).1.1-(b i).1.1)); linarith))) H
 simpa using hC.le
variable {I J : Type*}[DecidableEq I]
def rise(c:Cover)(p:Shaft G): Shaft G := ((p.1.1+c,p.1.2), p.2)
def cross(c:Cover) : vellum G→ₐ[ℝ] vellum G:=rename (rise c)
lemma vapour (p:vellum G)(x:Cover)(o:Site N): adsorb o (cross x p)= adsorb (wrap _ x+o) p:=by apply DFunLike.congr_fun (f:=(adsorb o).comp (cross x)) ?_ p; ext1 i; simp only [cross,adsorb,AlgHom.comp_apply,rename_X]; change MvPolynomial.X (R:=ℝ) (veil _ (rise x i)) = _; unfold rise veil; simp only [map_add,add_assoc]
variable {T:Itinerary}{o:StepPath T}
lemma mist {p q:Shaft G}{a b:ℕ→Cover}(hi: Interior T o)(ha:Medium T a)(hb:Medium T b):
 Flat T (fun i=> (spray G _).pulse (veil (o i) (rise (a i) p)) (veil (o i) (rise (b i) q)) - (land G).pulse (rise (a i) p) (rise (b i) q)):=by
 simp only [spray_eq,veil, rise,land]
 split
 · next he=>
    let v i:=q.1.1+b i; let u i:=p.1.1+a i; let w i:=v i+u i+step p.1.2
    have hv : Medium T v:=medium_add (Medium.constant T _) hb
    have hu : Medium T u:=medium_add (Medium.constant T _) ha
    have hm : Medium T w:=(medium_add hv hu).shift _
    apply sameF ((shrink (medium_sub hv hu)).sub (ocells hi hm))
    filter_upwards with i
    change (thread (wrap _ (v i-u i))-coverLine _)-thread (wrap _ (w i)+(o i+o i))=_
    rw [show coverLine (v i-u i)=coverLine (u i-v i) by rw [← nod,neg_sub]]
    dsimp only [w]; rw [map_add,map_add,map_sub, Lattice.wrap_step]
    change _= thread (wrap _ (v i) + _ - _) - thread (wrap _ (v i) + _ + _+_) - _
    rw [add_sub_add_right_eq_sub,show wrap _ (v i)+wrap _ (u i)+step p.1.2+(o i+o i)=wrap _ (v i)+o i+(wrap _ (u i)+o i)+step p.1.2 from by abel]; unfold v u; ring
 simpa using zeroF T
end YM.SchemeRG11.Acorn
