import YM.SchemeRG11.Long.Sigil
import YM.SchemeRG11.Long.Rim
/-! Long class density and supports. -/
noncomputable section
set_option autoImplicit false
namespace YM.SchemeRG11.Banner
open Function Filter Asymptotics Topology MeasureTheory Metric
open Flock Lattice Pert Align Full Maxwell Haze Pile Catch World Atoll Tree Acorn
open Labels MvPolynomial Outlook North Long
open scoped Classical Pointwise
variable {G:Gauge} {n d:ℕ} {T:Align.Itinerary} {B:Window} {R:ℝ}
local notation "D₁" => Atoll.land G
def coronal(T:Align.Itinerary)(B:Window): Ban G:= Long.play (cove T B) (∑ i:Axis,∑ j:Axis,Long.part i j)
def smoke(T:Align.Itinerary)(B:Window)(p:pLabel G):Ban G:= (coronal T B)*Long.castV (stemZero 1 p) - Long.Volume.mix p (coronal T B)
lemma vault (T:Align.Itinerary)(B:Window): Long.Nest T 4 (coronal (G:=G) T B):= (nest_sum _ _ _ (fun i _=>nest_sum _ _ _ (fun j _=>carries i j))).scale (y:=0) ((neg_zero (G:=ℤ)) ▸ (Long.choice T B)) -- check
lemma swell (V:Long.Volume G T){p:pLabel G}(h:IsWeightedHomogeneous generation p n) (B:Window): V.classV ((n:ℤ)+4) (smoke T B p):=by
 obtain ⟨a,b⟩:=V.sound h _ _ (vault T B); unfold smoke; refine V.sub ?_ b; rw [mul_comm]; exact V.mul a (V.nest _ _ (vault T B)) -- p implicit missing
lemma frameB(i:ℕ)(s:Finset Cover)(p:pLabel G): nebula (cove T B i) s p=(D₁).heat (castFirst 1 p)+∑x∈s, smoke T B p i x:=by
 let C:=coronal (G:=G) T B
 have hh:escort (cove T B i) s= ∑ x∈s,C i x:=by simp only [C,coronal,Long.play,North.escort,Finset.sum_apply,Long.part]
 rw [withholds,Dose.weave_comm,hh]; unfold smoke Long.Volume.mix; rw [Dose.weave]; simp only [Pi.sub_apply,Pi.mul_apply, Dose.weave,map_sum, Finset.sum_sub_distrib, Finset.mul_sum,Finset.sum_mul, Long.castV]; unfold C; abel
lemma smoked_out {i:ℕ}{x:Cover}(h:cove T B i x=0)(p:pLabel G):smoke T B p i x=0:=by unfold smoke Long.Volume.mix Dose.weave; simp only [Pi.sub_apply,Pi.mul_apply, coronal, play,h,zero_smul,zero_mul,mul_zero,map_zero,sub_zero]
lemma banished (h:B.rOut<R) (p:pLabel G):∀ᶠ i in atTop,∀x∉gateY T R i, smoke T B p i x=0:=by
 filter_upwards [escort_cut (T:=T) h] with i he x hx; exact smoked_out (he x hx).1 _

def ardor(T:Align.Itinerary)(B:Window)(θ:Cover→ G.Color):Ban G:=∑ i:Axis,∑ k:G.ColorIndex,cinders B i k T * budge θ i k
def flash(T:Align.Itinerary)(B:Window)(θ:Cover→ G.Color)(p:pLabel G):Ban G:= (1/2:ℝ) • (Volume.mix p (ardor T B θ)- ardor T B θ * Long.castV (stemZero 1 p))
lemma sparked(i:ℕ)(s:Finset Cover)(θ:Cover→ G.Color)(p:pLabel G): gas (cove T B i) s p θ= ∑ x∈s, flash T B θ p i x:=by
 let C:= cove T B i
 have he: fringe C s θ=∑ x∈s, ardor T B θ i x:=by unfold fringe ardor; simp only [parade, Finset.sum_product,Finset.sum_apply, Pi.mul_apply,cinders,budge];rfl
 have hh : (D₁).neg.heat (fringe C s θ)=fringe C s θ:=by calc
     _ = (D₁).neg.heat ((D₁).heat (fringe C s θ)) := by rw [fringeHeat]
     _ = _ := (D₁).opposite _
 unfold flash Long.Volume.mix
 simp only [Pi.smul_apply,Pi.mul_apply,Pi.sub_apply,← Finset.smul_sum,Dose.weave, castV]; simp_rw [Finset.sum_sub_distrib,← Finset.sum_mul, ←map_sum,←Finset.mul_sum,← _root_.map_sum,← he, hh]; rw [gas,castFree,mul_comm (fringe ..)]-- check fragile mul_comm
lemma driveP(V:Long.Volume G T)(θ:Cover→ G.Color){m:ℕ}(h:θ∈cap G.Color (m+1))(p:pLabel G)(hp:IsWeightedHomogeneous generation p n)(B:Window): V.classV ((n:ℤ)+(4-(m:ℤ))) (flash T B θ p):=by
 have H:Nest T (4-(m:ℤ)) (ardor T B θ):= nest_sum _ _ _ (fun a _=>nest_sum _ _ _ (fun k _=> drought B h a k))
 obtain ⟨hv,hb⟩:= V.sound hp _ _ H; apply V.coin; refine V.sub hb ?_; rw [mul_comm]; exact V.mul hv (V.nest _ _ H)
lemma nofire(θ:Cover→ G.Color)(p:pLabel G)(i:ℕ)(x:Cover)(h:∀ j,barkS T B j i x=0): flash T B θ p i x=0:=by
 have H:ardor T B θ i x=0:=by
    simp only [ardor,Finset.sum_apply,Pi.mul_apply,cinders, brim,_root_.map_sum,map_smul]; apply Finset.sum_eq_zero; intro j _; apply Finset.sum_eq_zero;intro k _; apply mul_eq_zero_of_left; apply Finset.sum_eq_zero; intro d _; rw [show cove T B i (x-step d)-cove T B i x=0 from h d,zero_smul]
 unfold flash; simp only [Pi.mul_apply,Pi.smul_apply,Pi.sub_apply,zero_mul, sub_zero,Volume.mix,Dose.weave,H,map_zero,mul_zero,smul_zero]
lemma cold_out (h:B.rOut<R)(θ:Cover→ G.Color)(p:pLabel G):∀ᶠ i in atTop,∀x∉gateY T R i,flash T B θ p i x=0:=by
 filter_upwards [escort_cut (T:=T) h] with i he x hx; refine nofire θ p _ _ fun j=>?_; unfold barkS; rw [(he x hx).2,(he x hx).1,sub_self]
lemma cold_in (T:Align.Itinerary)(B:Window)(θ:Cover→ G.Color)(p:pLabel G):∃R>0,∀ᶠ i in atTop,∀x, Near T R i x→flash T B θ p i x=0:=by
 choose r hr H using (fun i=>vacatesR (T:=T) B i)
 obtain ⟨j,hh⟩:= Finite.exists_min r; refine ⟨r j,hr _,?_⟩
 filter_upwards [eventually_all_finset Finset.univ|>.mpr (fun i _=> H i)] with i hi x hx
 exact nofire θ p _ _ fun v=> hi _ (Finset.mem_univ _) _ (le_trans hx (hh v))
end YM.SchemeRG11.Banner
