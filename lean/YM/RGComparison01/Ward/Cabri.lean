import YM.RGComparison01.Ward.Visage
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Tint
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Carrier
import YM.Push.STATIONARY_UNIFORM.Array

/-!
# Rooted Lattice.gauge representative on auxiliary period

All paths/measure points first. Position coordinates explicitly; log choice
frozen. Uses ambient real jets. Cost when `Mode` charges paid,
paying total aux diameter only POLYNOMIAL with constants fixed by the
allocator before thresholds, even though output stencil may be growing.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01.Ward
open Function Filter MeasureTheory RG Pressure Pressure.Stores Pressure.Tube Gauge Wilson
open Lattice Next.Fluctuations Push Push.Uniform Push.AbsoluteSums Precision Exterior
open Work.E03 Work.F03 ConnectedActivityE6 SliceRows Blaze Brush
open scoped Matrix.Norms.Frobenius Topology ContDiff InnerProductSpace Classical BigOperators
variable {G:Gauge}{c:Side}{j k :ℕ}
def sectionAt (x:Site c) (V:Config G c)(z:G.El):Site c → G.El:= fun y=> z*carrier x V y
def toral (x:Site c)(z:G.El)(V:Config G c):=Lattice.gauge (sectionAt x V z) V
@[simp]
lemma toral_gauge (x:Site c)(z:G.El)(V:Config G c)(a : Site c→ G.El): toral x z (Lattice.gauge a V)= toral x (z*a x) V:= by
  funext i
  unfold toral Lattice.gauge sectionAt carrier
  simp_rw [show (fun e:Edge _=> a e.1*V e * (a (e.1+step e.2))⁻¹)=Lattice.gauge a V from rfl,travel_gauge,deposits]
  group
@[simp]
lemma toral_one (x:Site c)(z:G.El) : toral x z (1:Config G c)=1:= by
  funext i; change _=(1:G.El); unfold toral Lattice.gauge sectionAt carrier; rw [SliceRows.trivial,SliceRows.trivial,Pi.one_apply]; group
local notation "R"=> (royalty G)
abbrev longitude (d:ℝ) (n:ℕ) (Q:ℝ) := ((4*n)*(d*Q))*Q + (d*Q +(4*n)*(d*Q)) -- natural cast bug check
lemma probity (x y:Site c) : separation x y ≤ c.val := by
   unfold separation pdist; refine Finset.sup_le (fun i _=>?_); have h:=lift_centers (x-y) i; omega
section
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {u d:ℝ} (Y: E→ Config G c) (p:E)
lemma toral_pay (X:Site c)(z:G.El) (h:Mode Y p k d) : Mode (toral X z ∘ Y) p k (longitude d c.val R):= by
  have ha : 0 ≤ longitude d c.val R:= by unfold longitude; have hu:= h.pos; have hz:= royalty_ge G; positivity
  have hg : max 1 R ≤ R:= max_le (royalty_ge G) le_rfl
  constructor; · exact ha
  intro i
  let Z (x:E) (v:Site c):= sectionAt X (Y x) z v; let I₀ :ℝ:=(4*c.val:ℕ)*(d*R)
  have he (v:Site c):Brush k R I₀ (fun i=> G.mat (Z i v)) p:=by
    have hx : (carriage X v).length ≤4*c.val:= (mileage X v).trans (Nat.mul_le_mul_left _ (probity X v))
    have hf:= (tour (U:=Y) (carriage X v) X h.pos h.atLink)|>.climb le_rfl (mul_le_mul_of_nonneg_right (show ((carriage X v).length:ℝ)≤ (4*c.val:ℕ) by exact_mod_cast hx) (mul_nonneg h.pos (zero_le_one.trans (royalty_ge _))))
    simpa only [mul_one] using! Blaze.offsetB hf z (1:G.El)
  have hh := Blaze.links (f:=fun i=> Z i _) (he i.1) (Blaze.links (h.atLink i) (Blaze.reverse (f:=fun t=>Z t _) (he (i.1+step i.2))) _ hg) _ hg -- price
  apply (hh.climb le_rfl (by unfold I₀ longitude; push_cast; rfl)).shimmy -- args
  exact Eventually.of_forall fun j=> by simp only [Function.comp_apply,toral,Lattice.gauge, G.mat_mul]; exact mul_assoc ..
end
namespace Visage
variable (C:Visage G k)
local notation "T"=> Uniform.Primary c G
local notation "A"=> Positions (Uniform.Primary c G)
abbrev polar (C:Visage G k)(W:Config G c) : Positions T:= let q := Uniform.tint G (Body 1 c)
                                                          q.symm (SliceRows.toLog fun i: Pressure.Bond c=> C.logG (G.mat (W i)))
def encode (x:Site c)(V:Config G c)(z:G.El):= C.polar (toral x z V)
abbrev prices (C:Visage G k):ℝ:= (k.factorial:ℝ)*C.cost
variable (x:Site c)(U : Config G c)
local notation "qL"=> (Uniform.tint G (Body 1 c))
include C
@[simp] lemma other (z:G.El)(w: Site c→ G.El): C.encode x (Lattice.gauge w U) z=C.encode x U (z*w x):= by unfold encode; rw [toral_gauge]
@[simp] lemma one (z:G.El) : C.encode x 1 z=0:= by
  unfold encode; rw [toral_one]; unfold polar; dsimp only; rw [show SliceRows.toLog (fun i: Bond c=> C.logG (G.mat ((1:Config G c) i)))=0 by ext1 j; simp only [SliceRows.toLog,Pi.one_apply,G.mat_one,C.on_one,Pi.zero_apply],map_zero]
lemma award (z:G.El)(he: ∀ i, ‖G.mat (toral x z U i)-1‖ ≤ C.radius): represent (qL (C.encode x U z)) = toral x z U:= by
  unfold encode polar; rw [ContinuousLinearEquiv.apply_symm_apply]; funext j; rw [Work.F03.represent_link,show (j.1,coord j.2)=pole j from rfl,SliceRows.at_pole]; exact C.rightC _ (he j)
lemma drape : Continuous (fun p: Config G c×G.El=> C.encode x p.1 p.2):=by
  have hp (i:Pressure.Bond c) : Continuous (fun p: Config G c×G.El=> toral x p.2 p.1 i):=by
    unfold toral Lattice.gauge sectionAt carrier; fun_prop
  exact (qL).symm.continuous.comp (continuous_pi fun i=> C.bloom.continuous.comp (G.continuous_mat.comp (hp ((poleEquiv c).symm i))))
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {d:ℝ}
lemma reckon (Y:E→Config G c)(p:E) (z:G.El)(h:Mode Y p k d) : Brush k C.prices ((1+R)*longitude d c.val (royalty G)) (fun i=> C.encode x (Y i) z) p:=by
  have hp := toral_pay Y p x z h; let f (t:E):= toLog (n:=c) fun i=> C.logG (G.mat (toral x z (Y t) i))
  have he : Brush k C.prices _ f p:=Brush.fold («T»:=fun i t=> f t i) (mul_nonneg (add_nonneg zero_le_one (zero_le_one.trans (royalty_ge _))) hp.pos) (by unfold prices; have hv:=C.pricey; positivity) (fun i=> (hp.atLink ((poleEquiv c).symm i)).pine (C.live _))
  have hs := he.report (qL).symm.toContinuousLinearMap (v:=1) (ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun i=> by rw [one_mul]; exact Uniform.tint_inv_le _)); rw [one_mul] at hs; exact hs
end Visage
end YM.RGComparison01.Ward
