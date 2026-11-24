import YM.MS.Fleet.Anchor
import YM.MS.Vista.Terrain
/-!
Rake uses the spread shell multiplier against 4d plane Lebesgue. When comparing to the
infinite lattice cover one can fold these integrals to the zone, but this will only work
at lattice offsets. The identities here are in the strictly periodic coordinates.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Fleet
open Set Filter Function Finset Metric MeasureTheory Real
open Koszul Plane Landau Detect Tone Momentum Heat Osc Fiddle Osc.Snap Native
open Lattice City Latch Job Belt Rake Flux Wire Book Convolve Orbit Cog
open scoped Topology ContDiff Interval
variable {G:Gauge}{I:Type}
variable {μ:Measure QP}{F H:Glade G I}{P:Latch.Edge G}
  {x y z:Lengths G}
local notation "pQ"=> field (parity (C:=G.ColorIndex) (A:=Axis))

lemma adv_lod (A:I→Cover)(h:Toned F): Toned (fun i t=> lodging (A i) ( F i t )) := ⟨ fun i E _ _ f w hv ht=> ((be_sm (A i)).comp hv.net0).mul (h.touch i E f w hv ht), fun i t l r he => congr_arg₂ (·*·) (φ_per (A i) (n_cast he)) (h.sound i t l r he) ⟩
lemma cap_lod (A:I→Cover)(h:Knits F): Knits (fun i t=> lodging ( A i ) ( F i t )) := by obtain ⟨hp,k,hk⟩:= h; exact ⟨ adv_lod A hp,k,fun i t l hv=> by dsimp only; rw [lodg,hk i t l hv,mul_zero]⟩
lemma cycle_fee (K:Latch.Edge G)(μ:Measure QP)(X:Law G)(c:ℂ): cycle ( c • K ) μ X=c • cycle K μ X:= by simp_rw [← Θ_z]; exact Vista.ΘpcFee ..
lemma spread_s (K:Latch.Edge G)(c:ℂ): Rake.spread ( c • K )= c • Rake.spread K:= by funext i j p; simp only [ Rake.spread,Pi.smul_apply, smul_eq_mul ]; ring
lemma spread_d (K:Latch.Edge G): Rake.spread ( dope K )= dope ( Rake.spread K ):= by funext i j p; simp only [ dope_p, Rake.spread ]; ring
lemma tr_town (h:Toned F)(i:I)(t:ℝ): cycle ( Rake.spread ( LaceL G t ) ) planeF ( F i t )=cycle (LaceL G t) μzone ( F i t ):= by
    funext w; unfold cycle; simp_rw [ degreeF ]; apply shineZ; · obtain hx:= Hz false 0 ( h.touch i ) ( station_t ( A:=QP ) w ) ( healthy G I |>.flexW i ) (contDiff_const (c:=t)) contDiff_id; convert! hx.continuous using 1; funext p; simp only [ id_eq, station_w, wait, be_0,one_mul, at_trc ]; rfl
    refine pin_C ?_; intro p q he; have hm: SpeaksK ( LaceL G t ):= ( healthy G I |>.proper i t ).pin; simp_rw [at_trc, hm _ _ he]; refine Finset.sum_congr rfl fun k _=> Finset.sum_congr rfl fun j _=> congr_arg ( LaceL G t k j q * · ) (h.sound i t ((k,p)::(j,-p)::w) ((k,q)::(j,-q)::w) (.cons ⟨rfl,he⟩ ( .cons ⟨rfl,he.opp⟩ (asc w) )))
lemma join_town (A:Cover) (h:Toned F)(hx:Toned H)(i:I)(t:ℝ): PairV false planeF 0 A ( Rake.spread ( LaceL G t ) ) (F i t) (H i t)= PairV false μzone 0 A (LaceL G t) (F i t) (H i t):= by -- needs 0 0 only
    funext w; unfold PairV; refine scatter_congr _ _ _ _ (fun l r he=>?_); simp only [be_0, one_mul]; refine Finset.sum_congr rfl fun x _=>Finset.sum_congr rfl fun y _=>?_ ; let K:= LaceL G t; let V (z:QP):= be A z*viν false K x y ( F i t) ( H i t ) l r z
    have hK:SpeaksK K:= ( healthy G I|>.proper i t|>.pin )
    have hh: pinQ V:= by
       intro p q he; unfold V viν; rw [ φ_per A he, h.sound i t _ _ (show twins (( x,p )::l) ((x,q)::l) from ( .cons ⟨rfl,he⟩ ( asc l ) )), hx.sound i t _ _ (show twins ((y,Opp false p)::r) ((y,Opp false q)::r) from (.cons ⟨rfl,he.opp⟩ (asc r))), hK x y he ];
    have hv : Continuous V:= by
       obtain hv:= touch_mesh false ( healthy G I|>.flexW i ) x y ( station_t ( A:=QP ) l ) ( station_t ( A:=QP ) r ) (h.touch i) (hx.touch i) (contDiff_const (c:=t)) contDiff_id; refine ( be_sm A ).continuous.mul ?_; convert! hv.continuous using 1; funext p; simp_rw [id_eq, station_w]; rfl
    change (∫ q, be A q * viν false (Rake.spread K) x y (F i t) (H i t) l r q ∂planeF)=∫ q,V q ∂μzone; rw [← shineZ hv (pin_C hh)]; refine integral_congr_ae (Eventually.of_forall fun q=>?_); unfold V viν Rake.spread; ring

end YM.MS.Fleet
