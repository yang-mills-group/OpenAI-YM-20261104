import YM.FVAAlt2.Rocket.Merits
import YM.FVAAlt2.Rocket.Tour
/-! # Tuition for off-shell physical positions at each Track
    Dual geometry uses *independent terminal side* n_ℓ of inversion
    vs the periods of actual Run. Every possible horizon and every tuple on
    an arbitrary index set.X, incl varying positions, given the precise Mesh/Curve
    & clearance scopes. Does not imply we can compare to exterior-OPE reads
    with collision scales. Next exhibit License on static separated tuples.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.FVAAlt2.Lodge.Track
open Function Set Filter MeasureTheory Topology Real
open Lattice RG Precision Gauge
open Oracle Epoch Calibration Rocket Uniform Binding Diagram Ledger Ledger.Sky Taping Atlas Spatial
open MS MS.Plane MS.Dial MS.Orbit MS.Tide MS.Vista MS.Fleet MS.Land MS.High MS.Rake
open scoped Topology ENNReal NNReal BigOperators Classical PowerSeries ContDiff Matrix.Norms.Frobenius
variable {X I:Type}(T:Track X){G:Gauge}
set_option quotPrecheck false
local notation:max "P_" x:max=> Page.opening T.entire x
def factor (x:X):ℕ:= (T.size (P_ x)).val/4
lemma factor_eq(x:X): (T.size (P_ x)).val=4*T.factor x:=(Nat.mul_div_cancel' (dvd_mul_of_dvd_left (by norm_num:4∣8) _ : 4∣(T.size P_ x).val)).symm
lemma factor_p (x:X): 0<T.factor x:=by have h:=T.factor_eq x; have hh:=(T.size P_ x).pos; omega
def tag (x:X):ℕ:= T.factor x-1
def campus (x:X) := Fleet.walkway (T.tag x)
lemma tags (x:X):4*(T.tag x+1)=(T.size (P_ x)).val:= by unfold tag; rw [Nat.sub_add_cancel (T.factor_p x)]; exact (T.factor_eq x).symm
lemma payments(x:X): dimT T.campus x=T.size (P_ x):= by
 apply Subtype.ext; exact (Fleet.fullC (T.tag x)).trans (T.tags x)
lemma ticks(x:X): MS.Vista.tickA T.campus x= T.desk.P x:=congr_arg (fun i:Side=> (i.val:ℝ)) (T.payments x)
def origin(x:X):= Fleet.crane (T.tag x)
lemma cornerL(x:X): Motion.slide 1 (T.origin x)= Tone.embed (T.origin x):= funext fun i=>one_mul _
lemma roomy (x:X): (1/8:ℝ)*(T.desk.P x) ≤ singular (T.desk.P x) (Motion.slide 1 (T.origin x)):=by
 let y:= Motion.slide 1 (T.origin x); let p:= T.desk.P x; let v:= Spatial.nearest (p/2) y
 have he:y 0=p/4:=by
    change 1* ↑( Fleet.crane (T.tag x) 0 : ℤ) = (( (T.size (P_ x)).val:ℕ):ℝ)/4; unfold Fleet.crane; rw [if_pos rfl, ← T.tags]; push_cast; ring
 have hp:0<p:= T.desk.synchronize _
 apply le_trans _ (norm_le_pi_norm (y-Motion.slide (p/2) v) 0)
 change _ ≤ ‖y 0-p/2*(v 0)‖; rw [Real.norm_eq_abs, le_abs]; rcases le_or_gt (v 0) 0 with ha|ha
 · left; have ht : ((v 0:ℤ):ℝ)≤0:= by exact_mod_cast ha
   change _*p≤_; nlinarith
 right; have hv: (1:ℝ) ≤ (v 0:ℤ) := by exact_mod_cast (show (1:ℤ) ≤ v 0 from ha)
 change _ ≤_; nlinarith
variable [LinearOrder I][Fintype I]
def VenueT(u:X→ Cover):Prop:= Clearance T.campus u∧ Vista.width T.campus u ∧ ∃ c:ℝ,0<c∧ ∀ x:X,c*(T.desk.P x)≤ Spatial.singular (T.desk.P x) (Motion.slide 1 (u x))
omit [LinearOrder I] [Fintype I] in
lemma visible : T.VenueT T.origin:= ⟨fun i=> Fleet.Cleared _, MS.Vista.centered_size _ _ (fun i=> Fleet.centerD (T.tag i)), 1/8,by norm_num,T.roomy⟩
-- careful empty instances unused!
variable (μ:ℝ)(U:X→ Cover)(W:I→ X→ Cover)(l:Filter X)
def PoseT : Trial X I:= {
    profile:= ⟨ T.Θ, fun i=>μ- T.Θ i, fun i=> (show (0:ℝ) ≤ 1 by norm_num).trans (T.space_hi _) ⟩
    head:= U
    off:=W
    side:=T.campus }
local notation "F"=> T.PoseT μ U W
local notation "Ω"=> T.Θ
local notation:max "P₀" x:max => Motion.slide 1 (U x)
lemma super (h:Tendsto T.batch l atTop): Super l T.campus T.Θ:=by
     intro a; filter_upwards [(T.era h).spread (max a 0) (le_max_right ..)] with i hi
     have hθ:= T.space_hi i; rw [T.ticks]; apply le_trans (b:= (max a 0) * (T.Θ i+ Real.log ( T.lumber.val i ).toReal)) _ (hi.trans ?_)
     · rw [T.toReal,log_exp]; nlinarith [le_max_left a 0,le_max_right a 0]
     have hp:T.depth (T.stop.choose i) ≤ T.desk.P i:= headroom T.desk (T.stop.choose i); exact Real.log_le_log (T.ht_live _) hp
lemma launch (hs: T.VenueT U)(h: Tendsto T.batch l atTop)(hp:MS.Tide.Profile (F).profile W)(ht: Rake.Mesh (F).profile (info W)) : Dial.Uses F l μ := ⟨hp,ht,fun _=>rfl, T.θ_runs h,T.super l h,hs.1,hs.2.1⟩
lemma native_costs (hp:MS.Tide.Profile (F).profile W) (i:I) : Kick.Nearest (fun x=>P₀ x) T.lumber fun w=> Zpose F w i:=by
    obtain ⟨C,hC,H⟩:=hp i; have hx(x): dist (P₀ x) (Motion.slide 1 (Zpose F x i))= ‖Tone.embed ( W i x )‖:=by
        rw [show Zpose _ x i= U x+W i x from rfl,map_add,dist_comm,dist_self_add_left]; apply congr_arg _; exact funext fun z=> one_mul _
    refine ⟨ ((Poly.standard _ (ENNReal.ofReal_ne_top (r:=C))).mul (Poly.roof _)).mono fun w=> ?_⟩
    change ENNReal.ofReal (dist _ _)≤_; rw [hx]; exact ((ENNReal.ofReal_le_ofReal (H w)).trans_eq (ENNReal.ofReal_mul hC.le))
omit [LinearOrder I] [Fintype I] in
lemma idNear : Kick.Nearest (fun x=>P₀ x) T.lumber U:= ⟨ by simp_rw [dist_self,ENNReal.ofReal_zero]; exact Poly.zeroQ _ ⟩
end YM.RegulatorIR.FVAAlt2.Lodge.Track
