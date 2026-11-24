import YM.FVA2.Arrival.Episodes
import YM.FVA2.Recall.Clocked
/-! # To each physical coupling nomenclature: Gram epoch re-expression

 Use with e.g. `Gear` for another rung's `g_i` in place of `g_N`; or
 $XSpace$ coupling at any rank (after tangent qualification). The conditional
 statement then also uses **coarse field coordinates in that nomenclature**.
 Need cumulative $g_N$ condition if switching back. This theorem doesn't
 address quasi-local analytic estimates. No freedom to discard `Clock`
 from those comparisons from this lemma. Here with inversion regulator and
 literal chart costs retained. No omitted determinant nor vacuum scalar.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Recall.Move
open Function Set Filter Finset MeasureTheory FormalOPE.RG10 FormalOPE.RG10.MultiGauge
open StationaryMarks MultiGauge.Stack PowerSeries MarkovChain Warp Splice OpenSlots
open Paint Euler PertExtension PertExtension.Series Radial GaussianScore Facade Lattice RG
open Tested OpenSlots.Quadratic Precision Chart BlockGauge MultiGauge.Blocking Fabric Papers Line Roof Router Hearth
open Arrival Episodic
open scoped Classical Topology BigOperators ContDiff

-- qualify an arbitrary common frame, in particular pass to terminal units
lemma from_move (P:PowerSeries ℝ)(h:constantCoeff P=0)(hp: coeff 1 P=1):∃ m:Move,m.frame=P:= by
 let p:= Stack.drop 1 P; have hx:P=X*p:= by rw [← pow_one X]; exact (Stack.recover 1 P (fun _ hi=> by obtain rfl:=show _=0 from Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hi); simpa only [coeff_zero_eq_constantCoeff_apply] using h)).symm
 refine ⟨⟨p,?_⟩,hx.symm⟩; rw [←coeff_zero_eq_constantCoeff_apply, show coeff 0 p= coeff 1 P from coeff_mk ..]; exact hp -- syntax
variable (m:Move)
lemma self_unit : coeff 1 (frame m)=1:= by unfold frame; rw [coeff_succ_X_mul 0 m.p, coeff_zero_eq_constantCoeff_apply ]; exact m.starts
lemma reversed : ∃ r:Move, m.sponsor r.frame=X ∧ r.sponsor m.frame=X:= by
 let P:=m.frame; have hx: IsUnit (coeff 1 P):=by rw [show coeff 1 P= _ from m.self_unit]; exact isUnit_one
 let u:= P.substInvOfIsUnit hx; have he: coeff 1 u=1:= by unfold u; rw [ PowerSeries.coeff_one_substInvOfIsUnit ]; simp; exact m.self_unit
 obtain ⟨r,hr⟩ := from_move u (PowerSeries.constantCoeff_substInvOfIsUnit ..) he; exact ⟨r,by rw [m.frame_stamp,hr]; exact PowerSeries.subst_substInvOfIsUnit_left P m.grounded hx,by rw [r.frame_stamp,hr]; exact PowerSeries.subst_substInvOfIsUnit_right P m.grounded hx ⟩
lemma of_frame (f:PowerSeries ℝ)(h:constantCoeff f=1) : ∃ t:Move,t.frame = X*f⁻¹:= by
 refine ⟨ ⟨ f⁻¹,?_⟩,rfl ⟩; obtain h':= congr_arg constantCoeff (show f⁻¹*f=1 from PowerSeries.inv_mul_cancel _ (h.symm ▸ one_ne_zero)); simpa only [map_one,map_mul,h,mul_one] using h'
lemma change (f:PowerSeries ℝ)(h:constantCoeff f=1) : ∃ r:Move, r.sponsor (X*f⁻¹)=X ∧ r.frame.subst (X*f⁻¹)=X:= by
 obtain ⟨t,ht⟩:= of_frame f h; obtain ⟨r,hs,hv⟩:= reversed t; rw [←ht]; exact ⟨r,hv,(t.frame_stamp _).symm.trans hs⟩

variable {G:Gauge}{c f n:Side}{J:ChartRatio G}
variable (Y:XSpace.Initialize G) {L: Fabric G n}(K: Gear L)(T: Cloth L) (h: LocalRatio J)
lemma any_layer (i:L.Accounts): ∃ t:Move,t.sponsor (K.coupling i)=X ∧ t.frame.subst (K.coupling i)=X:= by unfold Gear.coupling; exact change _ (K.begins i)
-- root exposure at terminal uses this declared last speed on an Epoch

def local_time : PowerSeries ℝ:=X*(K.terminal)⁻¹
lemma at_terminal : ∃ t:Move, t.sponsor ( local_time K )=X ∧ t.frame.subst ( local_time K )=X:= change _ (K.endv)
lemma transformed (i:L.Accounts): (m.weight (K.loops i)) * ( m.sponsor ( K.coupling i ) )^2 =X^2:= by
 unfold Move.weight; rw [ mul_right_comm, ← map_pow, ← map_mul, Gear.boost_out, map_pow,m.sponsor_x,frame,mul_pow,mul_assoc,←mul_pow, m.old,one_pow, mul_one]

variable (l:List (Folio G)) (y: Flats G ( Bottom L )) (x:G.ColorIndex)
local notation "w"=> (Move.weight m ∘ Gear.loops K)
local notation "r"=> Gear.loops K
local notation "p"=> Facade.collared T (Gear.loops K) h (Gear.priced _)
local notation "ρ"=> Facade.collared T w h (still m _ ( Gear.priced K ))
local notation "W"=> Flats G ( Bottom L )
local notation "φ"=> m.walk W
local notation "V"=> Facade.drive T (r∘some) (Facade.headquarters r) ( Hearth.markValue Y l n ) J p
local notation "A"=> ( Hearth.markValue Y l n )
local notation "D"=> Folio.asset l
open RGComparison.Core16
include x y
-- This time $y$ in new units, `s^{-D}` STAMP request. Doesn't allow orphan w
structure Employer (v:L.Accounts→ℝ→ℝ) (N:ℕ) : Prop where
    aligned : ∀ i,Through N ( Facade.amount (v i) ) ((Move.weight m ∘ Gear.loops K) i)
    heated : ∀ i,ContDiffAt ℝ ω (v i) 0
include h

def office := Stack.read y ( Move.walk m ( Flats G ( Bottom L ) ) V.2 )
theorem badgeFk (v:L.Accounts→ℝ→ℝ)(N:ℕ)(H:Employer m K v N) (i:ℕ)(hi:D+i≤N): Lumen.Fk.read ( localClimate T y x v ) J ( tease T x ) ( lens T y x ( Hearth.rad T ( Folio.scenario Y n l ))) D i = coeff i (m.p^(Folio.asset l)*office m Y K T h l y):= by
 obtain he:= epoch h m T r (Gear.priced K) (imprintRoot (Folio.scenario Y n l)); obtain hf:= predicted T y x v h w (still m r (Gear.priced K)) N H.heated H.aligned (Folio.scenario Y n l) (Folio.matured Y n l L.even) D i hi
 rw [ show m.walk _ (imprintRoot (Folio.scenario Y n l))= imprintRoot (Folio.scenario Y n l) from m.any_rise _ ] at he; rw [hf,he.2]
 -- weight from D
 rw [←broadcasted Y T l r (Gear.priced K) h,map_mul φ,map_pow, walk_x,map_mul,map_pow,map_mul ( Stack.read y ), load,show Stack.read y X=X from PowerSeries.map_X .., mul_pow,mul_assoc, PowerSeries.coeff_X_pow_mul',if_pos (by omega),Nat.add_sub_cancel_left ]; rfl
omit x y
-- transformed purchases still compared at **the same g_N** variable (now transformed to m.frame), not shifting the limit along an output-dependent clock.
theorem there : purchase T w (still m r (Gear.priced _)) h (m.walk _ (markValue Y l n))= m.sponsor ( Folio.coefficients Y n l ) := by rw [m.credit h T _ (Gear.priced _), toll Y T l _ (Gear.priced K) h K.first] -- args syntax
end YM.FVA2.Recall.Move
