import YM.FVAAlt2.Rocket.Fuel
import Mathlib.Analysis.Complex.ExponentialBounds
/-!
# Actual window plan instance

This generic instance with constant smoothing across each regulated interval
 can be instantiated with one actual Calendar and Run on thick windows, J ≥ older bounds.
 For degree ν fine steps at measurement, take 2ν² total steps, ν² at first stop (still holding
 field), and terminal unconditioning by Endings on near-constant side. All comparisons still
 are parameterized by μ.L etc. This is only permission for projection -- no connection to the
 retained Run or same vacuum action HERE. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.FVAAlt2.Lodge
open Function Set Filter MeasureTheory Topology Real
open Lattice RG Precision Gauge
open Oracle Epoch Calibration Rocket
open Uniform Binding Diagram Ledger Taping Atlas
open scoped Topology ENNReal NNReal BigOperators Classical PowerSeries ContDiff Matrix.Norms.Frobenius
structure Track (X:Type) where
   J:X→ℕ
   L:X→Side
   batch:X→ ℕ
   life x: 0< batch x
   stands x: 3≤ (L x).val
   owns x: Odd ( L x ).val
   issued x: 5 ≤ J x
variable {X:Type}(T:Track X)
namespace Track
def long(x:X):ℕ:= T.batch x * T.batch x
def entire(x:X):ℕ:=2*T.long x
def stop:Choice T.entire:= ⟨ T.long,fun x=>show T.long x≤ 2*T.long x from by omega ⟩
def surface(x:X):ℝ:= ((T.L x).val:ℝ)
def depth(w:Page T.entire):ℝ:= T.surface w.bindW ^ w.downW
def height(w:X):ℝ:= log (T.surface w)
def Θ(w:X):ℝ:= (T.batch w:ℝ)*T.height w
def size(t:Page T.entire):Side:= ⟨ 8 * (T.L t.bindW).val ^ (T.entire t.bindW - t.downW),by positivity ⟩
set_option quotPrecheck false
local notation:max "t_" x:max=> (T.L x).val
local notation:max "P_" x:max=>Page.opening T.entire x
local notation "L'"=> T.surface
local notation "E'"=> T.Θ
lemma surf_min(x:X): 3 ≤ L' x:= by unfold surface; norm_cast; exact T.stands x
lemma surf_lives(x:X): 0<L' x:= (show (0:ℝ)<3 from by norm_num).trans_le (T.surf_min x)
lemma ht_high(x:X): 1 ≤ T.height x := by rw [height,← exp_le_exp,Real.exp_log (T.surf_lives _)]; exact Real.exp_one_lt_three.le.trans (T.surf_min _)
lemma space_hi(x:X): 1≤ T.Θ x:= by unfold Θ; exact one_le_mul_of_one_le_of_one_le (by exact_mod_cast T.life _) (T.ht_high _)
lemma ht_live(t:Page T.entire): 0<T.depth t:=pow_pos (T.surf_lives ..) _
lemma moved (p:Flap T.entire): T.depth p.next=T.depth p.prev * t_ p.volW:= pow_succ ..
lemma drafted (p:Flap T.entire): T.size p.prev=T.size p.next * T.L p.volW:=by
 apply Subtype.ext; change 8 * t_ p.volW ^ (T.entire p.volW-p.offset)=8* t_ p.volW ^ (T.entire p.volW-(p.offset+1))*t_ p.volW;rw [show T.entire p.volW-p.offset=T.entire p.volW-(p.offset+1)+1 by have h:=p.ok; omega,pow_succ,mul_assoc]
lemma time_paid(x:Page T.entire): T.depth x * (T.size x).val=(T.size (P_ x.bindW)).val:=by
 unfold size depth; change L' x.bindW ^ x.downW* ↑( 8*t_ x.bindW ^ (_-x.downW))=↑(8*t_ x.bindW^ (T.entire x.bindW - 0 ));push_cast;rw [mul_left_comm,show _=(8:ℝ)* _ from rfl]; unfold surface; rw [← pow_add,Nat.add_sub_of_le x.good,Nat.sub_zero]
lemma perm_layer(x:Page T.entire): 4≤(T.size x).val:=by change 4 ≤ (8 * _ : ℕ); have h:0<t_ x.bindW ^ (T.entire x.bindW-x.downW):= pow_pos (T.L x.bindW).pos _;omega
lemma even_size(x:Page T.entire): Even (T.size x).val:= even_iff_two_dvd.mpr (by unfold size; change 2 ∣ 8*_ ; exact dvd_mul_of_dvd_left (by norm_num) _)
def desk : Circuit T.entire T.size := { l:= T.depth,P:=fun x=> (T.size (Page.opening T.entire x)).val,J:=T.J∘Page.bindW,sizeL:=T.L∘Flap.volW,seats:=T.drafted,odd:=fun _=>T.owns _,holds:=fun _=>T.stands _,stands:=T.perm_layer,dual:=T.even_size,week:=fun i=> Nat.le_trans (by decide:4≤5) (T.issued _),shakes:=fun _=>le_refl _,slow:= fun _=> Nat.le_succ _, l_p:= T.ht_live,comet:= T.time_paid }
lemma opens(x:X): T.desk.l (P_ x)=1:= pow_zero _
lemma shut (x:X): T.size (Page.finallyW _ x)=8:= by apply Subtype.ext; change 8 * _ ^ (T.entire x-T.entire x)= 8; simp
lemma clock (w:Page T.entire): log (T.depth w)= (w.downW:ℝ)* T.height w.bindW:=by rw [depth,log_pow]; rfl
lemma time_stop (i:X): log (T.depth (T.stop.choose i))= (T.batch i:ℝ) * E' i:=by rw [T.clock]; change (↑(T.batch i*T.batch i):ℝ)*T.height i= _; rw [Nat.cast_mul, mul_assoc]; rfl
lemma thick (i:X): log ( T.desk.P i ) = log 8 + 2 * (T.batch i:ℝ) * E' i:=by
 have ht: T.desk.P i=8*T.depth (Page.finallyW _ i):= by simpa only [T.shut,show ((8:Side).val:ℝ)= (8:ℝ) by change ((8:ℕ):ℝ)=8; norm_num,mul_comm] using (show T.depth (Page.finallyW _ i)*(T.size (Page.finallyW _ i)).val=T.desk.P i from T.time_paid _).symm -- adjust
 rw [ht,Real.log_mul (by norm_num) (T.ht_live .. |>.ne'),T.clock]; change log 8 + (↑(T.entire i):ℝ)*T.height i=_; unfold Θ; unfold entire long; push_cast; ring

def fill (i:X):ℝ:=exp (E' i)
lemma filled (i:X): 1≤ T.fill i:= Real.one_le_exp ((show (0:ℝ)≤1 by norm_num).trans (T.space_hi i))
lemma exp_th (i:X):T.fill i=T.surface i ^ T.batch i:=by unfold fill Θ height;rw [exp_nat_mul, exp_log (T.surf_lives _)]
lemma above (x:X): E' x ≤ T.fill x:= (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _)
lemma hallL (x): (T.batch x:ℝ) ≤ T.Θ x:=le_mul_of_one_le_right (Nat.cast_nonneg _) (T.ht_high _)
lemma length_pay(x): L' x≤ T.fill x:=by rw [exp_th]; exact (pow_one _).symm.trans_le (pow_le_pow_right₀ ((show (1:ℝ)≤3 by norm_num).trans (T.surf_min _)) (T.life _))

def lumber: Meter X:= ⟨fun i=> ENNReal.ofReal (T.fill i),fun i=> by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (T.filled _),fun _=> ENNReal.ofReal_ne_top⟩
lemma toReal (i:X): (T.lumber.val i).toReal=exp (E' i):= ENNReal.toReal_ofReal (exp_pos _).le
lemma θ_runs {l:Filter X}(h:Tendsto T.batch l atTop): Tendsto T.Θ l atTop:= tendsto_atTop_mono (f:=fun i:X=>(T.batch i:ℝ)) (T.hallL) (tendsto_natCast_atTop_atTop.comp h)
lemma era {l:Filter X}(h:Tendsto T.batch l atTop): Pace T.desk T.stop T.Θ l T.lumber:=by
    constructor
    · exact (Poly.roof _).mono fun i=>by change ‖exp _‖ₑ ≤ ENNReal.ofReal _; rw [← ofReal_norm,Real.norm_of_nonneg (exp_pos _|>.le)]; exact le_rfl
    intro r hr; filter_upwards [ (tendsto_natCast_atTop_atTop.comp h).eventually (eventually_ge_atTop (2*r))] with i hi
    rw [T.toReal,Real.log_exp] -- foo
    change _ ≤ log (T.depth (T.stop.choose i)); rw [T.time_stop]; change r* (E' i + E' i ) ≤ _; have ht:= T.space_hi i; change 2*r ≤ (T.batch i:ℝ) at hi; nlinarith

end Track
end YM.RegulatorIR.FVAAlt2.Lodge
