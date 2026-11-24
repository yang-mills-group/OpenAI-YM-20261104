import YM.Contacts.Model.School
/-! Difference after finite compact transfer. Explicit costs. -/
noncomputable section
namespace YM.Contacts.Model
open Function Lattice Finset Filter Set PhysicalNext.Repeat Pressure Wilson MeasureTheory RG
open Slide (Stars)
open Trio (froth Mirrors Offer)
open AnalyticBridge VerifiedReset Push.AbsoluteSums Animals YM.Stationary Milling PertExtension.Series Exterior Precision Ion
open Pulse Spine Garf Steam Bloch Radial House Lumen Metric
open scoped Topology NNReal InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {α:Type} {G:Gauge}{n m c C:Side}{k w r z χ i j:ℕ} (w)
section before
variable (F:bore G){B:TableFee}{X: G.ColorIndex}{P:Bed}
variable (hP:Aegis X F P) (h:G.Simple)
local notation "L" => Link G m
def foster (v:ℕ) (i:ℕ): Story G:= match v with
  | 0=> 0
  | v+1=> if 2≤ i+v+1 then hue (cutF w (F (i+v+1-2) (v+1))) else 0
def lines (k i:ℕ): Story G:= ∑ l∈Finset.range (k-i),foster w F l i
lemma lines_loc (k i : ℕ): LocalOn (Lattice.box (w+1)) (lines w F k i):= by
   intro U V h; unfold lines; rw [Finset.sum_apply,Finset.sum_apply]; refine sum_congr rfl ?_; intro r _; cases r with
   | zero=> rfl
   | succ r=> simp only [foster]; split; · exact hue_loc _ (cutF_loc w _) U V h
              rfl
lemma lines_boat : Adapted (lines w F k i):= by
   intro u V; unfold lines; rw [Finset.sum_apply,Finset.sum_apply]; refine sum_congr rfl ?_; intro r _; cases r with
   | zero=> rfl
   | succ r=> simp only [foster]; split; · exact paints _ u V
              rfl
lemma foster_ana (k j:ℕ)(x:Site m) : altitude (pass (foster w F k j) m x):= by cases k ; exact analyticAt_const; simp only [foster]; split; exact adapted_hue (cut_adopts w _) x; exact analyticAt_const
lemma lines_l (x:Site m): altitude (pass (lines w F k i) m x):= by
   unfold altitude pass Function.comp lines; simp_rw [Finset.sum_apply]; exact (ContDiffAt.sum fun j _=> (foster_ana w F j i x).contDiffAt).analyticAt
lemma parcel : plays (pass (lines w F k i) m)= fun x=>∑ l∈Finset.range (k-i), plays (pass (foster w F l i) m) x:= by funext x; unfold plays pass froth lines Function.comp; simp_rw [Finset.sum_apply]; rw [sum_comm] -- adv
variable {F}
include hP
lemma spiny (C:ℕ) (hk: j+1+i<C+3) (he:2≤ i+j+1)(s:Signed)(x:L) : let v:=hair F m (i+j+1-2) (j+1); design v (orderTurn s x)=design v x:= by -- include hP
   intro v; let q:=wind (hair F m) (C+3) i; have hx:= (should hP.blazing).protects C m i (by omega)
   have hr : q∘orderTurn s=q:= funext (hx.spins s)
   have he y: jet q (j+1) y=design v y:= by rw [show jet q (j+1) y= grate (hair F m) i (j+1) y from (wind_jet ..).trans (if_pos hk)]; unfold grate v; rw [show i+(j+1)=_ from (show i+(j+1)=i+j+1 by omega),if_pos he]
   rw [← he,←he, ← woven (F:=q) hx.analytic (orderTurn s) x (j+1),hr]

variable {σ:ℝ≥0}
-- particular finite input/head price C_*; only through this grade, ready for uniform connection.
structure Tills (k:ℕ)(σ:ℝ≥0)(u:ℝ) (F:bore G) :Prop where
  cap (i r:ℕ) : i<k → r<k → Rooted (terrain σ _) (F i r) u
  nonneg : 0≤u
include h hP
lemma tune_prices {v:ℝ}(hh : Tills (k+3) σ v F)(hi:i<k+3)(x:L) : ‖jet (plays (pass (lines w F (k+3) i) m)) j x- jet (wind (hair F m) (k+3) i) j x‖ ≤ ((k+3:ℕ):ℝ)*((Fintype.card (Lines G m 1):ℝ)*(Real.exp (-(σ:ℝ)*w)*v))*‖x‖^j:= by
   rw [Model.parcel]; unfold wind; erw [Ion.loan_sum _ (fun v _=> froth_apt (foster_ana w F v i (m:=m))),Ion.loan_sum _ (fun i _=> grate_ana ..),← sum_sub_distrib]; refine (norm_sum_le ..).trans ((sum_le_sum (g:=fun _=>(Fintype.card (Lines G m 1):ℝ)*(Real.exp (-↑σ*w)*v)*‖x‖^j) ?_).trans ?_)
   · have hv:= hh.nonneg; intro u hu; have he:= mem_range.mp hu; let B:=(Fintype.card (Lines G m 1):ℝ)*(Real.exp (-(σ:ℝ)*w)*v)*‖x‖^j
     have hL: froth (pass 0 m) ∘ input G m=fun _=>0:=by ext x; simp [pass,froth]
     cases u with
     | zero=> unfold House.grate; rw [show foster w F 0 i=0 from rfl,hL,Convoy.jet_empty]; split
              next h=> rw [show hair F m (i+0-2) 0=0 from Lintel.Plata.hair_quiet hP _ (by assumption) _ _ (by omega)]; erw [show design (0:Field (Fin 0) (Lines G m 1))=(fun x=>0) from funext fun i=> by simp [design], Convoy.jet_empty]; simp only [sub_zero,norm_zero]; positivity
              erw [Convoy.jet_empty]; simp only [sub_zero,norm_zero]; positivity
     | succ u=> simp only [foster]; unfold House.grate; rw [show i+(u+1)=_ from (show i+(u+1)=i+u+1 by omega)]; split
                next hv=>
                  refine (sensing (s:=σ) (b:=v) (q:=_) w ?_ ?_ x ?_ j).trans ?_
                  · exact fun i=> (should hP.blazing).my.here i _ _
                  · exact hh.cap (i+u+1-2) _ (by omega) (by omega) -- ordering
                  · intro s; exact spiny hP k (by omega) hv s x
                  · split; exact le_rfl; positivity
                rw [hL]; simp_rw [Convoy.jet_empty]; simp only [sub_zero,norm_zero]; positivity
   rw [sum_const,nsmul_eq_mul,card_range]; have hv:= hh.nonneg; rw [mul_assoc ((↑(k+3:ℕ)):ℝ)]; apply mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.sub_le ..)) (by positivity)
end before
end YM.Contacts.Model
