import YM.MS.Vane.Akin
/-!
# Far progression along West from Mid.Seats. Decaying ∀ positive rank & RHS to scalar. Budget convenient $δ=ε_gain$.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Vane
open Set Function Filter Finset Metric MeasureTheory Real
open Koszul Plane Landau Detect Tone Momentum Heat High Frame Wire Signal Flux Wind Garment Outlook Latch Job Belt Rake Geo
open Osc Fiddle Snap City Book.Convolve
open scoped Topology ContDiff Interval
variable { I E W:Type}{G:Gauge}{P:Geo I}{x y:ℝ}{b:Bool}{h n a:ℕ}{F H:Glade G I}{ξ: I→QP}
local notation "Ω"=> West P
abbrev Vista (P: Geo I):= (West P).time
abbrev sale (p: Vista P):= exp (- eps_gain*(tstart p-P.θ p.1))
abbrev ace (h:ℕ)(x:ℝ)(p: Vista P):= exp ( (-(h:ℝ) - x) * P.θ p.1)
abbrev far (P:Geo I)(h:ℕ)(x:ℝ)(p:Vista P) := ace h x p* sale p
lemma FarBasis (P:Geo I)(h:ℕ)(x:ℝ): nn (far P h x):= fun _=> mul_nonneg ( exp_pos _|>.le ) (exp_pos _|>.le )
lemma paidW (p:Vista P): P.θ p.1 ≤ tstart p:= p.2.property
lemma today (p:Vista P): (West P).price.length p= exp ( tstart p ) := rfl
lemma expoW (p: Vista P) : sale p≤1:= by apply Real.exp_le_one_iff.mpr; exact mul_nonpos_of_nonpos_of_nonneg ( neg_nonpos.mpr p_gain.le ) ( sub_nonneg.mpr ( paidW p ))
lemma tax_far (k n:ℕ)(p:Vista P): far P k x p*far P n y p≤ far P (k+n) (x+y) p:= by
    have hx : ace k x p * ace n y p= ace (k+n) (x+y) p:= by unfold ace; rw [ ← exp_add ]; push_cast; congr 1; ring
    calc
       _ = ace k x p*ace n y p * sale p * sale p:= by unfold far; ring
       _ ≤ _:= by rw [hx]; exact mul_le_of_le_one_right (FarBasis P (k+n) (x+y) p) (expoW p) -- .val?
-- differences use extra ε charged at θ only
abbrev coinZ (P:Geo I): Vista P→ℝ:= fun p=> ace 0 eps_gain p
lemma zeta (h:ℕ): far P h eps_gain =coinZ P*far P h 0:= by
    ext p; simp only [coinZ,far,Pi.mul_apply,ace, ← Real.exp_add]; push_cast; congr 1; ring
lemma γ_non (i:Vista P): 0≤ coinZ P i:= (exp_pos _).le
lemma high_chip (i:Vista P): chips Ω i ≤ coinZ P i:= by unfold chips coinZ ace; apply Real.exp_monotone; simp only [Nat.cast_zero, neg_zero,zero_sub]; exact mul_le_mul_of_nonpos_left ( paidW i ) ( neg_nonpos.mpr p_gain.le )
lemma pos_pitch (w: Legs (Mode ( BH G ) E ))(hz:w.length≥1): 1≤pitch w:= by
    cases w with| nil=>simp at hz| cons i v=> obtain he:= nat_cost (G:=G) ⟨i.1,0⟩; obtain ht:= pitch_nn (G:=G) v; rw [pitch,field_cons]; exact le_add_of_sub_left_le ( (sub_nonpos_of_le he).trans ht ) -- name
lemma εdecal (p: Vista P): (West P).price.length p * sale p = exp (eps_gain*(tstart p+P.θ p.fst)):= by rw [ today ]; unfold sale; rw [ ← exp_add ]; congr 1; unfold eps_gain; ring
lemma stamp (p:Vista P): (West P).stream p = Set.Icc (P.θ p.1) (tstart p):= by ext; rfl
lemma broken : Break ( G:=G ) b true Ω (far P h x) (far P h x):= by
    intro E _ _ w hw ht; obtain hv:= ht rfl; refine ⟨ eps_gain,p_gain,?_ ⟩; apply slideGrade (k:=1) (εWest P) (by omega) _ (pos_pitch w (by omega)); refine ⟨ pos_nn _ ( FarBasis P h x ) _ ,1,zero_lt_one,?_ ⟩ -- implicit uniform
    intro p q hp he; unfold far; have hg : P.θ q.1=P.θ p.1:= hp ▸ rfl
    simp only [one_mul,zpow_one, show ace h x q= ace h x p from (by unfold ace; rw [hg]) ]; rw [mul_left_comm ((West P).price.length q), mul_left_comm ((West P).price.length p)]; -- reference? `Scale.length`
    rw [ εdecal, εdecal, mul_left_comm _ (ace _ _ _), ← Real.exp_add (-eps_gain*δf p q),hg,show -eps_gain*δf p q+eps_gain * (tstart p + P.θ p.fst)=eps_gain*(tstart q+P.θ p.fst) from (by unfold δf tstart; ring)]
lemma Wharf ( h:Fits b F H ): Dash b Ω F H (fun p=> F p.1 (P.θ p.1)):= Fits.lens _ _ _ h stamp -- lower implicit order.X
-- transport p-> Shore inlet
abbrev kick (p: Vista P): Stem P:= ⟨ p.1, P.θ p.1,show 0≤_∧ _≤_ from ⟨ P.room p.1,le_rfl ⟩ ⟩ -- ↥Gulf price
abbrev reachW (P:Geo I) (F: Glade G I)(p:Vista P): Law G:= F p.1 (P.θ p.1)
lemma belowK (p: Vista P): ( Gulf P ).price.length ( kick p ) = exp (P.θ p.1):=rfl
lemma aboveV (p: Vista P): exp (P.θ p.1) ≤ (West P).price.length p := by rw [today]; exact exp_monotone (paidW p)
lemma garage : Bus (West P).price ( Gulf P ).price kick:= by
    constructor
    · refine ⟨1,zero_lt_one,1,fun p=>?_⟩; simp only [pow_one,one_mul,mul_one,Function.comp_apply, Pi.one_apply]; change P.habitat p.1*(1+|P.θ _|) ≤ P.habitat p.1*(1+|tstart p|); rw [ abs_of_nonneg ( P.room _ ), abs_of_nonneg ( le_trans ( P.room _ ) (paidW p))]; gcongr; exact paidW p
    exact ⟨1,zero_lt_one,fun p=> by rw [one_mul,belowK]; exact aboveV p⟩
lemma matchκ (w:Legs (Mode (BH G) E))(hw:w.length≥1) (p:Vista P): (Gulf P).price.length ( kick p ) ^ ( pitch w ) * life P h 0 x ( kick p ) ≤ (West P).price.length p ^ ( pitch w ) * far P h x p:= by
    rw [belowK,today]; obtain hW:= pos_pitch w hw; obtain ht:= paidW p
    rw [ show life P h 0 x ( kick p ) = ace h x p from ?_ ]; swap; · simp [ life,tstart,ace] -- eq exponents only
    unfold far sale ace; rw [a_e, a_e,← exp_add, ← exp_add, ← exp_add]; apply Real.exp_monotone; have he: eps_gain ≤ (pitch w:ℝ):= s_gain.le.trans (by exact_mod_cast hW); nlinarith
lemma hop (hx: Here b false ( Gulf P ) F ( life P h 0 x )): Lease b true (West P).price (reachW P F) ( far P h x ):= fun E _ _ w hv he=> Job.ticket (P:=kick) garage ( hx.highp E w hv he ) (paidMono (fun i=> matchκ w (by have hh:= he rfl; omega) i)) ( pos_nn _ (FarBasis P h x) _ )
end YM.MS.Vane
