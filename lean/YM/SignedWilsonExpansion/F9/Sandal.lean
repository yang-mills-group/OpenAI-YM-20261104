import YM.SignedWilsonExpansion.F9.Occasion
import YM.WilsonCoeffUV.Marked.Step.Exponential
/-!
# Precisely age the terminal. Keep calibration numbers **outside** the re-timing.

Cover engineering is fully charged elsewhere. Re-expression `rear` needed to
use the original measured unit at v rather than v' or ℓ. Scalar cap unit clock
at M travels exactly, before comparisons on any epoch regulator. This phase
compares cutoffs N→Kφ in the formal actionW **after** original F9 estimates.
-/
set_option autoImplicit false
set_option maxHeartbeats 750000
noncomputable section
namespace YM.WilsonCoeffUV.Mer.Xa
open Wilson Gauge AnalyticNext.QuarticMatch.Sheets Filter Function Matrix Lattice RG Laurent Bloch Metric
open Blue FreeResolvent Work.F08 Bank Soil Exterior Next.Free Tree Precision Power Embroider
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb
open Realm Fountain PathCost Embroider.Canvas Shard PowerSeries
open Supply Ticket Polestar Next.Foundations Patrol Shard.Plan
open Wheel.Mark (pieceO piece_auth)
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{A:Levels G}{Ñ:ChartRatio G}{J:Type*}{e s k h m c v b T N M i j l r p u :ℕ}{x y: Cost}
variable {B Q D Z X Y η t a:ℝ}{E W U:Credit}
local notation "Fz" => PowerSeries.X
variable {P Q':Era G ℝ}{R: Realm G (e+1) E}
variable {g:G.Simple}
section terminal
abbrev dew (P:Era G ℝ):Cost:= ScalarTrim P.2
lemma dew_coeff (P:Era G ℝ) : coeff e (dew P)=P.2 e 0 Fin.elim0:= coeff_mk _ _
lemma dew_auth (f:Respect k e u t P Z)(u':0≤t): FitS e (dew P) Z:=by
   intro i h; have p:= f.anchor i h 0; have he:=p.2.1.sum_le_tsum ({Fin.elim0} : Finset (dock Cover (Hooks G) 0)) (fun i _=>p.1 i); rw [Finset.sum_singleton] at he; rw [dew_coeff]; exact (le_mul_of_one_le_left (norm_nonneg _) (autumn_pos u' _ _)).trans (he.trans p.2.2)
lemma dew_flat (x:Cost)(P:Era G ℝ): dew (trim x P)= x*dew P:= by ext1 e; rw [dew_coeff, coeff_mul]; simp_rw [dew_coeff]; unfold trim affix; simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
lemma dew_sub (P Q:Era G ℝ): dew (P-Q)=dew P-dew Q:=by ext1 e; rw [map_sub,dew_coeff,dew_coeff,dew_coeff]; rfl
lemma dew_add (P Q:Era G ℝ): dew (P+Q)=dew P+dew Q:=by ext1 e; rw [map_add,dew_coeff,dew_coeff,dew_coeff]; rfl
lemma dew_smul (a:ℝ)(P:Era G ℝ): dew (a • P)=a • dew P:=by ext1 e; rw [map_smul, dew_coeff, dew_coeff]; rfl
lemma dew_piece : dew (pieceO G)=1:=by ext e; rw [dew_coeff]; rfl
-- bulk venue moving shape under point residents. mixed precision uses `memory`
lemma calendarCovers (p:P.2=Q'.2)(A:Levels G)(Ñ:ChartRatio G)(h:m≤ c): (cruises A Ñ N k c m P).2=(cruises A Ñ N k c m Q').2:=by
    induction h using Nat.decreasingInduction with
    | self=> rw [cruises_top,cruises_top]; exact p
    | of_succ i he ih=> rw [cruises_sub _ _ _ _ P he,cruises_sub _ _ _ _ Q' he]; unfold verseI; rw [ih]
lemma calendarX (g:G.Simple)(p:LocalRatio Ñ)(h:m≤ c)(t:c≤N)(x:Cost)(hP:Auth k P): cruises A Ñ N k c m (trim x P)=trim (toward A Ñ N m c x) (cruises A Ñ N k c m P):=by
    induction h using Nat.decreasingInduction with
    | self=> rw [cruises_top,cruises_top]; simp only [toward,Nat.sub_self, relativeF,palmB,reel_one]
    | of_succ i he ih=> rw [cruises_sub _ _ _ _ _ he, cruises_sub A Ñ N k P he,ih, toward_join x A Ñ (Nat.le_succ i) he,toward_next]; exact step_composed g (he.trans_le t) p _ _ (cruising A g p he t hP)
-- one column transported through all dates.L.Fence.
lemma calendarUnit (g:G.Simple)(p:LocalRatio Ñ)(h:m≤ c)(t:c≤N): cruises A Ñ N k c m (pieceO G)=pieceO G:=by
    induction h using Nat.decreasingInduction with
    | self=> exact cruises_top ..
    | of_succ i he ih=>
       rw [cruises_sub _ _ _ _ _ he,ih]; apply Auth.ext (Auth.verse A (he.trans_le t) g p (piece_auth)) (piece_auth (j:=k)); funext n; dsimp only [pieceO,verseI]; rw [rumble,reset_zinc,map_one]
lemma calendarGrow (g:G.Simple)(p:LocalRatio Ñ)(h:m≤ c)(t:c≤N)(hP:Auth k P)(q:k≤l): cruises A Ñ N k c m P=cruises A Ñ N l c m P:=by
    induction h using Nat.decreasingInduction with
    | self=> rw [cruises_top,cruises_top]
    | of_succ i he ih=>
       rw [cruises_sub A Ñ N k P he, cruises_sub A Ñ N l P he,←ih]; exact verseExpand A (he.trans_le t) g p (cruising A g p he t hP) q
lemma vapor (P:Era G ℝ) : (P-axeR P).2=(trim (dew P) (pieceO G)).2:=by
    funext i r; let U:=trim (dew P) (pieceO G); cases r with
    | zero=> funext v; let X:= dew_flat (dew P) (pieceO G); rw [dew_piece, mul_one] at X; have H:= congr_arg (coeff i) X; simp_rw [dew_coeff] at H; rw [show v=Fin.elim0 from Subsingleton.elim ..]; change P.2 i 0 _-lop P.2 i 0 _=U.2 i 0 _; simp only [lop,↓reduceIte,Pi.zero_apply,sub_zero]; exact H.symm
    | succ r=> unfold trim; simp only [Prod.snd_sub,Pi.sub_apply,axeR,lop, ite_false,if_neg (by omega : r.succ ≠ 0),sub_self, affix, Finset.sum_apply,Pi.smul_apply,pieceO]; symm; refine Finset.sum_eq_zero fun j _=>?_ ; rw [uband,shine_dark (by omega), smul_zero]
lemma booking (g:G.Simple)(p:LocalRatio Ñ)(h:m≤ c)(t:c≤N)(hP:Auth k P):
     dew (cruises A Ñ N k c m P)- dew (cruises A Ñ N k c m (axeR P))=toward A Ñ N m c (dew P):= by
    rw [← dew_sub,← cruisePlus A h g p t hP hP.axe]; let v:=vapor P
    change ScalarTrim _= _; rw [calendarCovers v A Ñ h]; change dew (cruises A Ñ N k c m (trim (dew P) (pieceO G)))= _; rw [calendarX g p h t _ piece_auth, calendarUnit g p h t,dew_flat,dew_piece,mul_one]
lemma dew_sum (S: Finset J)(P:J→Era G ℝ) : dew (∑ i∈S,P i)= ∑ i∈S,dew (P i):=by ext1 i; simp_rw [map_sum,dew_coeff]; simp only [Prod.snd_sum,Finset.sum_apply]
end terminal
section age
-- ℓ=m, charge the ore even when v=c
abbrev FadeRaw (A:Levels G)(Ñ:ChartRatio G)(N k m c:ℕ)(P:Era G ℝ):= dew (cruises A Ñ N k c m P)
def vaporC (G:Gauge)(k e:ℕ)(E W:Credit):Credit:= (Canopy.pageS G (e+1) E).prodC ((cabin G k e 0 E W).prodC (westW G k e 0 E W))
variable (d:Dormitory R k 0 W)(a':Canopy R m c Z)(hP:Respect k e 0 0 P B)
include d a' hP
/-- Change top-height of the formal heat engine, *after* actual signed estimate. Stop at v
pays only the nonconstant remainder after re-timing the full Σ. No gauge-mean dropping.
-/
theorem warmth_fee (hv:m≤v)(t:v≤c)(u:c≤b)(p:b≤N)(q:b≤M) :
   FitS e (rear R.draws R.paid M m v (FadeRaw R.draws R.paid M k m c P) - FadeRaw R.draws R.paid N k v c P)
       ((vaporC G k e E W).buy Z*R.tempC v c*B+(windy G k e 0 E W).buy Z*B*R.tempC c b):=by
    let A:=R.draws; let Ñ:=R.paid; let s:=rear A Ñ M m v; let P' := cruises A Ñ M k c v P; let f:= FadeRaw A Ñ M k m c P; let Q:= P'-axeR P'; have Hv:=t.trans (u.trans q)
    let wf:=a'.cut hv t (le_refl c); let T:=a'.cut (le_refl m) hv t; let g:= R.hG; let h:=R.green; have hH:=hP.auth; have ht:Auth k P':= cruising A g h t (u.trans q) hH
    let V:=cruises A Ñ M k v m (axeR P'); let D:=dew P'; let X:= FadeRaw A Ñ N k v c P
    let γ:ℕ→ℝ:= fun _=>0; have hr:=memory (ξ:=γ) d wf wf.bare (u.trans q) hP; have he:= voyage (ξ:=γ) d T T.bare Hv hr
    have hz: f-dew V= toward A Ñ M m v D:=by unfold f FadeRaw; rw [cruisesMore A Ñ P hv t]; exact booking g h hv Hv ht
    have hs : s f-X= s (dew V)+(D-X):=by rw [show f= _ from (sub_eq_iff_eq_add.mp hz), map_add,show s (toward A Ñ M m v D)=D from rear_toward D hv g h Hv]; abel -- fix
    have hx:= recalled d wf γ wf.bare b u q p hP
    change FitS e (s f-X) _; rw [hs]; refine FitS.plus ?_ ?_
    · refine ((T.direction_cost Hv (dew_auth he (le_refl 0)) (by omega)).2).more (le_of_eq ?_); unfold vaporC; rw [Credit.products,Credit.products]; ring
    change FitS e (dew _-dew _) _; rw [← dew_sub]; exact dew_auth hx le_rfl
end age
end YM.WilsonCoeffUV.Mer.Xa
