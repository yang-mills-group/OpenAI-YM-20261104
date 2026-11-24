import YM.FVAAlt2.Home.AxiomFree
/-!
# Leading oil ledger. Real MS knobs at the Physics launch. No charge of
 the *normalization* is spent here; D0=I proved without assuming Orientation.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2.Home.Report
open Function Finset Filter Topology Lattice
open Precision Extra.FD Maxwell Labels Extraction
open FormalOPE PertExtension PertExtension.LatticePT PertExtension.Position FormalOPE.RG10.InversionTop
open MS MS.Local.Physical MS.Koszul MS.Menus MS.Book MS.Plane MS.Theater MS.Land
open MeasureTheory Matrix
open PowerSeries (C coeff constantCoeff)
open Profiles
open RG10.Position (Plan)
open scoped Topology BigOperators ContDiff PowerSeries Classical Matrix
variable {G:Gauge}{L:Frames G}{B:MS.Local.Physical.Deck G}{M:Booked B}{H:Source.Hol G}
variable {d n:ℕ}
set_option linter.unusedSectionVars false
local notation "F"=> Glyph B d
local notation "PS"=> PowerSeries ℝ
local notation "PSc"=> PowerSeries ℂ
variable (K:MS.Land.Prescription B)(q:ℕ+)(μ:ℝ) -- n shadow remove

abbrev beamA (K:Prescription B)(x a:ℝ)(d:ℕ) := (aboard K a x d).map takeReal
def beam0 (K:MS.Land.Prescription B)(x a:ℝ)(d:ℕ):= (beamA K x a d).map PowerSeries.constantCoeff
lemma beam_t(x a:ℝ)(p:F)(j:Glyph B (Lobby.owner p).h): beam0 K x a d p (up (high p) j) = a^(( j.size:ℤ )-(↑p.size:ℤ)) * ((K.fees (Lobby.owner p).h (Lobby.owner p).item 0).register j).eval x:=by
 unfold beam0 beamA; rw [Matrix.map_apply,Matrix.map_apply,onOil, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, takeReal,PowerSeries.coeff_mk, rel,Lobby.changePrice, PowerSeries.coeff_C_mul,Billing.bore,PowerSeries.coeff_mk]; unfold oil; change ((a:ℂ)^((j.size:ℤ)- (↑p.size:ℤ)) *((((K.fees _ _ 0).register j).eval x:ℝ):ℂ)).re=_; rw [← Complex.ofReal_zpow, ← Complex.ofReal_mul,Complex.ofReal_re]
lemma beam_no (x a:ℝ)(p j:F)(h: j ∉ Set.range (up (high p) (B:=B))): beamA K x a d p j=0:=by
 unfold beamA aboard oilPoint; rw [Matrix.map_apply,Matrix.of_apply, Finset.sum_eq_zero (fun i _=>if_neg (show up _ i≠j from fun e=> h ⟨i,e⟩))]; change takeReal 0=0; unfold takeReal; ext i;rw [PowerSeries.coeff_mk,map_zero]; simp
lemma light0 (x a:ℝ)(p j:F)(he:p.grade≤ j.grade): beam0 K x a d p j=(1:Matrix F F ℝ) p j:=by
 let i:=MS.Land.read (B:=B) (Lobby.owner p).item
 by_cases hx:p=j; subst j; have H :↑i.grade≤p.grade:=le_rfl; have h': up (high p) i=p:= (lampu p (high p)).symm
 · have hz : (K.fees (Lobby.owner p).h (Lobby.owner p).item 0).register i=1:= Eq.trans ((K.init (Lobby.owner p).h (Lobby.owner p).item).Single i le_rfl) (if_pos rfl)
   calc _ = beam0 K x a d p (up (high p) i):= congr_arg (beam0 K x a d p) h'.symm
        _ = _:= by rw [beam_t,hz,show ( (i.size:ℤ)-(↑p.size:ℤ))=0 from sub_self (p.size:ℤ)]; simp
 by_cases hy:j∈Set.range (up (high p) (B:=B))
 · obtain ⟨u,rfl⟩:=hy;
   rw [beam_t,(K.init (Lobby.owner p).h (Lobby.owner p).item).Single u he,if_neg (show u≠i from fun ht=> hx (Eq.trans (lampu _ _) ( congr_arg _ ht.symm))), Polynomial.eval_zero,Matrix.one_apply_ne hx,mul_zero]
 rw [beam0,Matrix.map_apply,beam_no K _ _ _ _ hy, map_zero,Matrix.one_apply_ne hx]
lemma polynomial_rigid (P:Polynomial ℝ)(c:ℕ→ℝ)(hc:Tendsto c atTop atBot)(h:Tendsto (fun i=>P.eval (c i)) atTop (𝓝 0)): P=0:=by
 by_cases hv:0<P.degree
 · have hu : Tendsto (fun x:ℕ=> |P.eval (c x)|) atTop atTop:= (Polynomial.abs_tendsto_atBot _ hv).comp hc; exact False.elim ((not_tendsto_atTop_of_tendsto_nhds h.abs) hu)
 have hx:P=Polynomial.C (P.coeff 0):= Polynomial.eq_C_of_degree_le_zero (le_of_not_gt hv); rw [hx] at h; have hy:P.coeff 0=0:= tendsto_nhds_unique (f:=fun i:ℕ=>P.coeff 0) tendsto_const_nhds (by simpa only [ Polynomial.eval_C ] using h); rw [hy,map_zero] at hx; exact hx
include μ
-- from asymptotic small conclude all prices.Pay.
lemma rigidity(hq:1<q.val)(p j:F)(h:Tendsto (fun n=>beam0 K (μ-Profiles.Θ q n) (epsilon q n) d p j) atTop (𝓝 0)) (x a:ℝ): beam0 K x a d p j=0:=by
 by_cases he:j∈Set.range (up (high p) (B:=B)); swap; · rw [beam0, Matrix.map_apply,beam_no K _ _ _ _ he,map_zero]
 obtain ⟨v,rfl⟩:=he; rw [beam_t]; simp_rw [beam_t] at h; let P:=(K.fees (Lobby.owner p).h (Lobby.owner p).item 0).register v; -- infer with label
 let X(i:ℕ):= epsilon q i; let d':= p.size-v.size; have hz:v.size≤ p.size:=Nat.le_of_lt_succ v.1.isLt;
 let c(i:ℕ):= μ-Θ q i; have ht:Tendsto c atTop atBot:= by unfold c; simp_rw [sub_eq_add_neg]; exact tendsto_atBot_add_const_left _ _ (Filter.Tendsto.comp tendsto_neg_atTop_atBot (grows hq) )
 have hu:(v.size:ℤ) -p.size= - ( d' :ℤ ):= by unfold d'; omega
 have hh:P=0:= by
    apply polynomial_rigid _ c ht; rw [hu] at h; let A i:= X i ^ (-( d' :ℤ )); let t:ℝ:=(0:ℝ)^d'; have hx:Tendsto (fun i=> X i ^ d') atTop (𝓝 t):= (((epsilon_zero hq).mono_right inf_le_left ) : Tendsto X atTop (𝓝 0)).pow _
    refine (( (show Tendsto (fun i=> A i * P.eval (c i)) atTop (𝓝 0) from h).mul hx ).congr (fun i=>?_)).mono_right (le_of_eq (by rw [zero_mul]))
    unfold A; rw [_root_.zpow_neg,zpow_natCast, mul_right_comm, inv_mul_cancel₀ (pow_ne_zero _ (epsilon_pos q i|>.ne')),one_mul]
 unfold P at hh; rw [hh, Polynomial.eval_zero,mul_zero]
end YM.FVAAlt2.Home.Report
