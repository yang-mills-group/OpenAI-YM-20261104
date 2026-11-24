import YM.OPE.Loom.Observation
/-!
# Supply the transparent length-stride estimate on the enlarged comparison
Just on the short interval chosen for this one grouping; a single
non-restoration step. Keeping `CurvePay` simple here. -/
set_option autoImplicit false
noncomputable section
open Filter Function Set
open scoped Topology BigOperators Classical
namespace YM.OPE.Loom
open Lattice RG Wilson MergeProof Accent Ribbons Source Overlay
open Bid ManyCopies PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Mallow Bandage
open Push Marker
variable {G:Gauge} {C:Family G} {I J V : Type} [Fintype V] [Fintype J] {φ : Filter I} {T a c d : I→ℝ} {m k j : ℕ} {b v r : ℝ} {W : J→ℝ}
local notation "Y" => C.path.levels
local notation "X" => C.path.levels.clock.hatBeta
local notation "S" => C.S
local notation "P" => C.path.levels.budget
local notation "δ" => renal C.path.levels
local notation "ψ" => near C.path.levels
local notation "ζ" => fly C.path.levels
set_option quotPrecheck false
lemma count_earns {k:ℕ} : 1≤δ k * Real.exp ((count C 50 k:ℝ)/24):= by
    let t:= (X) (k+1); have ht: 1<t:= ((Y).fits.delayed _); have hz:0 < Real.log t := Real.log_pos ht
    let q:=(count C 50 k:ℝ); have hx: (50:ℝ)* Real.log t ≤ q:= by exact_mod_cast (Nat.le_ceil ((50:ℝ)* Real.log t)) --?? Nat cast
    have hp : 2*Real.log t ≤ q/24:= by linarith only [hz,hx]
    change 1 ≤ t^(-(2:ℝ))*_
    rw [Real.rpow_neg (show 0≤t by positivity), ← div_eq_inv_mul, Real.rpow_two,one_le_div (by positivity)]
    apply le_trans _ (Real.exp_monotone hp); rw [mul_comm 2, Real.exp_mul,Real.exp_log (by positivity),Real.rpow_two] -- orientation
lemma peg_nonempty [DecidableEq V]{n:Side}{i:ℕ}{B:Census V}{x:V→ℝ}{y:V→ℝ}{o:V→Site n}(he:∀ i,0<x i)(hf:∀ i,0<y i)(hx:∀ v,y v≤ x v)
    (hp: ∀ s:B.Mode,2 ≤ s.val.card→∀ a∈s.val,∀ b∈s.val,a≠b→ stride C 50 i-4 ≤ separation (o a) (o b)) : Repegs o (P i).B (fun a=>δ i*x a) y (1/2) 1 B:= by
    have hδ:0 < δ i:= Real.rpow_pos_of_pos (zero_lt_one.trans ((Y).fits.delayed _)) _
    refine buys (p:=count C 50 i) (by intro s h a ha b hb he; simpa [stride] using! hp s h a ha b hb he) ((P i).B_pos) (count_pos (by norm_num)) hf (fun a=>mul_pos hδ (he a)) ?_
    intro a; exact (hx a).trans ((le_mul_of_one_le_right (he a|>.le) count_earns).trans_eq (by ring))
omit [Fintype V] in
lemma erase [DecidableEq V]{n:Side}{i:ℕ}{B:Census V}{x:V→ℝ}{y:V→ℝ}{o:V→Site n}(hf:∀ i,0<y i)(hx:∀ v,y v≤ δ i*x v) : Repegs o (P i).B (fun a=>δ i*x a) y (1/2) 1 B:= by
    intro s hs p hp; rw [one_mul]; unfold Poly.toll
    apply (Finset.prod_le_prod (fun i _=> (hf i).le) (fun i _=> hx i)).trans
    exact le_mul_of_one_le_right (Finset.prod_nonneg (fun i _=> (hf i|>.le).trans (hx _))) (Real.one_le_exp (by positivity))

-- no erasures in cost except indicated k=m+1. fits terminal after attempt at m.
def priced (C:Family G)(k j : ℕ)(u:ℝ)(i:ℕ) := ((if i=k then renal C.path.levels k else 1)*(C.S.a j/C.S.a i)^4*u)
lemma price_pos {i:ℕ}(hr:0<r) : 0 < priced C k j r i := by
   unfold priced; have ht:= (S).a_pos i; have hp:= (S).a_pos j; have hh:0 < δ k:= Real.rpow_pos_of_pos (zero_lt_one.trans ((Y).fits.delayed _)) _; split <;> positivity
lemma price_march (hk:k ≤ m)(hr:0<r) : 6*((C.S.block m).val:ℝ)*priced C k j r m ≤ priced C k j r (m+1):=by
   have he:m+1≠k:=Nat.ne_of_gt (by omega); unfold priced; rw [if_neg he,one_mul];
   let L:ℝ:= (C.S.block m).val; let V:= C.S.a j/C.S.a m
   have hL:2 ≤ L:= size_enough C.path m; have hL':0 < L:= zero_lt_two.trans_le hL; have hδ : δ k≤ 1:= Real.rpow_le_one_of_one_le_of_nonpos (((Y).fits.delayed _).le) (by norm_num); have h':(if m=k then δ k else 1) ≤1:= by split; exact hδ; rfl
   have hI:0≤ V:= div_nonneg ((S).a_pos _).le ((S).a_pos _).le; rw [show C.S.a j/C.S.a (m+1)=V*L from by unfold V L; rw [Schedule.a_step]; field_simp]
   have ht:6*L≤L^4:=calc _ ≤ 2^(3:ℕ)*L:=by linarith only [hL]
                           _ ≤ L^3*L:=by gcongr
                           _ = _:=by ring
   change _*( (if m=k then δ k else 1)*V^4 *r) ≤ _
   apply le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (mul_le_of_le_one_left (pow_nonneg hI _) h') hr.le) (show 0≤6*L by positivity))
   refine (mul_le_mul_of_nonneg_right ht (show 0≤ V^4*r by positivity)).trans_eq ?_; ring
lemma price_next (hk:k ≤ m)(hr:0<r) : priced C k j r m ≤ priced C k j r (m+1) :=
   (le_mul_of_one_le_left (price_pos (C:=C) hr).le (show 1 ≤ 6*((C.S.block m).val:ℝ) by linarith only [size_enough (C.path) m])).trans (price_march hk hr)
lemma price_last (hr:0 < r) : priced C k j r k ≤ δ k * priced C k j r (k+1):=by
   unfold priced; rw [if_neg (Nat.ne_of_gt (show k<k+1 by omega)),one_mul,if_pos rfl,mul_assoc]; have hL:0≤ δ k:= (Real.rpow_pos_of_pos (zero_lt_one.trans ((Y).fits.delayed _)) _).le
   have hh:= le_of_lt ((S).strictAnti (Nat.lt_succ_self k)); have ha := (S).a_pos k; have hb:= (S).a_pos (k+1); have ht:= (S).a_pos j; gcongr
lemma price_top (hk:k < j) : priced C k j r j=r:=by unfold priced; simp [Nat.ne_of_gt hk,(C.S.a_pos j).ne']
end YM.OPE.Loom
