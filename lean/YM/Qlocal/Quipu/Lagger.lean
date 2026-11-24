import YM.Comparison.RG02.Assembly.Radial
/-!
# order-axis shifts preserve marking (power and vertices sold later)

`delay f` respects the Ring of symmetric coupling jet tables with each conditional set of marks tilted, all field-independent entries, and no changes to forest. Don't recalculate free itinerary.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Quipu.Lagger
open Finset Function YM.Marker YM.Multi YM.Primitives.GCC.Anchor
open YM.Extra.Trajectories (connected connected_quiet pass_connected part_sub pass_inj)
open YM.Comparison.RG02.Cumulants YM.Comparison.RG02.Order
open YM.Comparison.RG02.Order.Join
open YM.Comparison.RG02.Order (Symmetric)
open scoped BigOperators Classical
variable {V : Type} [DecidableEq V] {R : Census V} {r k : ℕ}
def dues (f:V→ℕ) (s:R.Mode) := ∑ i∈s.val, f i
variable (f:V→ℕ)
local notation "δ"=> dues f
lemma dues_add {x y s:R.Mode}(h: Poly.merges x y s): dues f x+dues f y=dues f s:= by unfold dues; rw [← h.2,sum_union h.1]
lemma dues_home : dues f R.quiet=0 := Finset.sum_empty
local notation "C"=> PTable R
variable (P Q:PTable R)(s:R.Mode)
def pauseC (P:PTable R) : PTable R:= PowerSeries.mk fun k=> Poly.inject fun i=> if dues f i ≤ k then (PowerSeries.coeff (k-dues f i) P).part i else 0
abbrev cell (P:PTable R) (s:R.Mode) (k:ℕ):= (PowerSeries.coeff k P).part s
lemma ask : cell (pauseC f P) s k= if dues f s≤k then cell P s (k-dues f s) else 0:= by unfold cell pauseC; rw [PowerSeries.coeff_mk]; rfl
lemma due : cell (pauseC f P) s (k+dues f s)=cell P s k:= by rw [ask,if_pos (by omega),Nat.add_sub_cancel]

def beam (P:PTable R)(v:R.Mode) := PowerSeries.mk (cell P v)
lemma beat (P:PTable R)(v:R.Mode) : cell P v k = PowerSeries.coeff k (beam P v):=(PowerSeries.coeff_mk ..).symm
lemma bills_equal {P Q:PTable R} (h:∀ k s,cell P s k=cell Q s k):P=Q:= by ext1 i; exact Poly.ext (h _)
lemma beam_mul_eq (s:R.Mode): beam (P*Q) s=∑ i:R.Mode, ∑ j:R.Mode, if Poly.merges i j s then beam P i * beam Q j else 0 := by
   ext1 k; unfold beam; simp only [map_sum]; nth_rw 1 [PowerSeries.coeff_mk]; rw [cell,PowerSeries.coeff_mul, Poly.part_sum]; simp_rw [Poly.part_mul];
   rw [sum_comm]; apply Finset.sum_congr rfl; intro i _; rw [sum_comm]; apply Finset.sum_congr rfl; intro j _; by_cases hx:Poly.merges i j s; simp_rw [if_pos hx]; rw [PowerSeries.coeff_mul]; simp_rw [PowerSeries.coeff_mk]
   simp [hx]
local notation "K"=>pauseC f
lemma lean_beam (s:R.Mode): beam (pauseC f P) s=beam P s * PowerSeries.X^(dues f s):= by
  ext1 k; rw [← beat, ask, PowerSeries.coeff_mul_X_pow']; split_ifs; exact beat _ _; rfl
lemma pact : pauseC f (P*Q)=pauseC f P*pauseC f Q:= by
  apply bills_equal; intro k s; rw [beat,beat,lean_beam, beam_mul_eq P Q, Finset.sum_mul,beam_mul_eq (K P)]; refine congr_arg _ (Finset.sum_congr rfl (fun i _=>?_)); rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro j _; split
  next he=> rw [lean_beam,lean_beam,← dues_add f he,pow_add]; ring
  simp
lemma corr : pauseC f (P+Q)=pauseC f P+pauseC f Q:= by
 apply bills_equal; intro k s; unfold cell; simp only [map_add, Poly.part_plus]; change cell (K (P+Q)) s k= cell (K P) s k+ cell (K Q) s k; rw [ask f (P+Q) s, ask f P s,ask f Q s]; split
 · simp [cell]
 simp
lemma fuel (b:ℂ) : K (b•P) = b • K P:= by
 apply bills_equal; intro k s; rw [ask]; unfold cell; rw [PowerSeries.coeff_smul, PowerSeries.coeff_smul]; simp only [Poly.part_smul]; change _ = b * cell (K P) s k; rw [ask f P s]; split; rfl; simp
lemma awake : K (1:PTable R)=1:= by
 apply bills_equal; intro k s; rw [ask]; by_cases hx:s= R.quiet
 · subst s; rw [dues_home]; simp
 have he(k:ℕ):cell (1:PTable R) s k=0:=by
    unfold cell; rw [PowerSeries.coeff_one]; split; rw [Poly.one_part]; exact if_neg hx; rfl
 split; · rw [he,he]
 exact (he _).symm
lemma alone : K (0:PTable R)=0:= by apply bills_equal; intro k s; rw [ask]; split <;>simp [cell]
section grading
variable [Fintype V]
def season (x:Grade R r):= series R r (pauseC f (collect x))
lemma season_w (v:Grade R r) : Symmetric (season f v):= Symmetric.known _
lemma equity (k:ℕ)(hs:k ≤ r)(x:Grade R r)(s:R.Mode): (observe R r (season f x) k).part s=if dues f s≤k then (observe R r x (k-dues f s)).part s else 0:= by
 unfold season; rw [observation _ _ _ hs]; change cell _ _ _=_; rw [ask f]; simp only [cell, collect_coeff]
lemma jetting : season f (series R r P)=series R r (K P):= by
 apply (sym_coeff _ _ (season_w f _) (Symmetric.known _)).mpr; intro j hj; ext1 s; rw [equity f j hj,observation R r (K P) hj]; change _=cell _ s j; rw [ask]; rw [observation R r P ((Nat.sub_le ..).trans hj)] -- annot
lemma seasons (p q:Grade R r): season f (p+q)= season f p +season f q:=by
 unfold season; rw [show collect (p+q)= collect p+collect q by ext1 i; rw [collect_coeff,observe_add,map_add,collect_coeff,collect_coeff], corr, map_add]
lemma quarterly (x:Grade R r)(b:ℂ): season f (b•x)= b • season f x:= by
 unfold season; rw [show collect (b•x)= b • collect x by ext1 i; rw [collect_coeff,observe_smul,PowerSeries.coeff_smul,collect_coeff], fuel, series_smul]
lemma seasonal (p q:Grade R r)(h:Symmetric p)(H:Symmetric q): season f (p*q)=season f p*season f q:= by obtain ⟨x,rfl⟩:=h; obtain ⟨y,rfl⟩:=H; rw [← map_mul,jetting, pact, jetting, jetting, map_mul]
abbrev pace (R:Census V)(r:ℕ): Grade R r →ₗ[ℂ] Grade R r where
 toFun:= season f
 map_add' := seasons f
 map_smul' x p:= quarterly f p x
lemma season_zero : season f (0:Grade R r)=0:=map_zero (pace f R r)
lemma season_one : season f (1:Grade R r)=1:= by
 rw [← show series R r (1:PTable R)=1 from map_one (series R r),jetting, awake]
lemma season_powers (p:Grade R r)(h:Symmetric p)(k:ℕ): season f (p^k)=season f p^k:= by induction k with
 | zero=> rw [pow_zero,pow_zero,season_one]
 | succ n ih=> rw [pow_succ,seasonal f (p^n) p (h.pow n) h,ih,pow_succ]
lemma season_pass (p:Grade R r)(h:Symmetric p) : season f p.pass= (season f p).pass:= by
   change (pace f R r) p.pass= _; unfold Poly.pass; rw [map_sum]; refine Finset.sum_congr rfl fun i _=> ?_; rw [map_smul]; exact congr_arg ((i.factorial:ℂ)⁻¹ • ·) (season_powers f p h i)
lemma cent (p:Grade R r) : (observe R r p 0).part R.quiet= p.part (Board R r).quiet:= by
 have hh: pick r 0=(indices r).quiet:=Subtype.ext (card_eq_zero.mp (picked r (Nat.zero_le _))); rw [observe, if_pos (Nat.zero_le _),Poly.part_smul,Nat.factorial_zero,Nat.cast_one,inv_one,one_mul]; unfold Poly.inject; change p.part (pair _ _)= _; rw [hh,pair_quiet]
lemma season_floor (p:Grade R r) : (observe R r (season f p) k).part R.quiet=(observe R r p k).part R.quiet:=by
 by_cases he:k≤ r; rw [equity f k he]; simp [dues_home f]; simp [observe,he]
lemma ray_blank (p:Grade R r) : (season f p).part (Board R r).quiet=p.part (Board R r).quiet:=by
 rw [← cent, season_floor, cent]
lemma season_log {x:Grade R r} (h:Symmetric x)(hP:x.part (Board R r).quiet=1): season f (connected x)= connected (season f x):= by
 apply pass_inj ((ray_blank f _).trans (connected_quiet hP)) (connected_quiet ((ray_blank f _).trans hP)); rw [← season_pass f _ (h.log hP), pass_connected hP, pass_connected ((ray_blank f x).trans hP)]
end grading
end YM.Qlocal.Quipu.Lagger
