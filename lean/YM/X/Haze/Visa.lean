import YM.X.Haze.Tile
/-!
# Hazy bills with two exponents, get physical limits along annuli.
Tendsto only required along punctured profiles. integer ℤ cost for native a,b.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Haze
open Lattice Wilson Next.Rank CellsInt Beamer Interval PertExtension LatticePT Normal Filter Set Function Metric MeasureTheory Asymptotics
open Reed Stems Fielding Print
open scoped Topology BigOperators Classical ENNReal
variable {q : ℕ+} (hq:1<q.val) {n:Side} {k m v:ℕ} {R:ℝ}
local notation "Fℕ"=>(atTop:Filter ℕ)
local notation "ε"=>epsilon q
variable {V:Type*}[NormedAddCommGroup V][NormedSpace ℝ V] {a b c d:ℤ}
def price (q:ℕ+)(a b:ℤ)(i:ℕ)(z:Cover):ℝ:= (epsilon q i)^a*(day z)^b
lemma price_pos (q:ℕ+)(a b:ℤ)(i:ℕ)(z:Cover):0< price q a b i z:= mul_pos (zpow_pos (epsilon_pos q i) a) (zpow_pos (day_pos z) b)
abbrev Mist (V:Type*):= ℕ→Cover→ V
def Visible (q:ℕ+)(R:ℝ)(s:ℤ)(f:Mist V):Prop:=∃ C:ℝ,0≤C∧ ∀ᶠ i in Fℕ, ∀ z,street z ≤ gate q R i→ ‖f i z‖ ≤ C*price q 0 s i z -- remove
structure Visa (q:ℕ+)(R:ℝ)(a b:ℤ)(f:Mist V):Prop where
   who : ∃ C:ℝ,0≤C∧ ∀ᶠ i in Fℕ,∀ z:Cover,street z ≤ gate q R i→ ‖f i z‖ ≤ C*price q a b i z
   whereL(x:E4)(hx:x≠0)(hy:‖x‖≤R)(z:Fielding.Walk)(hz:plot q z x): Released (fun i=> ((epsilon q i) ^(b-a)) • f i (z i))
lemma decomp (b c:ℤ)(i z) : price q a b i z * price q c d i z = price q (a+c) (b+d) i z :=by unfold price; rw [zpow_add₀ (epsilon_pos q i).ne',zpow_add₀ (day_pos z).ne']; ring
-- monotone conversion
lemma here_road (hr:R≥0)(i:ℕ)(z:Cover)(hz:street z≤gate q R i): ε i*day z ≤1+R:= by
   have hp : ε i≤1:= by unfold epsilon; exact inv_le_one_of_one_le₀ (Interval.cane q i)
   have hw:= (gate_mem _ hr z).mp hz; unfold day;rw [mul_add,mul_one]; linarith
lemma price_rise (hr:R≥0)(ha:c≤a)(hb:a-b≥c-d) (i:ℕ)(z:Cover)(hz:street z≤gate q R i) : price q a b i z ≤ (1+R)^(a-c) * price q c d i z := by
   have H : day z^(b-d) ≤ day z^(a-c):= zpow_le_zpow_right₀ (day_me z) (by omega)
   have hpos:= price_pos q c d i z
   have hx : price q a b i z=price q (a-c) (b-d) i z * price q c d i z:= by rw [decomp, sub_add_cancel,sub_add_cancel]
   rw [hx]; refine mul_le_mul_of_nonneg_right ?_ hpos.le; unfold price
   apply le_trans (mul_le_mul_of_nonneg_left H (zpow_pos (epsilon_pos q i) _|>.le)); rw [← mul_zpow]; exact zpow_le_zpow_left₀ (by omega) (mul_nonneg (epsilon_pos q i|>.le) (day_pos z|>.le)) (here_road hr i z hz) -- name
variable {f g:Mist V}
namespace Visa
lemma zero : Visa q R a b (0:Mist V):=by refine ⟨⟨0,le_rfl,by simp⟩,?_⟩; intro x hx hr z hz; simp only [Pi.zero_apply,smul_zero]; exact Released.zero
lemma add (h:Visa q R a b f)(hp:Visa q R a b g): Visa q R a b (f+g):= by
   obtain ⟨C,hc,he⟩:= h.who; obtain ⟨D,hd,hg⟩:= hp.who; refine ⟨⟨C+D,add_nonneg hc hd,?_⟩,fun x hx hr z hz=> ?_⟩
   · filter_upwards [he,hg] with i hi ht z hz; rw [add_mul]; exact (norm_add_le ..).trans (add_le_add (hi z hz) (ht z hz))
   simp only [Pi.add_apply,smul_add]; exact (h.whereL x hx hr z hz).add (hp.whereL x hx hr z hz)
lemma smult (a':ℝ)(h:Visa q R a b f):Visa q R a b (a' • f):= by
   obtain ⟨C,hc,he⟩:= h.who; refine ⟨⟨‖a'‖*C,by positivity,?_⟩,fun x hx hr z hz=>?_⟩
   · filter_upwards [he] with i hi z hz; rw [Pi.smul_apply,Pi.smul_apply,norm_smul,mul_assoc];gcongr; exact hi z hz
   simp_rw [Pi.smul_apply,smul_comm (_^_) a']; exact (h.whereL x hx hr z hz).smul (a:=fun _:ℕ=> a') ⟨a',tendsto_const_nhds⟩
lemma neg (h:Visa q R a b f):Visa q R a b (-f):= by simpa only [neg_one_smul ℝ] using Visa.smult (-1:ℝ) h
lemma sub (h:Visa q R a b f)(hp:Visa q R a b g):Visa q R a b (f-g):= by rw [sub_eq_add_neg]; exact h.add hp.neg
lemma counts {I:Type*}(w:Finset I){u:I→Mist V}(h:∀ i∈w,Visa q R a b (u i)) : Visa q R a b (∑ i∈w,u i):= by
   induction w using Finset.induction_on with
   | empty=> rw [Finset.sum_empty]; exact zero
   | insert i w hi ih=> rw [Finset.sum_insert hi]; exact (h i (by simp)).add (ih (fun j hj=> h j (by simp [hj])))
lemma station (L:ℝ)(h:Visa q R a b f)(hx:L≤R):Visa q L a b f:= by
   obtain ⟨c,hc,he⟩:= h.who; refine ⟨⟨c,hc,?_⟩,fun x he h z hz=> ?_⟩; filter_upwards [he] with i hi z hz; exact hi z (hz.trans (Nat.floor_le_floor (mul_le_mul_of_nonneg_left hx (amp_pos .. |>.le)))) -- proof station h shadow
   exact (show Visa q R a b f from by assumption).whereL x he (le_trans h hx) z hz
include hq in
lemma stretch (h:Visa q R a b f)(hr:R≥0)(ha:c≤a)(hb:c-d≤a-b): Visa q R c d f:= by
   obtain ⟨C,hc,he⟩:=h.who; refine ⟨⟨C*(1+R)^(a-c),by positivity,?_⟩,fun x hx hp z hz=>?_⟩
   · filter_upwards [he] with i hi z hz; refine le_trans (hi z hz) ?_; rw [mul_assoc]; gcongr; exact price_rise hr ha hb i z hz
   have he := h.whereL x hx hp z hz; let t:= (d-c-(b-a)); have ht:t≥0:= by omega
   have hw: Released (fun i=> ε i ^ t):= by simp_rw [show ∀ i:ℕ, ε i ^ t= ε i ^ t.toNat from fun i=> by nth_rw 1 [show t= (t.toNat:ℤ) from by omega]; rw [zpow_natCast]]; exact ⟨(0:ℝ)^t.toNat,(paths hq).cutoff.pow _⟩ -- zpow coe needed
   simp_rw [show d-c=t+(b-a) from by unfold t; omega,zpow_add₀ (epsilon_pos q _).ne',mul_smul]; exact he.smul hw
end Visa
end YM.PositionX.Haze
