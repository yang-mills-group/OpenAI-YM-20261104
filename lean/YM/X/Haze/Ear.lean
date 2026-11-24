import YM.X.Haze.Pin
/-!
Use Hazy bank for terminal earnings at a stencil radius. Away can lift affordability std. Include Tender shell & log vanish.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Haze
open Lattice Wilson Next.Rank CellsInt Beamer Interval PertExtension LatticePT Normal Filter Set Function Metric MeasureTheory Asymptotics
open Reed Stems Fielding Print Braid
open scoped Topology ContDiff BigOperators Classical ENNReal
variable {q : ℕ+} (hq:1<q.val) {k m:ℕ} {R:ℝ}
local notation "Fℕ"=>(atTop:Filter ℕ)
local notation "ε"=>epsilon q
variable {V:Type*}[NormedAddCommGroup V][NormedSpace ℝ V]{f:Mist V} {a b:ℤ}
-- off can use any physical floor. get regular monomials
lemma annular {r:ℝ}(hp:r>0)(h:Visa q R a b f)(hx:∀ᶠ i in Fℕ, ∀ z, street z ≤ gate q r i → f i z=0)(ha:a<1): Visa q R 1 (b-a+1) f:= by
   let w:= b-a+1; obtain ⟨C,hc,hi⟩:= h.who; refine ⟨⟨C/r^(1-a),by positivity,?_⟩,fun x hx hr z hz=>?_⟩
   · filter_upwards [hi,hx] with i hi hh z hz; specialize hi z hz; by_cases hu:street z≤gate q r i; · rw [hh z hu,norm_zero]; exact mul_nonneg (by positivity) (price_pos q 1 w i z|>.le)
     rw [gate_mem _ hp.le] at hu; have hw : r ≤ ε i * day z:= (not_le.mp hu|>.le).trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) (epsilon_pos q i|>.le)); apply le_trans hi; rw [div_mul_eq_mul_div,mul_div_assoc]; gcongr <;> try exact Nat.zero_le _
     refine (le_div_iff₀ (zpow_pos hp _)).mpr ((mul_le_mul_of_nonneg_left (zpow_le_zpow_left₀ (by omega: (1:ℤ)-a≥0) hp.le hw) (price_pos ..|>.le)).trans ?_)
     rw [mul_zpow]; change price q a b i z*price q (1-a) (1-a) i z≤_; rw [decomp,show a+(1-a)=1 by ring, show b+(1-a)=b-a+1 by ring]
   rw [show b-a+1-1=b-a by ring];exact h.whereL x hx hr z hz

-- sums helpers for χ where dynamic supports
variable [CompleteSpace V]
def influx (p:ℕ→Lane)(f:Mist V):=fun i=>beadR (p i) (f i)
def relabel (p:ℕ→Lane) : Mist ℝ:=fun i z=>p i z
lemma star_smul (w:ℕ→Lane)(h: Starboard q R (relabel w)) : Starboard q R (fun i z=> w i z • f i z):= by
   apply h.mono; intro i hi z hz; exact hi z (fun h=> hz (show w i z • f i z=0 from by rw [show w i z=0 from h,zero_smul]))
lemma posed (w:ℕ→Lane): ∀ i:ℕ, Frugal (fun z=>relabel w i z • f i z) (w i).support:= by
   intro i z hz; rw [Finset.mem_coe,Finsupp.mem_support_iff]; exact fun h=> hz (show w i z • f i z=0 from by rw [h,zero_smul])
include hq
variable (x: Floor R)
lemma mask_won (h:Visa q R a b f)(ha:1≤a)(hb:4≤a-b): Released (influx (Floor.maskL q x) f):= by
   have ht:= Visa.stretch (d:=(-3)) hq h x.positive.le ha (by omega)
   exact dom_release hq x.positive.le (Visa.scales (Floor.mask_visa hq x R x.positive.le) ht) (Eventually.of_forall (posed (Floor.maskL q x))) (star_smul _ (x.onboard hq)) -- zero_add subtype?
lemma mask_special (h:Visa q R a b f)(ha:1≤a)(hb:4<a-b): Tendsto (influx (Floor.maskL q x) f) atTop (𝓝 0):= by
   let w:=Floor.maskL q x; let y(i:ℕ)(z:Cover): V:= w i z • f i z; have he: Visa q R a b y:= by let Hx:= Visa.scales (Floor.mask_visa hq x R x.positive.le) h; simpa using Hx
   have hs:= star_smul (f:=f) w (x.onboard hq); let θ:E4→V:=0; suffices hθ: ∀ x':E4,x'≠0→Tendsto (fun i=> (ε i ^(-4:ℤ)) • mosaic (ε i) (y i) x') Fℕ (𝓝 (0:V)) by
      convert! dom_budget (g:=θ) x.positive.le (Visa.stretch (d:=(-3)) hq he x.positive.le ha hb.le) (Eventually.of_forall (posed w)) hs hθ using 1; simp [θ]
   intro p hp; let z(i:ℕ):=index (ε i) p
   rcases le_or_gt ‖p‖ R with hR|hR
   · obtain ⟨r,hr⟩:= he.whereL p hp hR z (entrant hq p); let K:= -4-(b-a); have hk:0<K:=by omega
     change Tendsto (fun i=>(ε i ^ (-4:ℤ)) • y i (z i)) Fℕ (𝓝 0); simp_rw [show (-4:ℤ)= K+(b-a) by unfold K; ring,zpow_add₀ (epsilon_pos q _).ne',mul_smul]; have ht : Tendsto (fun i=>ε i ^ K) Fℕ (𝓝 0) := by
          simp_rw [show ∀ i:ℕ, ε i^K=ε i^K.toNat from fun i=> by nth_rw 1 [show K=(K.toNat:ℤ) by omega]; rw [zpow_natCast]]; simpa only [zero_pow (show K.toNat≠0 by omega)] using! (paths hq).cutoff.pow K.toNat
     simpa using ht.smul hr
   refine tendsto_const_nhds.congr' ?_; filter_upwards [(entrant hq p).norm.eventually (lt_mem_nhds hR),hs] with i hi hh; unfold mosaic; change 0=(ε i)^(-4:ℤ) • y i (z i); rw [show y i (z i)=0 from not_not.mp (fun h=> not_le_of_gt hi (gate_range R x.positive.le _ (hh _ h))),smul_zero]
lemma shell_release (i:Axis)(h: Visa q R a b f)(hb:3≤a-b) : Released (influx (fun k=> changed (Floor.maskL q x k) i) f):= by
   let w(k:ℕ):= changed (Floor.maskL q x k) i; let y(k:ℕ)(z:Cover):= w k z • f k z; have hx:Visa q R (1+a) b y:= by simpa only [zero_add] using (Floor.changed_visa hq x i).scales h
   have hp: Visa q R 1 (-3) y:= by
      rcases le_or_gt 0 a with ha|ha
      · exact Visa.stretch hq hx x.positive.le (by omega) (by omega)
      refine Visa.stretch hq (annular (r:=x.s.rIn/2) (by have := x.s.rIn_pos; positivity) hx ?_ (by omega)) x.positive.le (by rfl) (by omega); apply (x.changed_out hq i).mono; intro k hk z hz; unfold y w; rw [hk _ hz,zero_smul]
   exact dom_release hq x.positive.le hp (Eventually.of_forall (posed w)) (star_smul _ (x.changed_ship hq i))
end YM.PositionX.Haze
