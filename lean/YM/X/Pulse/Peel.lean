import YM.X.Pulse.Riddle
/-!
# reality, Unit and Signed spin of unheated stencil α families. independent of ℒ
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Pulse
open Lattice Wilson Next.Rank Normal MvPolynomial Function Filter Set MeasureTheory Asymptotics Reed Braid
open Clove Crystal Gravity Shelf Haze Ocean Interval Size Fielding Print PertExtension LatticePT Plate
open Stems hiding X
open Crate Crate.Fund Hinge Spindle
open scoped Topology ContDiff BigOperators Classical
variable {q:ℕ+}{n:Side}{k d:ℕ}{R:ℝ}{I V T:Type*}{G:Gauge}
open Pert.Position Maxwell Maxwell.Free Bare Function Pert.RawLabels
variable {F:Labels.Frames G}(S:Bare.Shop F) (w:Floor R)
local notation "E"=> Pert.Position.E F
local notation "A"=> F.level d
local notation "L"=> Labels.Label G d
local notation "E₀"=> epsilon q k
variable (Y:T→ℕ)
open Finset
variable {e:ℝ}(P:Fin k→Word G)
variable {j m:ℕ}(x:Fin m→ Site n)
local notation "Z"=> poly (Jam n G)
variable (s:Signed)(p:Fin m→ Pert.Position.E F d)(e₀:ℝ)
local notation "Px" b=> partM S n e₀ x d b
set_option quotPrecheck false
local notation "R₀"=> (Model F).conj (hierarchy F).spin d
local notation "sρ"=> Pert.Rigid.wear F d
local notation "U₀"=> Module.End ℂ (E d)
variable (r:ℝ)(u:Signed×Bool)(f: Module.End ℂ (Pert.Position.E F d))(p':Pert.Position.E F d)
structure Quoin (f:U₀):Prop where
   mark : f ((Model F).unit d)=0
   pays : ∀ k<d,∀ p∈ lower F k d, f p∈ lower F k d
lemma gain_real (h:Quoin f): Quoin (α_c f):= by
   have hv(k:ℕ)(hk:k<d)(p:E d)(hp:p∈lower F k d) : R₀ p∈ lower F k d:= by rw [up_pre F hk.le] at *; obtain ⟨x,rfl⟩:=hp; exact ⟨_, (up_conj F hk.le ..).symm⟩
   refine ⟨?_,fun k hk p hp=> hv k hk (f _) (h.pays k hk _ (hv k hk p hp))⟩; simp [α_c,h.mark]
lemma into_spin (h:Quoin f): Quoin (α_s s f):= by
    have he(k:ℕ)(t:Signed)(hk:k<d)(p:E d)(hp:p∈ lower F k d): sρ t p∈lower F k d:= by rw [up_pre F hk.le] at *; obtain ⟨v,rfl⟩:=hp; rw [Pert.Rigid.wear_ride,up_signed]; exact ⟨_,rfl⟩
    refine ⟨?_, fun k hk p hp=> he k s⁻¹ hk (f _) (h.pays _ hk _ (he k s hk p hp)) ⟩; unfold α_s; simp [Pert.Rigid.wear,h.mark]
def bravo (u:Signed×Bool)(f:U₀):= (if u.2 then α_c else id) (α_s u.1 f)
lemma cap_real_yes (t:Signed): R₀ (α_s t f (R₀ p'))= bravo (t,true) f p':= rfl
lemma topic (h:Quoin f): Quoin (bravo u f):= by unfold bravo; split; exact gain_real _ (into_spin _ _ h); exact into_spin _ _ h
abbrev sheet:= Signed × Bool
def c :ℂ:= (Fintype.card sheet:ℂ)⁻¹
lemma complement : star c=c:= by unfold c; rw [star_inv₀,star_natCast]
lemma amount_c : (∑ _:sheet,c) =1 := by have hp : 0 < Fintype.card sheet:= Fintype.card_pos; unfold c; rw [Finset.sum_const,nsmul_eq_mul,Finset.card_univ,mul_inv_cancel₀]; exact_mod_cast hp.ne'
def avg (f:U₀):=∑ i:sheet,c • bravo i f
lemma avg_cost (h:Quoin f): Quoin (avg f):= by
    unfold avg; constructor
    · simp_rw [LinearMap.sum_apply, LinearMap.smul_apply,(topic _ _ h).mark,smul_zero,sum_const_zero]
    intro i hi p hp; rw [LinearMap.sum_apply]; exact Submodule.sum_mem _ (fun t _=>Submodule.smul_mem _ _ ((topic t _ h).pays _ hi p hp))
lemma avg_r : R₀ (avg f p')=avg f (R₀ p'):= by
    let t:Equiv.Perm sheet := Equiv.prodCongr (Equiv.refl Signed) (Equiv.boolNot); unfold avg; rw [LinearMap.sum_apply,LinearMap.sum_apply,map_sum,← Equiv.sum_comp t (fun i=> (c • bravo i f) (R₀ p'))]; apply Finset.sum_congr rfl; intro ⟨a,b⟩ _; simp only [bravo,t, Equiv.prodCongr_apply,Equiv.refl_apply,LinearMap.smul_apply,map_smulₛₗ,starRingEnd_apply,complement]; apply congr_arg; cases b; · change R₀ (α_s a f p')=R₀ (α_s a f (R₀ (R₀ p'))); rw [crρ]
    change R₀ (R₀ _)=_; rw [crρ]; rfl
private lemma sρ_comm(t:Signed): sρ s (α_s (t*s) f p')= α_s t f (sρ s p') := by simp_rw [α_s,LinearMap.comp_apply,mul_inv_rev]; rw [sρ_mul,sρ_mul,mul_inv_cancel_left]
lemma avg_s : sρ s (avg f p')=avg f (sρ s p'):= by
    unfold avg; let t:Equiv.Perm sheet:= Equiv.prodCongr (Equiv.mulRight s) (Equiv.refl Bool); conv_lhs=> rw [LinearMap.sum_apply,map_sum,← Equiv.sum_comp t]
    rw [LinearMap.sum_apply]; apply Finset.sum_congr rfl; intro ⟨a,b⟩ _; simp only [LinearMap.smul_apply]; rw [map_smul]; apply congr_arg; cases b; exact sρ_comm ..; change sρ s (R₀ (α_s (a*s) f (R₀ p')))= R₀ (α_s a f (R₀ (sρ s p'))); rw [← sρ_real,sρ_comm,sρ_real]
-- lie restriction
def knit (h:Quoin f)(hr:∀ p:E d, R₀ (f p)=f (R₀ p))(hv:∀s:Signed,∀p:E d,sρ s (f p)= f (sρ s p)) : Buffer F d:= by
   refine ⟨(f.restrictScalars ℝ).toContinuousLinearMap,h.mark,h.pays,hr,?_,map_smul f _⟩
   intro s p; simp_rw [← Pert.Rigid.wear_ride]; exact hv s p
lemma knit_val(h:Quoin f)(hr hv): bufferL F (knit f h hr hv)= f:= LinearMap.ext fun _=>rfl
def node(h:Quoin f): Buffer F d:= knit (avg f) (avg_cost f h) (avg_r f) (fun s=> avg_s s f)
def barter: Buffer F d:= node (away (q:=q) (k:=k) S w d) ⟨stove _ _, fun p hp q hq=> stayed S w q hp hq⟩
variable (hq:1<q.val)(hr:R<r)
lemma node_val (h:Quoin f): bufferL F (node f h)= avg f:= knit_val ..
lemma barter_val : bufferL F (barter (q:=q) (k:=k) S w)= avg (away (q:=q) (k:=k) S w d):= node_val ..
variable {L₀:ℕ→ Module.End ℂ (Pert.Position.E F d)}
lemma tickle(hy:∀p:E d,(fun k=> L₀ k p)∈ Trust q (E d))(i:sheet): -- binder L
    (fun k=>bravo i (L₀ k) p')∈ Trust q (E d):=by
    have he(p:E d):(fun k=>α_s i.1 (L₀ k) p)∈ Trust q (E d):= traverse (hy (sρ i.1 p)) (sρ (i.1)⁻¹)
    cases h:i.2
    · simp [bravo,h]; apply he
    simp [bravo,h]; exact traverseS (he (R₀ p')) R₀
include hq
lemma Barter_charge (p:E d): (fun i=> bufferL F (barter (q:=q) (k:=i) S w) p)∈ Trust q _ := by
    rw [show (fun i=> _) =∑ t:sheet,c • (fun i=> bravo t (away (q:=q) (k:=i) S w d) p) from ?_]; exact Submodule.sum_mem _ fun i _=> Submodule.smul_mem _ _ (tickle p (fun p=>robust S w p hq) i)
    ext1 i; rw [barter_val,avg,LinearMap.sum_apply,Finset.sum_apply]; rfl
include hr
lemma Barter_balance : balance q S r m (fun k=> bufferL F (barter (q:=q) (k:=k) (d:=d) S w)):=by
    simp_rw [barter_val,avg]; refine balance_avg (s':=Finset.univ) (J:=fun t:sheet=>fun i=> bravo t (away (q:=q) (k:=i) S w d))  S ?_ amount_c; intro ⟨s,b⟩ _; have hx:= balance_s (L₀:= fun i=> away (q:=q) (k:=i) S w d) S s (m:=m) (light_res S w hr hq); cases b;exact hx; exact balance_r S hx
end YM.PositionX.Pulse
