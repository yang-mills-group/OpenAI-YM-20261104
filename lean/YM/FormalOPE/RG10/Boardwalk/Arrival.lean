import YM.FormalOPE.RG10.Horizon.Trend
/-!
 # Quantitative orientation and atlas estimates (WALK direction)

Arithmetic interface. For upper bounds on *formal coefficients* at regulators tending to UV
 and stress budgets. Two lengths: Z count ≤ power of Θ-age when using on local/core `Λ`,
 and a decay length (in metric budgets, positive exponent multiplies it; exponential notation).
 Regulator or position procedures here still built separately. Efficient permits polynomial in Z.
 Need Z eventually sub-exponential in decay length for shrink (wider, e.g. including geometry
 clock T in Z for that application, **require this still fits**). Quick: NOT necessarily
 $g^∞-flat$ unless decay length$\gg\Lambda=\log 1/g$ when relevant. Does exponentiate, fixed
 positive exponent. Transform only in SAME age with revealed Z and test context. Don’t spend at
 every time-step in a product of unbounded horizon. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalOPE.RG10.Boardwalk
open Filter Function Finset Real Clearing Ledger Rates
open scoped Topology BigOperators Classical
variable {I : Type*} {l:Filter I}

structure Path (l:Filter I) where
 height : I→ℝ
 meters : I→ℝ
 proceeds : Tendsto meters l atTop
 ample : ∀ᶠ i in l, 1 ≤ height i
 affordable (x:ℝ)(hx:0<x): ∀ᶠ i in l,height i ≤ Ledger.tilt (meters i) (-x)

variable (P:Path l)
-- length power ≈ L1.Count arbitrary number of orientation tests only finite here
abbrev grow (m:ℕ)(i:I) := P.height i ^m
abbrev fade (δ:ℝ)(i:I) := Ledger.tilt (P.meters i) δ
-- one-sided budgets, may use with norms or already nonnegative (negative ok for absorption if needed)
def Crop (x:I→ℝ) := ∃ (M:ℝ)(n:ℕ), 0 ≤ M ∧ ∀ᶠ i in l,x i ≤ M*grow P n i
-- expedite positive exponent; coefficients are independent
-- historical Matron uses ψ, no impact

def Cut (x:I→ℝ) := ∃ (δ M:ℝ),0<δ ∧ 0≤M ∧ ∀ᶠ i in l,x i ≤ M*fade P δ i

local notation "φ" => fade P
local notation "L" => P.meters
local notation "Y" => P.height
variable {α β:ℝ} {n k:ℕ}
lemma budget (h:0<α) : ∀ᶠ i in l, P.height i ^ n ≤ fade P (-α) i := by
 induction n generalizing α with
 | zero => filter_upwards [P.proceeds.eventually (eventually_ge_atTop 0)] with i hi; rw [pow_zero,← no_tilt (s:=L i)]; exact shade (by linarith) hi
 | succ n ih=>
   -- induction has fixed h: generalize α
   have hy:0<α/2:=by linarith
   filter_upwards [ih hy,P.affordable (α/2) hy,P.ample] with i hi ho hm
   rw [pow_succ]; apply (mul_le_mul hi ho (zero_le_one.trans hm) tilt_pos.le).trans
   unfold fade; rw [← tilted]; apply le_of_eq; congr 1; ring

variable {P}
local notation "G" => grow P
namespace Crop
variable {x y z:I→ℝ}
lemma mono (h:Crop P x) (hu:∀ᶠ i in l,y i ≤ x i) : Crop P y:= by obtain ⟨w,n,hw,h⟩:=h; exact ⟨w,n,hw,(h.and hu).mono (fun i hi=> hi.2.trans hi.1)⟩
lemma fixed (v:ℝ) : Crop P (fun _=>v):=⟨|v|,0,abs_nonneg _,Eventually.of_forall fun i=> by rw [grow,pow_zero,mul_one]; exact le_abs_self v⟩
lemma up (n:ℕ): Crop P (grow P n) := ⟨1,n,zero_le_one,Eventually.of_forall (fun _=> (one_mul (G n _)).symm.le)⟩ -- collision
lemma join (hx:Crop P x)(hy:Crop P y): Crop P (fun i=>x i+y i):= by
 obtain ⟨v,n,hv,h⟩:=hx; obtain ⟨w,m,hw,u⟩:=hy; refine ⟨v+w,n+m,add_nonneg hv hw,?_⟩; filter_upwards [h,u,P.ample] with i hi hui hp; rw [add_mul]; apply add_le_add <;> (first | apply hi.trans | apply hui.trans); any_goals apply mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hp _) <;> omega
lemma smul (hx:Crop P x) {r:ℝ}(hr:0≤r): Crop P (fun i=>r*x i):= by
 obtain ⟨v,n,hv,h⟩:=hx; refine ⟨r*v,n,mul_nonneg hr hv,?_⟩; filter_upwards [h] with i hi; rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hi hr
lemma multiply (hx:Crop P x)(hy:Crop P y)(hh:∀ᶠ i in l,0≤x i): Crop P (fun i=> x i*y i):= by
 obtain ⟨v,n,hv,h⟩:=hx; obtain ⟨w,m,hw,u⟩:=hy; refine ⟨v*w,n+m,mul_nonneg hv hw,?_⟩; filter_upwards [h,u,P.ample,hh] with i hi hui hp hh
 calc
   _ ≤ (v* _) * (w* _):= (mul_le_mul_of_nonneg_left hui hh).trans (mul_le_mul_of_nonneg_right hi (mul_nonneg hw (pow_nonneg (zero_le_one.trans hp) _)))
   _ = _:= by unfold Boardwalk.grow; rw [pow_add]; ring
end Crop

namespace Cut
variable {x y:I→ℝ}
lemma nil : Cut P (fun _=>0):= ⟨1,0,zero_lt_one,le_refl _, Eventually.of_forall (by simp)⟩
lemma mono (hx:Cut P x) (hy:∀ᶠ i in l,y i ≤ x i): Cut P y:=by obtain ⟨δ,w,hδ,hw,h⟩:=hx; exact ⟨δ,w,hδ,hw,(h.and hy).mono fun i hi=> hi.2.trans hi.1⟩
lemma join (hx:Cut P x)(hy:Cut P y): Cut P (fun i=>x i+y i):=by
 obtain ⟨δ,v,hδ,hv,h⟩:=hx; obtain ⟨α,w,hα,hw,u⟩:=hy; refine ⟨min δ α,w+v,lt_min hδ hα,add_nonneg hw hv,?_⟩; filter_upwards [h,u,P.proceeds.eventually (eventually_ge_atTop 0)] with i hi hui hp; rw [add_mul,add_comm (w*_)]; exact add_le_add (hi.trans (mul_le_mul_of_nonneg_left (shade (min_le_left ..) hp) hv)) (hui.trans (mul_le_mul_of_nonneg_left (shade (min_le_right ..) hp) hw))
lemma multiply (hx:Cut P x)(hy:Crop P y)(hh:∀ᶠ i in l,0≤ y i) : Cut P (fun i=> x i*y i):= by
 obtain ⟨δ,v,hδ,hv,h⟩:=hx; obtain ⟨w,m,hw,u⟩:=hy; have hy:0<δ/2:=by linarith
 refine ⟨δ/2,v*w,hy,mul_nonneg hv hw,?_⟩; filter_upwards [h,u,budget (n:=m) P hy,hh] with i hi hui hb hh
 calc
   _ ≤ v* fade P δ i * (w * fade P (-(δ/2)) i):= mul_le_mul hi (hui.trans (mul_le_mul_of_nonneg_left hb hw)) hh (mul_nonneg hv tilt_pos.le)
   _ ≤ _ :=by rw [mul_mul_mul_comm v,fade,fade,fade,← tilted, show δ+ -(δ/2)=δ/2 by ring]
lemma smul (hx:Cut P x){r:ℝ}(hr:0 ≤ r): Cut P (fun i=> r*x i):= (hx.multiply (Crop.fixed r) (Eventually.of_forall fun _=>hr)).mono (Eventually.of_forall fun _=> (mul_comm ..).le) -- possible indentation
lemma crop (hx:Cut P x): Crop P x:= by
 obtain ⟨δ,w,hδ,hw,h⟩:=hx; apply (Crop.fixed (P:=P) w).mono; filter_upwards [h,P.proceeds.eventually (eventually_ge_atTop 0)] with i hi hp; apply hi.trans; apply mul_le_of_le_one_right hw ((shade hδ.le hp).trans _); rw [no_tilt]
lemma early {δ:ℝ} (h:0 < δ): Cut P (fade P δ):= ⟨δ,1,h,zero_le_one,Eventually.of_forall (fun _=> (one_mul (_:ℝ)).symm.le)⟩
-- regain unit constant with smaller exponent
lemma earns (hx:Cut P x) : ∃ δ:ℝ, 0 < δ ∧ ∀ᶠ i in l,x i ≤ fade P δ i:= by
 obtain ⟨δ,w,hδ,hw,h⟩:=hx; have ht : ∀ᶠ s:ℝ in atTop, Ledger.legUp s w 0*Ledger.tilt s δ ≤ Ledger.tilt s (δ/2):= Rates.absorbed (p:=0) (M:=w) (by linarith : δ /2 < δ)
 exact ⟨δ/2,by linarith,(h.and (P.proceeds.eventually ht)).mono fun i hi=> hi.1.trans (by simpa [Ledger.legUp] using! hi.2)⟩
lemma arrival (hx:Cut P x) (ht:∀ᶠ i in l,0≤x i): Tendsto x l (𝓝 0):= by obtain ⟨δ,hδ,u⟩:= hx.earns; exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ((Rates.fade_out hδ).comp P.proceeds) ht u
end Cut
end YM.FormalOPE.RG10.Boardwalk
