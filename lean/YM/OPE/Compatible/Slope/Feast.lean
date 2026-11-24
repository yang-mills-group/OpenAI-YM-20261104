import YM.OPE.Compatible.Slope.Wake
/-!
# Volume settlement (extension in inherited wait, sums sym etc). Propagate well including rise after contraction
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Lattice Laurent Filter MeasureTheory RG Finset Next.Free Bloch Precision Planned.PrimaryIntegral295 Planned.PrimaryIntegral295.Carrier
open scoped Topology BigOperators Classical
variable {r k j n d m:ℕ}{x:ℝ}{P:Flight j k}
def banner (P:Flight j k) (a:Fin r→ Axis) (b:Fin r→Axis)(t:ℝ)(v:Bin r→ℝ):Bin r→ℝ:= courier (parcelK (fun _=>linesOf P t) a b 0) v
-- trans costs before-L
def pilgrim (P:Flight j k) (a b: Fin (r+1) → Axis) (t:ℝ) (v:Bin r→ℝ):Bin r→ℝ:= ∑ i : Site P.L, midland (courier (parcelK (fun _=>linesOf P t) a b (fun _=>lift i)) (upland v))
local notation "C" => P.L
lemma lift_charge {L: Side} (p:Site L) : size (lift p)≤ 4*L.val:=by
   have h i: (lift p i).natAbs≤L.val:=by have := lift_centers p i; omega
   unfold size; exact (sum_le_sum fun i _=> h i).trans_eq (by simp [Axis])
lemma stamp_local (hv:0<x)(ht:4≤k)(hp:4≤j)(hr:n≤ j-2) (he:n≤m) (r:ℕ):
    ∃ A:ℝ,0 ≤ A ∧ ∀ (P:Flight j k) a b z (p:Bin r→ℝ), Sack (poise m) p z → purewell p n→ Sack (poise m) (banner P a b x p) (A/(P.L.val:ℝ)^(r+n)*z) := by
    obtain ⟨U,hU,hB⟩:= hornsAt (r:=r) (m:=m) x hv hp ht hr
    let K := (1+(Finset.card (trail (Keys r) n):ℝ)); have hl :0 ≤ K:=by unfold K; positivity
    refine ⟨K*U,by positivity,fun P a b z p h y=>?_⟩
    have hh(k:Fin r): size ((fun _=>0:Fin r→Cover) k) ≤ 4*P.L.val:=by simp [size]
    apply (letter_charge (hB P a b _ hh) he (poise_one m) (div_nonneg hU (by positivity)) P.L.property h (newt y he h)).tips; exact le_of_eq (by unfold K;rw [pow_add]; ring)
lemma stamp_globe (hv:0<x)(ht:4≤k)(hp:4≤j)(hr:n≤ j-2)(he:n ≤ m)(r:ℕ):
    ∃ A:ℝ,0≤A∧ ∀ (P:Flight j k) a b z (p:Bin r→ℝ), Sack (poise m) p z→purewell p n→ Sack (poise m) (pilgrim P a b x p) (A*(P.L.val:ℝ)^4/(P.L.val:ℝ)^(r+1+n)*z):=by
    obtain ⟨U,hU,hB⟩:= hornsAt (r:=r+1) (m:=m) x hv hp ht hr
    let K:ℝ := (1+(Finset.card (trail (Keys (r+1)) n):ℝ)); have hl:0≤K:=by unfold K; positivity
    let R:ℝ:=((r+1:ℕ):ℝ)^m; have hu:0≤R:=by unfold R; positivity
    refine ⟨R*K*U,by positivity,fun P a b z p h y=>?_⟩
    let f(i:Site P.L):= courier (parcelK (fun _=>linesOf P x) a b (fun _=>lift i)) (upland p)
    let L:ℝ:= P.L.val; have hd:= upland_bill h
    have ht (i):Sack (poise m) (f i) (K*U/L^(r+1+n)*z):=by
       apply (letter_charge (hB P a b (fun _=>lift i) (fun _=>lift_charge i)) he (poise_one m) (div_nonneg hU (by positivity)) P.L.property hd (newt (uplight p y he h) he hd)).tips
       apply le_of_eq; rw [pow_add]; unfold K L; ring
    apply (Sack.finGather Finset.univ (fun i : Site P.L=> midland (f i)) _ (fun i _=> midland_bill (ht i)) (fun i=> zero_le_one.trans (poise_one m i))).tips
    apply le_of_eq; rw [sum_const, nsmul_eq_mul,Finset.card_univ,site_card,Nat.cast_pow]; change L^4* (R*_)=_;unfold L; ring
end YM.OPE.Flume
