import YM.WilsonCoeffUV.Root.UV.Shear
/-!
# Solving with moving projections. Two-times arithmetic, gained pos through y.
Post bound independent of block length on multiplying unknown. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.WilsonCoeffUV.Cosmos
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Bulb
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {n:Side}{U V E:Type*}{r h D l j e k a N m:ℕ} {G:Gauge}{F:Labels.Frame G h}{s t t' A B C x y δ σ γ H S O v:ℝ}

-- for economy uniform cardinal. choose M dependent only l and h; can inflate l. Includes S for post e,r,d fixed.
def shadesT (F:Frame G h)(l:ℕ):ℝ := (blockS F l).card
lemma shadesT_nn (F:Frame G h)(l:ℕ):0≤shadesT F l:= by unfold shadesT; positivity
-- cPrice=ψ*X^d
lemma paidCP (F:Frame G h)(e k:ℕ)(C x:ℝ): cPrice F k x (C*x^e) = cPrice F k 1 C * x^(e+1):=by simp only [cPrice, pow_add, pow_one, Finset.sum_mul]; refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=> by ring
lemma paidCP_nn (F:Frame G h)(k:ℕ){x y:ℝ}(p:0≤ x)(q:0≤ y):0≤cPrice F k x y:= Finset.sum_nonneg (fun i _=> Finset.sum_nonneg fun i _=>by positivity)

-- rates compressed with all inputs and fine cap x≥1. abs and visit. e=current.
structure Spur (P Q: Thesis F D)(σ:ℝ)(T X:Coil F)(e r l:ℕ)(S δ b b':ℝ):Prop where
    step (i:Alma F):valence F i=l→Twig 0 σ b (impose P T i e r)
    side (i: Alma F):valence F i=l→ Twig 0 σ b (impose Q X i e r)
    gape (i:Alma F):valence F i=l→Twig 0 σ b' (impose P T i e r-impose Q X i e r)
    foil:CostS T X l e r S δ
structure Plinth (P Q: Thesis F D)(σ:ℝ)(e r l:ℕ)(C B:ℝ): Prop where
    pose (i: Alma F) : valence F i=l→ Twig 0 σ C (P i e r)
    vale (i: Alma F) : valence F i=l→ Twig 0 σ C (Q i e r)
    peek (i: Alma F) : valence F i=l→ Twig 0 σ B (P i e r-Q i e r)
lemma rise_graph (F:Frame G h)(e r k l c:ℕ)  (u:r≤l+e){Z:ℝ}(hb:0≤B)(ht:0≤S)(hg:0≤Z):∃ E:ℝ,0≤E∧ ∀ (n:Side)(T X:Coil F)(P Q:Thesis F D){w G π y δ x s:ℝ}, 0≤ w→1≤x→1≤ y→0≤ δ→
    (∀ i,shellK (valence F i) (P i))→(∀ i,shellK (valence F i) (Q i))→
    leaseM n F (lineS T 0) → leaseM n F (lineS X 0) → Rapt F (steed (lineS T 0) n) Z → Rapt F (steed (lineS X 0) n) Z →
    Spur P Q s T X e r l (B*x^k) ((1+w)*δ) (G/(n.val:ℝ)*w+S*x^c) (G/(n.val:ℝ)*π+S*x^c*(1+w)*δ) →
    (∀ i: Alma F,valence F i=l→ Twig 0 s y (Q i e r)) →
    (∀ i: Alma F,∀ j:ℕ,j< e∨ j=e∧ valence F i<l→ Shelf Bank.terrain 0 s x δ (P i j r) (Q i j r)) →
    Plinth P Q s e r l ((shadesT F l*Z*G)/(n.val:ℝ)*w + E*x^(c+(k+1))) ((shadesT F l*Z*G)/(n.val:ℝ)*π + E*x^(c+(k+1))*y*(1+w)*δ):=by
    let β:= shadesT F l; have hβ:0≤β:= shadesT_nn ..; let A:= cPrice F e 1 B; have ha:0≤ A:= paidCP_nn F e zero_le_one hb
    let W:= S+A+β*B; have hw: S+A≤ W:= le_add_of_nonneg_right (mul_nonneg hβ hb); have hp :0≤ W:= (add_nonneg ht ha).trans hw
    refine ⟨β*(Z*W),by positivity,?_⟩
    intro n T X P Q w G' π y δ x s hx hX hy hD hP hQ Tt Xx ht0 hv hz hK h'
    let t:=1+w; let z:=t*δ; have hZ:0≤ t:=by unfold t; positivity
    have hu:δ ≤ z:=le_mul_of_one_le_left hD (by unfold t; linarith)
    have hh:= campPay Tt.1 Xx.1 hz.foil hP hQ (show 0≤x from zero_le_one.trans hX) (by positivity) (show 0≤z from hD.trans hu) (fun i j v=>by
      have he:=h' i j v; exact ⟨he.wax,he.wane,he.toll.cost (mul_le_mul_of_nonneg_left hu (zero_le_one.trans hX))⟩)
    simp_rw [paidCP] at hh
    let f:=c+(k+1); let L:ℝ:= n.val
    have he:S*x^c+A*x^(k+1)≤(S+A)*x^f:= roof_pair _ _ _ hX ht ha c (k+1)
    have hh' : (S+A)*x^f≤ W*x^f:= mul_le_mul_of_nonneg_right hw (by positivity)
    let D':= G'/L*w+W*x^f
    have E0 (i:Alma F)(h:valence F i=l): Twig 0 s D' (troops (lineS T 0) (fun v=>P v e r) l i):=by
       rw [campPost]; exact Cork.cost (Cork.sub (hz.step i h) (hh i h).wax) (by rw [add_assoc]; exact add_le_add_right (he.trans hh') _)
    have E1 (i: Alma F)(h:valence F i=l): Twig 0 s D' (troops (lineS X 0) (fun v=>Q v e r) l i):=by
       rw [campPost]; exact Cork.cost (Cork.sub (hz.side i h) (hh i h).wane) (by rw [add_assoc]; exact add_le_add_right (he.trans hh') _)
    have hY : ∀ i: Alma F,valence F i=l→ Twig 0 s (G'/L*π+W*x^f*y*t*δ) (troops (lineS T 0) ((fun v=>P v e r) - (fun v=> Q v e r)) l i):=by
      intro i p; have he' : troops (lineS T 0) ((fun v=>P v e r) - (fun v=> Q v e r)) l i = (impose P T i e r-impose Q X i e r)-(camps T P l e r i-camps X Q l e r i)-troops (lineS T 0-lineS X 0) (fun v=>Q v e r) l i :=by
         rw [← sector_minus,← sector_diff,campPost Q X,campPost P T]; abel
      rw [he']; refine Cork.cost (Cork.sub (Cork.sub (hz.gape i p) (hh i p).toll) (costScuff hz.foil u _ hK i p)) ?_
      change G'/L*π+S*x^c*t*δ+A*x^(k+1)*z+β*(B*x^k*z*y) ≤ G'/L*π+ _
      calc _ = G'/L*π+ ((S*x^c+A*x^(k+1))+β*B*x^k*y)*z:=by unfold z; ring
           _ ≤ G'/L*π+ ((S+A)*x^f*y+β*B*x^f*y)*z:= by apply add_le_add_right; refine mul_le_mul_of_nonneg_right (add_le_add ?_ ?_) (hD.trans hu); exact he.trans (le_mul_of_one_le_right (by positivity) hy); exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hX (by unfold f; omega)) (by positivity)) (zero_le_one.trans hy)
           _ = G'/L*π+ _:= by unfold W z; ring
    refine ⟨fun i p=>?_,fun i p=>?_,fun i p=>?_⟩
    · apply Cork.cost (troopsStow _ E0 Tt ht0 i p); change β*(Z*D') ≤_; unfold D'; apply le_of_eq; ring
    · apply Cork.cost (troopsStow _ E1 Xx hv i p); change β*(Z*D') ≤_; unfold D'; apply le_of_eq; ring
    apply Cork.cost (troopsStow _ hY Tt ht0 i p); change β*(Z*_) ≤_; apply le_of_eq; ring
end YM.WilsonCoeffUV.Cosmos
