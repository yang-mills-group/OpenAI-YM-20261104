import YM.WilsonCoeffUV.Stable.ExactTally
/-!
# Terminal comparison roots admissions & exact cumulative.
-/
set_option autoImplicit false
set_option maxHeartbeats 510000
noncomputable section
namespace YM.WilsonCoeffUV.Shard
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {n:Side}{r h D l j i e k a m b u N M c:ℕ} {G:Gauge}{F:Labels.Frame G h}{s A C t B x δ:ℝ}{H: Hol G}{T:SectionData F}{p:h<D}{v: Rails h k u e}{E W K U':Credit} {R S: TowerS G D}

-- expand in m-first succession. old target requests canonical vs unwrapped only local at epoch - preserve ratio charges to threshold separately at assembly.
section
variable (L:CutsP H T p v E W K U')
namespace CutsP
abbrev springP (i:ℕ):= queries L.ax L.tx T p L.N k L.ceilC L.m i L.pt
abbrev springQ (i:ℕ):= queries L.ax L.tx T p L.M k L.ceilC L.m i L.pt'
abbrev tileP:= tallyV L.ax L.tx T p L.N k L.ceilC L.m L.pt
abbrev tileQ:= tallyV L.ax L.tx T p L.M k L.ceilC L.m L.pt'
lemma onward (he:i≤L.i): On k (L.springP i):=by
    let ht:= L.chest.I; exact burdenOn (m:=L.m) L.L L.ha (Nat.add_le_add_left he _) (L.hc.trans L.hn) ht.ex.1 ht.ex.2.1
lemma carve1 : L.springP L.i=L.pt-Shrine L.Ntop L.tileP:= release L.L.L _ rfl
lemma carve2 (w:i<L.i): Spout L.ax L.tx L.N (L.m+i) h k (L.springP (i+1))= L.springP i:= tired L.L L.ha (Nat.add_le_add_left w _) (L.hc.trans L.hn) L.chest.I.X L.chest.I.ex.1 L.chest.I.ex.2.1
omit L in
lemma stature (H:Hol G)(T:SectionData F)(p:h<D)(v:Rails h k u e)(E W K U':Credit): ∃ V:Credit,∀ L:CutsP H T p v E W K U',∀ i≤e,∀ j,twain (V.buy L.Age*L.fuel) L.δm (coeff i (L.tileP j)) (coeff i (L.tileQ j)):=by
    obtain ⟨A,h⟩:=bootPaid H T p v E W K U'
    let V:=coinQ F v.sup D; let X:= (PriceSale (H:=H) (T:=T) (v:=v) (p:=p) (E:=E) (W:=W) (K:=K) (U':=U')).choose
    refine ⟨(pur V).plus (A.prodC X),fun L i u j=>?_⟩; let Y:=L.chest; have hp:= h Y L.i (show _ from le_refl L.ceilC) _ u j
    let A':=L.Age; let B:=L.fuel; have ha : 1≤ A':= L.windowC.warm
    have hx:(L.vesselsC.tempC (L.m+L.i) L.ceilC)=1:= trail_end ..; have he: L.ceilC-L.m=L.i:=by unfold ceilC; omega
    have hp': A.buy Y.quest.Age*Y.I.R.tempC (Y.I.m+L.i) Y.I.c*Y.I.wealth≤ (A.prodC X).buy A'*B:=by
        change _*L.vesselsC.tempC (L.m+L.i) L.ceilC*(X.buy A'*B)≤ _; rw [hx,mul_one,Credit.products, mul_assoc]; exact mul_le_mul_of_nonneg_right (A.elder Y.quest.I.warm L.cupped) L.org
    unfold tileP tileQ tallyV; simp only [Pi.add_apply,map_add]; rw [he]; apply ((L.price0 j u).add hp).lift _ (trail_pos ..).le
    refine (add_le_add (mul_le_mul_of_nonneg_right (pure_goal V A') L.hf) hp').trans ?_; rw [← add_mul]; exact mul_le_mul_of_nonneg_right (Credit.fuel _ _ ha) L.hf
omit L in
theorem moisture (H:Hol G)(T:SectionData F)(p:h<D)(v:Rails h k u e)(E W K U':Credit): ∃ V:Credit,∀ L:CutsP H T p v E W K U',∀ j≤e,∀ i≤L.i,∀ r:ℕ, let Z:= L.m+i; YieldP 0 1 u (V.buy L.Age * L.vesselsC.tempC Z L.ceilC * L.fuel) L.δm ((L.springP i).2 j r) ((L.springQ i).2 j r):=by
    obtain ⟨A,h⟩:= burden_credit H T p v E W K U'; let V:= (PriceSale (H:=H) (T:=T) (p:=p) (v:=v) (E:=E) (W:=W) (K:=K) (U':=U')).choose
    refine ⟨A.prodC V,fun L j p i v r=>?_⟩; intro Z; have ht:= h L.chest i j (show _ from Nat.add_le_add_left v L.m) p r
    rw [Chest.rateK] at ht; refine ht.step ?_ (trail_pos ..).le; let T:= L.vesselsC.tempC Z L.ceilC
    rw [Credit.products]; apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (A.elder L.chest.quest.I.warm L.cupped) (trail_pos ..).le) L.org).trans; exact le_of_eq (show _*T*(V.buy L.Age *L.fuel)=_ from by change _*T* _=_*T*_; ring)
end CutsP
end
end YM.WilsonCoeffUV.Shard
