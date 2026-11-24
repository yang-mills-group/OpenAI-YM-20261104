import YM.WilsonCoeffUV.Product.Report.Charges
/-!
# Admit windows/profiles - Motif
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Soil
open Gauge Power PathCost Precision Embroider Fountain Cosmos Shard Realm
open PowerSeries
open scoped Topology BigOperators
variable {n c:Side}{U V α β:Type*}{r h D j e i l k:ℕ}{A B C s:ℝ}{G:Gauge}
open Embroider
open scoped ContDiff
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos PathCost PowerSeries
open scoped Matrix.Norms.Frobenius
variable {b b' u m M N a:ℕ}{H:Hol G} {δ Z y:ℝ} {E W V':Credit}{R:Realm G (e+1) E}
variable (Q:Fin (a+1)→ SealR G)
abbrev Herit:= (i:Fin (a+1))→ (Q i).Rider
abbrev Wilt:= (i:Fin (a+1))→ Rarity (Q i).D
def Motif (S:Schedule)(y:ℕ→ℝ)(m i:ℕ)(z:ℝ):ℝ:= z + Compar S y m i
lemma compar_tier (_H:R.anchor ≤ m)(t:m≤ i): R.y m≤ Compar R.draws.S R.y m i:= by unfold Compar; linarith only [scales R.draws.S t,show (0:ℝ)≤ (i-m:ℕ) by positivity]
lemma compar_age (S:Schedule)(y:ℕ→ℝ)(m:ℕ): Monotone (Compar S y m):=fun _ _ h=> add_le_add (add_le_add_right (sub_le_sub_right (scales S h) _) _) (by exact_mod_cast Nat.sub_le_sub_right h m)
-- receipt per package. product outfits not uniform rank allocation abroad
structure Bough (Q:Fin (a+1)→ SealR G) (F:Wilt Q)(y Z:ℝ) (p:Fin (a+1)→ℝ): Prop where
    pos:1≤ Z
    lanes i:Amplitude (F i) (p i)
    rents i : (F i).radius ≤ Z
    room : |y| ≤ Z
    seats i j:i≠j → ClearDay (F i) (F j) Z⁻¹
structure Sitting (P:Fin (a+1)→ SealR G)(G':Fin (a+1)→ℝ) (e:ℕ)(δ:ℝ)(X Y:Herit P) :Prop where
    stock i: 0≤ G' i
    track i:Terms e (P i) (G' i) δ (X i) (Y i)
variable {Q}
lemma Sitting.gainP {p:Fin (a+1)→ℝ}{X Y:Herit Q}{x:ℝ}(h:Sitting Q p e δ X Y)(v:δ≤x): Sitting Q p e x X Y:=⟨h.stock,fun i j k b=>(h.track i j k b).wide v⟩

variable (Q)
def arouse (A:Levels G)(Ñ:ChartRatio G)(F: Wilt Q)(X:Herit Q)(m i N:ℕ)(y:ℝ): Fin (a+1) →Era G Lounge:= fun j=> (Q j).spins A Ñ (F j) m i N y (X j)
def crestValue (V: Type*) [NormedRing V][NormedAlgebra ℝ V](B:Fin (a+1)→ Era G V):= MassP G V a B
abbrev asp (i:Fin (a+1)):= (Q i).h
abbrev capP:=∑ i,asp Q i
abbrev HearthC (A:Levels G)(Ñ:ChartRatio G)(F: Wilt Q)(X:Herit Q)(m i N:ℕ)(y:ℝ): Era G Lounge:= MassP G Lounge a (arouse Q A Ñ F X m i N y)
abbrev awaken (A:Levels G)(Ñ:ChartRatio G)(F:Wilt Q)(X:Herit Q)(m i N:ℕ)(y:ℝ)(o:CellR): Fin (a+1)→ Era G ℝ:= fun j=> locale o (arouse Q A Ñ F X m i N y j)
abbrev Ashore (A:Levels G)(Ñ:ChartRatio G)(F:Wilt Q)(X:Herit Q)(m i N:ℕ)(y:ℝ)(o:CellR):Era G ℝ:= MassP G ℝ a (awaken Q A Ñ F X m i N y o)
lemma ash_spans (A:Levels G)(Ñ:ChartRatio G)(F:Wilt Q)(X:Herit Q)(m i N:ℕ)(y:ℝ)(o:CellR): Ashore Q A Ñ F X m i N y o=locale o (HearthC Q A Ñ F X m i N y):=(PortalHome ..).symm
variable {Q}
abbrev HorizonP (H:Hol G)(R:Realm G (e+1) E)(W V:Credit)(Q: Fin (a+1)→SealR G):= ∀ i,Nonempty (PassportC H R (Q i) W V)
lemma Hearth_enter (P:HorizonP H R W V' Q)(F:Wilt Q)(X:Herit Q)(t:R.anchor≤ i)(q:i≤N): Auth (capP Q) (HearthC Q R.draws R.paid F X m i N y):= PortalLong a _ (asp Q) fun j=> (P j).elim fun h=>passportHead h (F j) _ y t q
lemma ash_head (P:HorizonP H R W V' Q)(F:Wilt Q)(X:Herit Q)(t:R.anchor ≤ i)(q:i≤ N)(o:CellR): Auth (capP Q) (Ashore Q R.draws R.paid F X m i N y o):=by rw [ash_spans]; exact locale_val _ (Hearth_enter P _ _ t q) o
lemma blaze_step (P:HorizonP H R W V' Q)(F:Wilt Q)(X:Herit Q) (t:R.anchor≤m)(p:m≤ i)(q:i<N) (o:CellR) :
    let Ψ k:= awaken Q R.draws R.paid F X m k N y o; (fun j=> verseI R.draws R.paid i N (asp Q j) (Ψ (i+1) j))= Ψ i:=funext fun j=> (P j).elim fun h=>passportCarry h (F j) _ o t p q
-- rekindle local first joins
abbrev Ash (A: Levels G)(Ñ:ChartRatio G)(F:Wilt Q)(X:Herit Q)(m i N:ℕ)(y:ℝ)(o:CellR):Era G ℝ:= DeltaGap A Ñ i N (awaken Q A Ñ F X m (i+1) N y o) (asp Q)
lemma ash_tide (P:HorizonP H R W V' Q)(F:Wilt Q)(X:Herit Q) (t:R.anchor≤m)(p:m≤ i)(q:i<N) (o:CellR):
    let A k:= Ashore Q R.draws R.paid F X m k N y o; Ash R.draws R.paid F X m i N y o= verseI R.draws R.paid i N (capP Q) (A (i+1))- A i:=by
    intro A
    unfold Ash DeltaGap startK; rw [blaze_step P F X t p q];
-- costs helpers. Δ old & price event counts
lemma moth (S:Finset (Fin (a+1)))(C: Fin (a+1)→ Credit) : ∃ W:Credit,∀ i ∈S,∀ z,1≤ z → (C i).buy z≤ W.buy z:=by
   apply uniformPays (P:=fun i W=>∀ z,1≤z→ (C i).buy z ≤ Credit.buy W z) S (fun i _=>⟨C i,fun _ _=>le_rfl⟩)
   exact fun _ _ _ _ p t x y=> (t x y).trans (p x y)
-- bare common independent price all at one scale (not association-sum powers)
lemma costs_join (C x:ℝ) (D: Fin (a+1)→ ℝ)(h:Fin (a+1)→ℕ):
    (∏ i,C*(x^(h i))⁻¹ * D i) = C^(a+1)*(x^(∑ i,h i))⁻¹ * (∏ i,D i):=by rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Finset.prod_inv_distrib,Finset.prod_pow_eq_pow_sum]
lemma regionPay (H:Hol G)(Q:Fin (a+1)→ SealR G)(E W V:Credit)(e u:ℕ): ∃ C:Credit,∀ (R:Realm G (e+1) E), HorizonP H R W V Q →∀ m i b N M (F:Wilt Q) (X Y: Herit Q)(A B: Fin (a+1)→ℝ)(Z y δ)(o:CellR), R.anchor≤ m → m≤ i → i≤ b → b ≤ N→ b≤ M → Compar R.draws.S R.y m i ≤ Z → Bough Q F y Z B → R.tempC i b≤ δ→ Sitting Q A e δ X Y →
   let π:= paceT R.draws.S m i; let V':ℝ:= (π^(capP Q))⁻¹ * ∏ i,(B i*A i); Fringed (capP Q) e u π (C.buy Z*V') δ (Ashore Q R.draws R.paid F X m i N y o) (Ashore Q R.draws R.paid F Y m i M y o):=by
   obtain ⟨W',hW⟩:= moth Finset.univ (fun (i:Fin (a+1))=>hardCash e u E W V H (Q i)); let c:= (coinMat (capP Q) e)^a; let C:= (pur c).prodC (W'.powC (a+1))
   refine ⟨C,fun R h m i b N M F X Y A B Z y δ o v t p q f ht H' hv hy=>?_⟩; intro π V'; let L:=W'.buy Z; let T j:= L*(π^((Q j).h))⁻¹*(B j*A j); have hx:0<π:=pace_pos ..
   have hT : ∀ j,Fringed (asp Q j) e u π (T j) δ (awaken Q R.draws R.paid F X m i N y o j) (awaken Q R.draws R.paid F Y m i M y o j):=by
      intro j; obtain ⟨P⟩:=h j; apply ((capLife P v t p q f ht (hy.stock j) hv (X j) (Y j) (hy.track j) (F j) (H'.rents j) u o H'.room (H'.lanes j)).1).pay; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hW j (Finset.mem_univ _) _ H'.pos) (inv_nonneg.mpr (by positivity))) (mul_nonneg (H'.lanes j).1 (hy.stock j))
   apply (valueP a _ _ (asp Q) T (le_refl (capP Q)) hT hx.le).pay; unfold C; rw [Credit.products,Credit.power,loadRep,show (∏ i,T i)= _ from costs_join L π (fun i=> B i*A i) (asp Q)]
   let f:ℝ:= W'.buy Z ^ (a+1); have hf:0≤ f:=pow_nonneg (zero_le_one.trans (W'.purchase H'.pos)) _; have hV:0≤ V':= mul_nonneg (by positivity) (Finset.prod_nonneg fun i _=> mul_nonneg (H'.lanes i).1 (hy.stock i))
   change c*(f*(π^capP Q)⁻¹*(∏ i,B i*A i)) ≤ _; rw [mul_assoc f,←mul_assoc]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (pure_goal ..) hf) hV
end YM.WilsonCoeffUV.Mer
