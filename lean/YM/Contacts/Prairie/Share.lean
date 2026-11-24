import YM.Contacts.Prairie.Point
namespace YM.Contacts.Prairie
open Function Set Finset Filter RG Wilson Lattice Precision Exterior Push.AbsoluteSums Extra.Iteration
open Bloch Milling Milling.Steam Pulse Spine MergeProof Milling.Forge Laurent Stationary Matrix Work.F08
open Milling.Garf Form House PertExtension.Series Tree Larch FreeResolvent PhysicalNext.RankCovariance
open Next.Free Milling.Lumen Barrage.Reserve
open scoped Topology BigOperators Matrix Classical NNReal ContDiff Matrix.Norms.Frobenius
noncomputable section
variable {G: Gauge}
namespace Parcel
open Origin Barrage.Slope Ion Resetter
variable (e:Parcel G) (p q u:Word) (s:Step) (n:Side) {i j:ℕ} {ζ:ℝ≥0}{b:ℝ}
-- arbitrarily long (switched) chains, shared final steps
abbrev Boom:= Finset Step
def OK (S:Boom)(p:Word):Prop:= ∀ t∈p,t∈ S
section
variable {S:Boom}{p w:Word}{s:Step}
lemma OK.nil : OK S []:= by simp [OK]
lemma OK.cons (h:OK S p)(hs:s∈S): OK S (s::p):= fun t h' => (List.mem_cons.mp h').elim (fun he => he.symm ▸ hs) fun he=> h t he
lemma OK.tail (h: OK S (s::p)): OK S p:= fun t he=> h t (List.mem_cons.mpr (.inr he))
lemma OK.head (h:OK S (s::p)): s∈S:= h _ (List.mem_cons_self ..)
lemma OK.append (h:OK S p) (k:OK S w): OK S (p++w):= by intro t ht; rcases List.mem_append.mp ht with hx|hx; apply h _ hx; apply k _ hx
end
def mileage (u:Word):ℝ:= (1/2:ℝ)^u.length
lemma mileage_pos (u):0 < mileage u:= by unfold mileage; positivity
@[simp] lemma mileage_nil : mileage [] =1:= by simp [mileage]
@[simp] lemma mileage_cons : mileage (s::p)=mileage p/2:= by simp [mileage,pow_succ,div_eq_mul_inv]
def enough (z:ℕ)(S:Boom):= ∀ t∈ S,z ≤ t.L.val
variable {S:Boom}{z Z:ℕ}
lemma enough.fall (h:enough Z S)(hz:z≤Z):enough z S:= fun t ht=>hz.trans (h t ht)
abbrev decade := sight e.T e.J
lemma decade_pos : 0<e.decade:= sight_pos _ _
lemma decade_le : 2*e.decade≤e.reach:= NNReal.coe_le_coe.mp (by push_cast; have h : (e.decade:ℝ)*3 ≤ e.reach := (shelf_span ..).1; linarith only [h, NNReal.coe_nonneg e.decade])
def habit:= keconomic (e.column p).metric (e.column q).metric
def grove : ℕ→Side:= fun i=>⟨i+1,by omega⟩
lemma grow_tim : Tendsto (fun i=>(grove i).val) atTop atTop:= tendsto_atTop_mono (f:=id) (fun i=>by change i ≤ i+1; omega) tendsto_id
abbrev priceK := (kin_bill e.T e.J).choose
lemma K_pos : 0≤e.priceK := (kin_bill ..).choose_spec.1
lemma K_funds : (krow (e.column p).metric).strip e.reach e.priceK := (kin_bill e.T e.J).choose_spec.2 _ (e.toll p)
abbrev shop := (Fintype.card (Breed 1 (TypeFace 1)):ℝ)*(e.priceK+e.priceK)
lemma deposits: Rooted (terrain e.decade (TypeFace 1)) (e.habit p q) e.shop:= by
   apply arrive_both (R:=portfolio _ _) (strip_minus (e.K_funds p) (e.K_funds q)) (add_nonneg e.K_pos e.K_pos); exact_mod_cast e.decade_le -- habitu
lemma gift_pos : 0≤e.shop:= (e.deposits [] []).cash
lemma Q_floor : ∃ Z:ℕ,∀ (p q) (s:Step),Z ≤ s.L.val→∀ b,Rooted (terrain e.decade _) (e.habit p q) b→ Rooted (terrain e.decade _) (e.habit (s::p) (s::q)) (b/2):= by
   let v:=e.decade; obtain ⟨u,hu,hu',g,hg,G⟩:= angled (σ:=v) (η:=v) (TypeFace 1) (TypeFace 1) 1 e.decade_pos e.tax_pos.le
   obtain ⟨k,hk⟩:= exists_nat_gt (max ((v:ℝ)/u) (2*g)); refine ⟨k, fun p q s h b he=> ?_⟩; let L:=s.L; let A := TypeFace 1
   have hl : ((v:ℝ)/u) ≤ L.val:= (le_max_left ..).trans (hk.le.trans (Nat.cast_le.mpr h)); have hy : 2*g ≤ L.val := (le_max_right ..).trans (hk.le.trans (Nat.cast_le.mpr h)); have hL:=side_pos L; have hs : (v:ℝ)/L.val≤u:= (div_le_iff₀ hL).2 (by simpa only [mul_comm (L.val:ℝ)] using (div_le_iff₀ (NNReal.coe_pos.mpr hu)).1 hl)
   have hv : (v:ℝ) ≤e.reach:= by have ht:=NNReal.coe_le_coe.mpr e.decade_le; push_cast at ht; change 2*(v:ℝ)≤ _ at ht; linarith only [ht, NNReal.coe_nonneg v]
   let R(p:Word):=e.gas p s; have h' (p:Word)(l:List Axis)(ht:l.length≤3): Row.strip (advanceC L (R p) l) v (e.tax/(L.val:ℝ)^(1+l.length)):= strip_mono (e.rod p s l (ht.trans (by have hh:=e.high; omega))) hv le_rfl
   let T k:= e.traveler s (grove k); let u' := e.tax/(L.val:ℝ)^(1+List.length ([]:List Axis)); have hD:0 ≤ u':= by have hx:=e.tax_pos; unfold u'; positivity
   have hr:= steadfast (F:=(e.column p).metric) (M:=(e.column (s::p)).metric) (G:=(e.column q).metric) (K:=(e.column (s::q)).metric) (R:=R p) (R':=R q) (e.whole _) (e.whole _) (e.whole _) (e.whole _) grow_tim T (fun i => rfl) (fun i P Q hp hq=> by have hh : R p=P:= eq_of_heq hp; have hr:R q=Q:= eq_of_heq hq; rw [← hh,← hr]; exact ⟨(e.awake p s).primary _,(e.awake q s).primary _⟩) (e.symmetry _) (e.symmetry _) (he.weaken (terrain_le hu') le_rfl) hs (h' p [] (by simp)) (h' q [] (by simp)) hD
   let V: Fin 2 → Cross L A A:= ![R p,R q]
   have ht : install ∘ V = ![install (R p),install (R q)]:= funext fun i=> by fin_cases i<;>rfl
   unfold habit; rw [hr,← ht]; refine (G L s.odd hs V (fun i l hl=>?_) _ _ he (both_publish _) (vessel_age (e.whole p) (e.whole q) ((e.floor p 1).starts.trans (e.floor q 1).starts.symm))).weaken (fun _=>le_rfl) ?_
   · fin_cases i; exact h' p l hl; exact h' q l hl
   rw [div_le_iff₀ hL]; have h:= he.cash; nlinarith only [hy,h]
abbrev Quota := e.Q_floor.choose
lemma Q_price (S:Boom)(hS: enough e.Quota S)(he:OK S u) : Rooted (terrain e.decade _) (e.habit (u++p) (u++q)) (e.shop*mileage u):= by induction u with| nil=> rw [mileage_nil,mul_one]; exact e.deposits p q|cons s u ih=>rw [List.cons_append,List.cons_append,mileage_cons,←mul_div_assoc]; exact e.Q_floor.choose_spec _ _ s (hS _ he.head) _ (ih he.tail) -- which mul_div_assoc
lemma Q_strip (S:Boom)(hS: enough e.Quota S)(he:OK S u) : Row.strip (portfolio (e.column (u++p)).metric (e.column (u++q)).metric) e.decade (e.shop*mileage u):= from_both (e.Q_price p q u S hS he)
end Parcel
end
end YM.Contacts.Prairie
