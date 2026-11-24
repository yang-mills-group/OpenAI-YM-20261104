import YM.WilsonCoeffUV.Stable.Calendar
/-! # Stable letter demand propagation. Explicit fuel on arbitrary normalized input;
receipts auxiliary Bends on every Mark. -/
set_option autoImplicit false
set_option maxHeartbeats 410000
noncomputable section
namespace YM.WilsonCoeffUV.Shard
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {n:Side}{r h D l j i e k a m b u N M c:ℕ} {G:Gauge}{F:Labels.Frame G h}{s A C t B x δ:ℝ}

-- descending n≥m. c=input birth (fine top, translated start). starts locally
-- totalize beyond c with input. R formal Σ[Y]. Color stiffness.
noncomputable def breaths (A:Levels G)(Ñ:ChartRatio G)(T:SectionData F)(p:h<D)(N k c m:ℕ)(P:TowerS G D): TowerS G D:= if H:m<c then Sink A Ñ T p N m k (breaths A Ñ T p N k c (m+1) P) else P
termination_by c-m
lemma breath_step (A:Levels G)(Ñ:ChartRatio G)(T:SectionData F)(p:h<D)(P:TowerS G D) (v:m<c): breaths A Ñ T p N k c m P=Sink A Ñ T p N m k (breaths A Ñ T p N k c (m+1) P):= by rw [breaths,dif_pos v]
lemma breath_top (A:Levels G)(Ñ:ChartRatio G)(T:SectionData F)(p:h<D)(P:TowerS G D):breaths A Ñ T p N k m m P=P:=by rw [breaths,dif_neg (lt_irrefl m)]
variable {H:Hol G}{T:SectionData F}{p:h<D} {v:Rails h k u e}{E W K V V':Credit} {Y X Z:TowerS G D}
lemma nursing (t:Torch H T p v E W K)(h0:t.L.V.anchor≤m)(p':m≤c)(hp:c≤N)(P:On k Y)(q:opal F Y=0): let X:=breaths t.L.V.draws t.L.V.paid T p N k c m Y; On k X∧opal F X=0:=by
    induction p' using Nat.decreasingInduction with
    | self=> rw [breath_top]; exact ⟨P,q⟩
    | of_succ i he ih=> obtain ⟨x,-⟩:=ih (by omega); rw [breath_step _ _ T p _ he]; apply Sink_for _ _ _ _ (production t.L (he.le.trans hp) h0).1 v.hk (he.trans_le hp) t.L.V.hG t.L.V.green x

def Granite (F:Frame G h)(k u e:ℕ)(A:ℝ)(X:TowerS G D): Prop:= On k X ∧ opal F X=0 ∧ 0≤ A ∧ ∀ i r,i≤e→Fruit 0 1 u (X.2 i r) A

def OrePeak (H:Hol G)(T:SectionData F)(p:h<D)(v:Rails h k u e)(E W K B:Credit)(i r:ℕ): Prop:=∀ a:Torch H T p v E W K,∀ m c N,a.L.V.anchor≤m → m≤c → c≤N→∀ P:TowerS G D,∀ A,Granite F k u e A P → let L:= a.L.V; Fruit 0 1 u ((breaths L.draws L.paid T p N k c m P).2 i r) (L.cash B m*L.tempC m c*A)
lemma OrePeak.more {d:ℕ}(X:OrePeak H T p v E W K V i d) (h:∀ y:ℝ,1≤y→ V.buy y ≤ V'.buy y): OrePeak H T p v E W K V' i d:= by
   intro a m c N h' t x P A q L'; exact (X a m c N h' t x P A q).more (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (h _ (a.L.V.depth _ h')) (trail_pos ..).le) q.2.2.1)

lemma overOre(h': k+i<r) : OrePeak H T p v E W K V i r:=by
   intro a m c N z y w P A q' L; have hy:=L.depth m z
   rw [solo_shape (nursing a z y w q'.1 q'.2.1).1 i r h']; exact Fruit.zero.more (mul_nonneg (mul_nonneg (zero_le_one.trans (V.purchase hy)) (trail_pos ..).le) q'.2.2.1)
namespace Ore
-- step convolution arithmetic
lemma purchase_border (C:Credit)(R:Realm G e E)(p:R.anchor≤m){A:ℝ}(q:0≤A): A≤(Credit.tower C Credit.liftA (R.y m))*R.tempC m m*A:=by
   rw [tempC,trail_end,mul_one]; exact le_mul_of_one_le_left q ((C.purchase (R.depth _ p)).trans (Credit.raised C _ _ Credit.lift_good (R.depth _ p)))
lemma aging (T:Credit) (R:Realm G e E) (p:R.anchor≤m)(u:ℕ)(A:ℝ)(hA:0≤A): let d:= arc R.draws.S m
    Real.exp (-d/2)*(T.tower Credit.liftA (R.y (m+1))*R.tempC (m+1) u*A)+R.cash T m*R.tempC m u*A ≤ T.tower Credit.liftA (R.y m) * R.tempC m u*A:=by
    intro d; let C:= R.tempC m u; let P:= R.tempC (m+1) u; let B:= T.tower Credit.liftA (R.y (m+1)); let Z:=Real.exp (-d/4)
    have he:C=Z*P:=one_leg ..; have hf: Real.exp (-d/2)=Z*Z:=by unfold Z; rw [← Real.exp_add]; congr 1; ring
    change Real.exp _*(B*P*A)+R.cash T m*C*A≤ _
    rw [hf, show Z*Z*(B*P*A)= (Z*B)*C*A from by rw [he]; ring,←add_mul,←add_mul]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (Credit.step_cap T (R.depth m p) (R.depth (m+1) (by omega)) (R.age _ _ p m.le_succ) (arch_pos ..)) (trail_pos ..).le) hA
def jumped (E V:Credit):= (Realm.jump E V).prodC E
lemma lift_money (R:Realm G e E)(h:R.anchor≤m)(V:Credit)(q): R.cash V (m+1)*R.tempC (m+1) q≤R.cash (jumped E V) m*R.tempC m q := by
    apply (mul_le_mul (R.shift_z V h) (R.missed h) (trail_pos ..).le (zero_le_one.trans (Credit.purchase _ (R.depth _ h)))).trans; exact le_of_eq (by unfold jumped cash; rw [Credit.products]; ring)
end Ore
open Ore
lemma portico (p': i≤ e) (h': r≤k+i)(hv:∀ i' j,lowerGrade i' j i r→OrePeak H T p v E W K V i' j): ∃ C:Credit, OrePeak H T p v E W K C i r:=by
   have ht:r≤ k+e:=by omega
   let B:= rocket H T p v i r ht E W K; let V':= jumped E V; let C:= B.prodC V'
   refine ⟨C.behind,?_⟩; intro a m c N x y w P A q L; let R:= a.L.V; have hx:= R.depth m x; let F' m:=breaths R.draws R.paid T p N k c m P
   have hA:= q.2.2.1
   suffices hh : ∀ i'≤c, R.anchor ≤ i' → Fruit 0 1 u ((F' i').2 i r) (C.tower Credit.liftA (R.y i')*R.tempC i' c*A) by exact (hh m y x).more (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (Credit.donation C _ _ _ hx) (trail_pos ..).le) hA)
   intro m hm; induction hm using Nat.decreasingInduction with
   | self=> intro he; unfold F'; rw [breath_top]; exact (q.2.2.2 i r p').more (purchase_border C R he hA)
   | of_succ m g ih=>
      intro h
      let X:=F' (m+1); let t:=R.tempC m c
      have hh:R.anchor≤ m+1:=by omega
      have H := ih hh; have hy: ∀ i' j,lowerGrade i' j i r → Fruit 0 1 u (X.2 i' j) (R.cash V' m * t * A):= fun i j v=> (hv i j v a (m+1) c N hh g w P A q).more (mul_le_mul_of_nonneg_right (lift_money R h V c) hA)
      have ht':0≤t:= (trail_pos ..).le; obtain ⟨s,hX⟩:= nursing a hh g w q.1 q.2.1
      rw [show F' m=Sink R.draws R.paid T p N m k X from breath_step _ _ T p P g]; apply (boat a h (g.trans_le w) p' ht X s hX _ _ H (mul_nonneg (mul_nonneg (zero_le_one.trans (V'.purchase (R.depth _ h))) ht') hA) hy).more
      exact le_trans (le_of_eq (show _ + _= Real.exp (-arc R.draws.S m/2)*(C.tower Credit.liftA (R.y (m+1))* R.tempC (m+1) c*A)+R.cash C m*R.tempC m c*A from congr_arg (fun y=> Real.exp (-arc R.draws.S m/2)*(C.tower Credit.liftA (R.y (m+1))*R.tempC (m+1) c*A)+y) (show R.cash B m*(R.cash V' m*t*A)=R.cash C m*t*A by unfold C cash; rw [Credit.products]; ring))) (aging C R h c A hA)
-- recursive order helper for all finite tall sectors; no infinite user reader assumption
lemma seasonsPaid (P: ℕ→ℕ→Credit→Prop)(k e:ℕ) (h:∀ i≤e,∀ r,∀ W, (∀ i' j,lowerGrade i' j i r→ P i' j W) → ∃ V,P i r V)
   (x:∀ i r, k+i < r →∀ V,P i r V) (v:∀ i r A B, (∀ y:ℝ,1≤y → A.buy y ≤ B.buy y) → P i r A→P i r B): ∃ X:Credit,∀ i≤e,∀ j,P i j X:=by
   suffices H:∀ n≤ e+1,∃ X: Credit,∀ i j,i<n→P i j X from (by obtain ⟨X,t⟩:=H _ le_rfl; exact ⟨X,fun i h r=>t _ _ (by omega)⟩)
   intro n hv; induction n with
   | zero=> exact ⟨Credit.unit,by omega⟩
   | succ i ih=>
      obtain ⟨C,H⟩:= ih (by omega)
      have hh : ∀ r ≤ k+i+1,∃ V:Credit,(∀ r',r≤r'→ P i r' V) ∧ (∀ y:ℝ,1≤ y→ C.buy y≤ V.buy y):=by
          intro r ht
          induction ht using Nat.decreasingInduction with
          | self=> exact ⟨C,fun _ q=> x _ _ (by omega) _,fun _ _=> le_rfl⟩
          | of_succ r he ih=>
             obtain ⟨V,f,g⟩:= ih; obtain ⟨S,u⟩:= h i (by omega) r V (fun a b g'=>by rcases g' with p|⟨p,z⟩; exact v a b C V g (H _ _ p); subst a; exact f b z)
             refine ⟨V.plus S,fun k e=>?_ ,fun y w=>(g _ w).trans (Credit.thickens _ w)⟩; by_cases j:r=k; · subst r; exact v _ _ _ _ (fun _ w=> Credit.thickened _ w) u
             exact v _ _ _ _ (fun _ w=>Credit.thickens _ w) (f k (by omega))
      obtain ⟨V,t,w⟩:=hh 0 (by omega); refine ⟨V,fun j r v'=>?_⟩; by_cases e:j=i; subst j; exact t r (by omega); exact v j r C V w (H _ _ (by omega))
lemma bloom_all (H:Hol G)(T:SectionData F)(p:h<D)(v:Rails h k u e)(E W K:Credit): ∃ X:Credit,∀ i≤e,∀ j, OrePeak H T p v E W K X i j:=by
    refine seasonsPaid (fun i j V=>OrePeak H T p v E W K V i j) k e ?_ (fun i j v _=>overOre v) (fun i j A B t p=> p.more t)
    intro i hv r V hf; by_cases h:r≤k+i
    · exact portico hv h hf
    exact ⟨V,overOre (by omega)⟩
end YM.WilsonCoeffUV.Shard
