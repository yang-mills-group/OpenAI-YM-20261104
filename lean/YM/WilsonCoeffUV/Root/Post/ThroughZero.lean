import YM.WilsonCoeffUV.Root.Post.Armature
/-! # All partial entry costs *independent* of unknown source norm at absolute rank. Necessary in graph shear proof. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.WilsonCoeffUV.Cosmos
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Bulb
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {n c:Side}{U V E:Type*}{r h D l i j e k a m:ℕ} {G:Gauge}{F:Labels.Frame G h}{s t t' A X B C δ:ℝ}{I:Bulb G}

lemma wist (F:Frame G h)(p:lowerGrade i j e k)(v:Alma F)(D): Bank.Slate (Tern G e k D) (Scorn G e k D) (fun I x=> echoS F (fanfare I.path x.P.P h x.Y i j) v) (fun I x=>echoS F (fanfare I.path x.P.Q h x.Z i j) v):=by
    obtain ⟨d,H⟩:= Fabric.higher (G:=G) p h D; refine ⟨d,fun I=>?_⟩; obtain ⟨B,hb,q⟩:= H I; obtain ⟨C,hC,p⟩:= paid_echo F _ I.positive j D
    refine ⟨C*B,by positivity,fun x=>?_⟩; rw [mul_assoc]; have hp:= q x; refine ⟨p _ _ _ hp.wax,p _ _ _ hp.wane,?_⟩; rw [← echo_minus F v hp.wax hp.wane I.positive I.positive]; exact (p _ _ _ hp.toll).trans_eq (by ring)
lemma BankSlate_add {J:Type*}{U:J→Type*}{x y:(j:J)→U j→ℝ}{P Q M K:(j:J)→U j→ℝ}(p:Bank.Slate x y P Q)(q:Bank.Slate x y M K)(h:∀ j,Brite (x j) (y j)): Bank.Slate x y (P+M) (Q+K):=by
    obtain ⟨d,H⟩:= p; obtain ⟨n,T⟩:= q; refine ⟨d+n,fun j=>?_⟩; obtain ⟨A,a,u⟩:= H j; obtain ⟨C,c,v⟩:= T j
    exact ⟨A+C,by positivity,fun i=> ((u i).add (v i)).lift (roof_pair _ _ _ ((h j).large i) a c _ _) ((h j).dist i)⟩
lemma BankSlate_sum {J:Type*}{V:J→ Type*}{x y:(j:J)→V j→ℝ}(h:∀ j,Brite (x j) (y j))(S:Finset U){P Q: U→(j:J)→V j→ℝ}(he:∀ i∈S,Bank.Slate x y (P i) (Q i)): Bank.Slate x y (fun j v=> ∑ i∈S,P i j v) (fun j v=> ∑ i∈S,Q i j v):=by
    classical
    induction S using Finset.induction_on with
    | empty=> simp only [Finset.sum_empty]; exact Bank.Slate.one h
    | @insert i S p ih=> simp_rw [Finset.sum_insert p]; exact BankSlate_add (he i (Finset.mem_insert_self ..)) (ih fun i hi=> he i (Finset.mem_insert_of_mem hi)) h

def ptax (F:Frame G h)(Y:Single G D)(i:ℕ)(v:Alma F):= ∑ r∈Finset.range (valence F v), if valence F v≤ i+r then echoS F (Y (i+r-valence F v) r) v else 0
lemma coin_purse (F:Frame G h)(p:i≤ e)(k D:ℕ)(v:Alma F): Bank.Slate (Tern G e k D) (Scorn G e k D) (fun I x=> ptax F (fanfare I.path x.P.P h x.Y) i v) (fun I x=> ptax F (fanfare I.path x.P.Q h x.Z) i v):=by
    unfold ptax; refine BankSlate_sum (matur e k D) _ ?_; intro r hr; by_cases H: valence F v ≤ i+r
    · simp only [if_pos H]; exact wist F (show lowerGrade (i+r-valence F v) r e k from Or.inl (by have hh:= Finset.mem_range.mp hr; omega)) v D
    simp only [if_neg H]; exact Bank.Slate.one (P:=fun _=>0) (matur e k D)
-- if upperGrade T. note explicit properties.
lemma gust (F:Frame G h)(v:Alma F)(p:lowerGrade i (valence F v) e k)(D): Bank.Slate (Tern G e k D) (Scorn G e k D) (fun I x=> glean F (fanfare I.path x.P.P h x.Y) i v) (fun I x=> glean F (fanfare I.path x.P.Q h x.Z) i v):=by
    have hp:i≤ e:=by unfold lowerGrade at p; omega
    simp_rw [tail_glint]; exact BankSlate_add (coin_purse F hp k D v) (wist F p v D) (matur e k D)
-- ⇒ uniform
abbrev Funds (F:Frame G h)(e:ℕ):= Fin (e+1)×Alma F
def priorF (F:Frame G h)(e r:ℕ): Finset (Funds F e) := by
  classical
  exact Finset.univ.filter (fun i=> lowerGrade i.1.val (valence F i.2) e r)
lemma prior_iff (F:Frame G h)(i:Funds F e): i∈ priorF F e r↔lowerGrade i.1.val (valence F i.2) e r:=by classical simp [priorF]
private lemma uniformJ {U:Type*}{J:U→Type*}{E:Type*}(x y:(u:U)→J u→ℝ)(F T:E→ (u:U)→J u→ℝ)(S:Finset E)(hx:∀ i∈ S,Bank.Slate x y (F i) (T i))(hp:∀ i,Brite (x i) (y i)): ∃ d:ℕ,∀ j,∃ C:ℝ,0≤ C∧∀ v,∀ i∈S,twain (C*x j v^d) (y j v) (F i j v) (T i j v):= by
    classical
    induction S using Finset.induction_on with
    | empty=> exact ⟨0,fun j=>⟨0,le_rfl,by simp⟩⟩
    | @insert i S h ih=>
      obtain ⟨d,H⟩:= hx i (Finset.mem_insert_self ..); obtain ⟨k,T⟩:= ih (fun i hi=>hx i (Finset.mem_insert_of_mem hi)); refine ⟨d+k,fun j=>?_⟩; obtain ⟨a,p,q⟩:= H j; obtain ⟨b,g,t⟩:=T j; refine ⟨a+b,by positivity,fun v u hu=>?_⟩
      have hh:= (hp j).large v; have hv:= (hp j).dist v; have hz:0≤x j v:= zero_le_one.trans hh
      rcases Finset.mem_insert.mp hu with h'|h'; subst u; exact (q v).lift (mul_le_mul (le_add_of_nonneg_right g) (pow_le_pow_right₀ hh (by omega)) (by positivity) (by positivity)) hv
      exact (t v _ h').lift (mul_le_mul (le_add_of_nonneg_left p) (pow_le_pow_right₀ hh (by omega)) (by positivity) (by positivity)) hv
lemma prior_tap (F:Frame G h)(e r D:ℕ): ∃ d:ℕ,∀ I:Bulb G,∃ C:ℝ,0≤ C ∧∀ W:Tand I e r D,∀ v:Alma F,∀ i:ℕ,lowerGrade i (valence F v) e r → twain (C*W.x^d) W.σ (glean F (fanfare I.path W.P.P h W.Y) i v) (glean F (fanfare I.path W.P.Q h W.Z) i v):=by
    obtain ⟨d,H⟩:= uniformJ (Tern G e r D) (Scorn G e r D) (fun (i:Funds F e) j v=>glean F (fanfare j.path v.P.P h v.Y) i.1.val i.2) (fun i j v=>glean F (fanfare j.path v.P.Q h v.Z) i.1.val i.2) (priorF F e r) (fun i hi=>gust F i.2 ((prior_iff F i).mp hi) D) (matur e r D)
    refine ⟨d,fun I=>?_⟩; obtain ⟨C,h,t⟩:= H I; refine ⟨C,h,fun W v i p=>?_⟩; let k:Funds F e:= (⟨i,by unfold lowerGrade at p; omega⟩,v); exact t W k ((prior_iff ..).mpr p)

structure EntryΔ (W:Tand I e r D)(F:Labels.Frame G h)(A C:ℝ) (d:ℕ): Prop where
    pos : 0 ≤C
    pose j i : (j<e∨j=e∧r≤valence F i) → ‖glean F (fanfare I.path W.P.P h W.Y) j i‖≤ C*W.x^d
    vale j i : (j<e∨j=e∧r≤valence F i) → ‖glean F (fanfare I.path W.P.Q h W.Z) j i‖≤ C*W.x^d
    toll j i : (j<e∨j=e∧r≤valence F i) → ‖glean F (fanfare I.path W.P.P h W.Y) j i-glean F (fanfare I.path W.P.Q h W.Z) j i‖≤ C*W.x^d*(1+A)*W.σ
lemma summarize (F:Labels.Frame G h)(r e D:ℕ)(d:ℕ): ∃ n:ℕ,∀ (I:Bulb G)(S:ℝ),0≤ S→∃ C:ℝ,0≤ C∧∀ (W:Tand I e r D)(A B V:ℝ), 0≤ A → Wager W F A B V S d → EntryΔ W F A C n:=by
    obtain ⟨c,H⟩:=prior_tap F e r D
    obtain ⟨k,g⟩:= uniformJ (Tern G e r D) (Scorn G e r D) (fun (v:Alma F) I x=> ptax F (fanfare I.path x.P.P h x.Y) e v) (fun v I x=>ptax F (fanfare I.path x.P.Q h x.Z) e v) Finset.univ (fun i _=> coin_purse F (le_refl e) r D i) (matur e r D)
    refine ⟨(k+d)+c,fun I S p=>?_⟩; obtain ⟨A,hA,t⟩:= H I; obtain ⟨B,b,q⟩:= g I
    let C:=B+S+A; have hc:0≤C:=by unfold C; positivity
    refine ⟨C,hc,fun W D T V hx W'=>?_⟩
    have hv:= W.P.rich; have hh:=W.P.θ; let x:=W.x; change 1≤x at hv
    let Z:=C*W.x^((k+d)+c); let θ:=W.σ; let P:= glean F (fanfare I.path W.P.P h W.Y); let Q:=glean F (fanfare I.path W.P.Q h W.Z); have hu :0≤Z:=by unfold Z; change 0≤ C*x^_; positivity
    have ht : Z≤ Z*(1+D):=le_mul_of_one_le_right hu (by linarith)
    have he j (i:Alma F)(v:j<e∨ j=e∧r≤valence F i): ‖P j i‖≤Z∧‖Q j i‖≤Z∧ ‖P j i-Q j i‖≤ Z*(1+D)*θ:=by
       by_cases hg:lowerGrade j (valence F i) e r
       · have hw : twain Z θ (P j i) (Q j i):= (t W i j hg).lift (mul_le_mul (show A≤C from le_add_of_nonneg_left (add_nonneg b p)) (pow_le_pow_right₀ hv (by omega)) (pow_nonneg (zero_le_one.trans hv) _) hc) hh
         exact ⟨hw.main,hw.side,hw.gap.trans (mul_le_mul_of_nonneg_right ht hh)⟩
       unfold lowerGrade at hg; have ha: j=e:=by omega
       have hb: valence F i=r:=by omega
       subst j
       have hq:= q W i (Finset.mem_univ i); let X:=1+D; have hX:0≤X:=by unfold X; linarith
       have hc : B*x^k+S*x^d≤ Z := (roof_pair _ _ _ hv b p k d).trans (mul_le_mul (le_add_of_nonneg_right hA) (pow_le_pow_right₀ hv (by omega)) (by positivity) hc)
       unfold P Q; simp_rw [tail_glint];
       let Y:= fanfare I.path W.P.P h W.Y; let F':=fanfare I.path W.P.Q h W.Z
       change ‖ptax F Y e i+echoS F (Y e (valence F i)) i‖≤ _ ∧‖ptax F F' e i+echoS F (F' e (valence F i)) i‖≤ _∧‖ptax F Y e i+echoS F (Y e (valence F i)) i-(ptax F F' e i+echoS F (F' e (valence F i)) i)‖≤ _
       rw [hb]; refine ⟨(norm_add_le ..).trans ((add_le_add hq.main (W'.fare i hb)).trans hc),(norm_add_le ..).trans ((add_le_add hq.side (W'.care i hb)).trans hc),?_⟩
       rw [add_sub_add_comm]; have hA : B*x^k ≤ B*x^k*(1+D):=le_mul_of_one_le_right (by positivity) (by linarith)
       apply (norm_add_le ..).trans ((add_le_add (hq.gap.trans (mul_le_mul_of_nonneg_right hA hh)) (W'.owe i hb).gap).trans ?_); change B*x^k*X*θ+S*x^d*X*θ≤ Z*X*θ; rw [←add_mul,←add_mul]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc hX) hh
    exact ⟨hc,fun j i v=>(he _ _ v).1,fun j i v=>(he _ _ v).2.1,fun j i v=>(he _ _ v).2.2⟩
end YM.WilsonCoeffUV.Cosmos
