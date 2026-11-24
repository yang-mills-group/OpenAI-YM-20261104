import YM.WilsonCoeffUV.Marked.Bounds.Bracket
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.WilsonCoeffUV.Wheel.Mark
open Function PowerSeries Blue Mer Lattice RG Embroider Embroider.Canvas Soil Bank Laurent Cosmos Filter Gauge Power Matrix Precision Wilson Tree Exterior AnalyticNext.QuarticMatch.Sheets Bloch FreeResolvent Work.F08 Metric Shard Realm PathCost
open scoped Topology BigOperators
variable {c f:Side}{ι α U β V t:Type}{J K I S T:Finset ι}{p:ι→U}{d:Bank.Distance U}{D k:ι→ℕ}{i j i' j' a e r h N n m l:ℕ}{G:Gauge}{σ τ u A B C:ℝ}
variable {w s:Gear G→ℝ}[DecidableEq ι]

def elixir (I:Gear G):= (I.s+I.σ)/2
lemma pureEl (I:Gear G): I.σ<elixir I:=by unfold elixir; linarith [I.holds]
lemma highEl (I:Gear G): elixir I<I.s:=by unfold elixir; linarith [I.holds]

abbrev scald {I:Gear G}(t:ZL D S e I)(J:Finset ι)(l):= Blue.mix t.L.P.moving (fun i=> sluice (finalZ (t.quietT J) l i))
lemma scalePay {D k:ι→ℕ}(i r:ℕ)(h:i≤ e)(u:J⊆ S): ∃ d:ℕ,∀ I:Gear G, ∃ C:ℝ,0≤C∧∀ t:ZL D S e I,Wig Bank.terrain t.places (elixir I) (C*t.L.x^d*t.β^J.card) J (scald t J (mass k J) i r):=by
    let F (I:Gear G)(t:ZL D S e I)(j):= (t.L.P.moving^j*(t.L.P.moving⁻¹)^r)
    let eV (I:Gear G)(t:ZL D S e I) j:= finalZ (t.quietT J) (mass k J) j r; let X (I:Gear G)(t:ZL D S e I) (j:ℕ) := coeff (i-j) (F I t j) • eV I t j
    have hi j (x:j≤ i): QuestB elixir (fun I (t:ZL D S e I)=>X I t j) J:=by
        have hv : QuestB elixir (fun (I:Gear G) (t:ZL D S e I)=> eV I t j) J:=by simp_rw [eV,finalZ,Finset.sum_apply]; apply QuestB.sum; intro a _; exact choirZ D G S a j e r (x.trans h) u elixir highEl (fun I=> (I.price.trans (pureEl I)).le)
        obtain ⟨c,P⟩:=hv; obtain ⟨d,H⟩:=titles (G:=G) (e:=e+1) (i:=i-j) (by omega) 0 j r; refine ⟨d+c,fun I=>?_⟩; obtain ⟨A,hA,P⟩:=P I; obtain ⟨B,hB,V⟩:=H I; refine ⟨B*A,by positivity,fun t=>?_⟩
        let a := coeff (i-j) (F I t j); have hh:= zero_le_one.trans t.L.rich; apply ((P t).μ a).more; have hf:‖a‖≤ B*t.L.x^d:=(V t.L).main; apply (mul_le_mul_of_nonneg_right hf (P t).1).trans_eq; rw [pow_add]; ring
    let Z (I:Gear G)(t:ZL D S e I):= ∑ j∈ Finset.range (i+1),X I t j
    obtain ⟨d,H⟩:= QuestB.sum (w:=elixir) (J:=J) (P:=X) (K:=Finset.range (i+1)) (fun i p=> hi i (by have he:= Finset.mem_range.mp p; omega))
    refine ⟨d,fun I=>?_⟩; obtain ⟨A,hA,H⟩:= H I; refine ⟨A,hA,fun t=>?_⟩; have hp:= H t; refine ⟨hp.1,fun x=>?_⟩; have he:= hp.2 (pierR ∘ x); simpa only [scald,X,F,eV,Blue.mix, Finset.sum_apply,Pi.smul_apply] using! he

lemma common_scale (G:Gauge)(D k:ι→ℕ)(e:ℕ) [Fintype ι]: ∃ d:ℕ,∀ I:Gear G,∃ C:ℝ,0≤C∧∀ (S J :Finset ι)(_h:J⊆S) i r,i≤e → r≤ mass k J+i →∀ t:ZL D S e I,Wig Bank.terrain t.places (elixir I) (C*t.L.x^d*t.β^J.card) J (scald t J (mass k J) i r):=by
    let a:= {s:(Finset ι)× (Finset ι)|s.2⊆s.1}
    let V:= mass k (Finset.univ) + e
    let U: Type:= {x:↑a × Fin (e+1) × Fin (V+1)// x.2.2.val ≤ mass k x.1.val.2 + x.2.1.val}
    classical
    let L := mass k
    let _ : Fintype a:= Fintype.ofFinite a; let _ : Fintype U:= Fintype.ofFinite U
    choose d ht using fun i:U=>scalePay (G:=G) (D:=D) (k:=k) (i:=i.val.2.1.val) (r:=i.val.2.2.val) (Nat.le_of_lt_succ i.val.2.1.isLt) (J:=i.val.1.val.2) (S:=i.val.1.val.1) i.val.1.property
    let z:=∑ i,d i; refine ⟨z,fun I=>?_⟩; choose f hf x using fun i=>ht i I; let C:=∑ i,f i; refine ⟨C,Finset.sum_nonneg fun i _=>hf i,fun S J v i r h p t=>?_ ⟩
    have hk:mass k J≤ L Finset.univ:=by unfold L; rw [stairK k (Finset.subset_univ J)]; exact Nat.le_add_right ..
    let e':U := ⟨(⟨(S,J),v⟩, ⟨i,by omega⟩, ⟨r,by unfold L at hk; unfold V; omega⟩),p⟩; have he:=t.L.rich
    exact (x e' t).more (mul_le_mul_of_nonneg_right (mul_le_mul (Finset.single_le_sum (fun i _=> hf i) (Finset.mem_univ e')) (pow_le_pow_right₀ he (Finset.single_le_sum (fun _ _=> Nat.zero_le _) (Finset.mem_univ e'))) (pow_nonneg (zero_le_one.trans he) _) (Finset.sum_nonneg fun i _=>hf i)) (pow_nonneg t.ht _))
section
variable [Fintype ι]
abbrev muralExp (G:Gauge)(D k:ι→ℕ)(e):=(common_scale G D k e).choose
abbrev shrinePost (G:Gauge)(D k:ι→ℕ)(e)(I):= ((common_scale G D k e).choose_spec I).choose

variable {C W:Credit}
structure Cloze (D k:ι→ℕ)(R:Realm G (e+1) W)(C:Credit):Prop where
   carpet (m:ℕ) (h:R.anchor≤m): shrinePost G D k e (R.mint m h).gear ≤ R.cash C m
   heat (m:ℕ) (h:R.anchor≤m): (elixir (R.mint m h).gear-(R.mint m h).σ)⁻¹≤ R.cash C m
variable {R:Realm G (e+1) W}
def safeB (p:ι→Cover)(B:family G D)(S:Finset ι)(e:ℕ)(σ A:ℝ): Prop:=∀ J⊆ S,∀ i≤e,∀ r,Wig Bank.terrain p σ (A^J.card) J ((B J).2 i r)
abbrev vigor (G:Gauge)(D k:ι→ℕ)(e:ℕ)(C E:Credit):= C.prodC ((costXV G e E).powC (muralExp G D k e))
lemma waltz (R:Realm G (e+1) W)(p:Cloze D k R C)(Q:family G D)(t:Eu k Q)(u:Q ∅=0)(m N)(x:R.anchor≤m)(g:m<N)(v:ι→Cover)(z:ι→Site (ll R.draws m).L)(b: safeB (fun i=> (ll R.draws m).L.val • v i + lift (z i)) Q S e (R.mint (m+1) (by omega)).σ A)(q:J⊆ S)(a:0≤ A)(f:i≤e): Wig Bank.terrain v (elixir (R.mint m x).gear) (R.cash (vigor G D k e C W) m*A^J.card) J ((logO R.draws R.paid m N Q k J).2 i r):=by
   let I:=(R.mint m x).gear; let X:Rally (e+1) 0 I:= ReelTime R (le_refl e) x g (le_refl N) (le_refl N); let d:=muralExp G D k e; let U:=R.cash (vigor G D k e C W) m
   have he:A≥0:=a; have ht:=X.rich; have hv:0≤U:=zero_le_one.trans (Credit.purchase _ (R.depth _ x)); let L:= logO R.draws R.paid m N Q k
   let Y:ZL D S e I:=⟨X,Q,v,z,A,a,u,fun s h i hi l=> (b s h i hi l).shave (R.crossing m x)⟩
   by_cases w:r≤mass k J+i
   · rw [onSide R.draws R.paid m N Q k u t R.hG R.green g]
     change Wig _ _ _ _ _ (scald Y J (mass k J) i r)
     refine (((common_scale G D k e).choose_spec I).choose_spec.2 S J q i r f w Y).more (mul_le_mul_of_nonneg_right ?_ (pow_nonneg a _)); unfold vigor cash; rw [Credit.products,Credit.power]; exact mul_le_mul_of_nonneg_right (p.carpet m x) (pow_nonneg (zero_le_one.trans Y.L.rich) d)
   have hp:L J=(L J):=rfl; rw [(step_L R.draws R.paid m N Q k g R.hG R.green t J).coverN i r (by omega)]; exact Wig.zero.more (mul_nonneg hv (pow_nonneg he _))
theorem one_shore (p:Cloze D k R C)(Q:family G D)(t:Eu k Q)(u:Q ∅=0)(m N)(x:R.anchor≤m)(g:m<N)(v:ι→Cover)(z:ι→Site (ll R.draws m).L)(b: safeB (fun i=> (ll R.draws m).L.val • v i + lift (z i)) Q S e (R.mint (m+1) (by omega)).σ A)(a:0≤ A) :
    safeB v (logO R.draws R.paid m N Q k) S e (elixir (R.mint m x).gear) (R.cash (vigor G D k e C W) m*A):=by
    let U:= R.cash (vigor G D k e C W) m; have hU:1 ≤ U:=Credit.purchase _ (R.depth _ x); intro J h i f r
    by_cases g':J=∅; · subst J; rw [logHush]; change Wig _ _ _ _ _ 0; simp only [Finset.card_empty,pow_zero]; exact Wig.zero.more zero_le_one
    apply (waltz R p Q t u m N x g v z b h a f).more; rw [mul_pow]; apply mul_le_mul_of_nonneg_right _ (pow_nonneg a _); change U≤U^J.card; exact le_trans (by rw [pow_one] : U≤ U^1) (pow_le_pow_right₀ hU (Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr g')))
end
end YM.WilsonCoeffUV.Wheel.Mark
