import YM.WilsonCoeffUV.Root.UV.Legality
/-!
# Spacer of earlier obligations. Triangular gap induction. Not inferred from convergence of cutoff maps. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.WilsonCoeffUV.Cosmos
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Bulb Realm PathCost
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {n:Side}{U V:Type*}{r h D l e j k a c N M m b i:ℕ} {G:Gauge}{F:Labels.Frame G h}{H:Hol G}{s t t' A B C x y δ σ γ S O v:ℝ}

variable {E W U' V':Credit}{T:SectionData F}{p:h<D}
def oldJobs (a b c i l k:ℕ):Prop := a< i ∨ a=i ∧ b<l ∨ a=i∧ b=l∧k<c
lemma before1 (p: lowerGrade a b i k): oldJobs a l b i l k:= by unfold oldJobs; unfold lowerGrade at p; omega
lemma before2 (p:a< i ∨ a=i ∧ b<l): oldJobs a b c i l k:= by unfold oldJobs; omega
section
def Sees (H:Hol G)(T:SectionData F)(p:h<D)(e:ℕ)(E W:Credit) (U:Credit)(i l k:ℕ): Prop:=∀ L:Theatre H T p e E W,∀ m (h:L.V.anchor≤ m),∀ b N M (_:m≤ b)(_:b≤N)(_:b≤M),∀ j: Alma F,valence F j=l → Shelf Bank.terrain 0 (L.angle m h).lamp.exitS (L.V.cash U m) (L.V.tempC m b) ((L.lore N m).2 j i k) ((L.lore M m).2 j i k)
def Hanks (H:Hol G)(T:SectionData F)(p:h<D)(e:ℕ)(E W:Credit) (U:Credit)(i l k:ℕ):Prop:= ∀ L:Theatre H T p e E W,∀ m (h:L.V.anchor≤ m),∀ N (_:m≤ N),∀ j:Alma F,valence F j=l → Twig 0 (L.angle m h).lamp.exitS (L.V.cash U m) ((L.lore N m).2 j i k)
end
lemma Sees.Hanks (P:Sees H T p e E W U' i l k): Hanks H T p e E W U' i l k:= fun L m v N h j q=> (P L m v N N N h le_rfl le_rfl j q).wax
lemma Sees.more (P:Sees H T p e E W U' i l k)(h:∀ y:ℝ,1≤y→ U'.buy y≤V'.buy y): Sees H T p e E W V' i l k:= fun L m u b N M hw hn hm j q=> (P L m u b N M hw hn hm j q).step (h _ (L.V.depth m u)) (trail_pos ..).le
-- all funds c folded root. δ doublingE. coarse too.
def blockAge (G:Gauge)(e:ℕ)(E U:Credit):= ((jump E (full_vacuum G (e+1) E).choose).plus (jump E U)).plus U
lemma buoyant (L:Theatre H T p e E W)(hv:L.V.anchor≤m)(hi:i≤e)(hp:m<b)(hn:b≤N)(hm:b≤M)(H':∀ a l' r,oldJobs a l' r i l k→ Sees H T p e E W U' a l' r):
   let K:=blockAge G e E U'; let x:= L.V.cash K m; let δ:= L.V.cash (doubling E) m*L.V.tempC m b
   let P:= L.lore N (m+1); let Q:= L.lore M (m+1); let I:= L.angle m hv
   (L.V.mint m hv).runs (i+1) 0 δ x N M ∧
   (∀ v: Alma F,valence F v=l→∀ j r,lowerGrade j r i k → Shelf Bank.terrain 0 I.lamp.input x δ (P.2 v j r) (Q.2 v j r)) ∧
   (∀ v: Alma F,∀ j:ℕ,j< i ∨ j=i∧ valence F v< l→ Shelf Bank.terrain 0 I.lamp.exitS x δ ((L.lore N m).2 v j k) ((L.lore M m).2 v j k)):= by
   intro K x δ P Q I
   let B:=(full_vacuum G (e+1) E).choose; let Z:=doubling E; let V:=L.V; let y:=V.y m
   have hy:1≤ y:= V.depth _ hv
   have ht: V.cash ((jump E B).plus (jump E U')) m≤ x:= Credit.thickens U' hy
   have hp': V.cash U' m ≤ x:= Credit.thickened _ hy
   have hu:= elderT (k:=i+1) (j0:=0) V hv hp hn hm (fun i' j z=>(full_vacuum G (e+1) E).choose_spec i' (by unfold lowerGrade at z; omega) j)
   have hz:= V.also_temp (b:=b) hv; have hg: 0≤δ:= (trail_pos ..).le.trans hz
   refine ⟨fun i j h=>(hu i j h).up ((Credit.thickens _ hy).trans ht) hg,fun v h j r z=>?_ ,fun v j q=>?_⟩
   · have hq:= (H' j l r (before1 z) L _ (show L.V.anchor ≤m+1 from by omega) b N M hp hn hm v h).shrink (L.touch m hv)
     exact Shelf.step ⟨hq.wax,hq.wane,hq.toll.cost (mul_le_mul_of_nonneg_left hz (zero_le_one.trans (Credit.purchase U' (L.V.depth _ (by omega)))))⟩ ((V.shift_z U' hv).trans ((Credit.thickened _ hy).trans ht)) hg
   have hq:= H' j (valence F v) k (before2 q) L _ hv b N M hp.le hn hm v rfl
   have hs : V.tempC m b ≤ δ:= le_mul_of_one_le_left (trail_pos ..).le (Z.purchase hy)
   exact Shelf.step ⟨hq.wax,hq.wane,hq.toll.cost (mul_le_mul_of_nonneg_left hs (zero_le_one.trans (U'.purchase hy)))⟩ hp' hg

lemma capState (L:Theatre H T p e E W)(hp:L.V.anchor≤m)(ha:i≤ e)(hb:m≤ N): ∃ A:ℝ,1≤A∧∀ j: Alma F,Twig 0 (L.angle m hp).lamp.exitS A ((L.lore N m).2 j i k):= by
    choose A hA using fun j=>(production L hb hp).2 j i ha k; refine ⟨1+∑ i,A i,le_add_of_nonneg_right (Finset.sum_nonneg fun i _=> (hA i).1),fun j=>Cork.cost (hA j) ((Finset.single_le_sum (fun i _=> (hA i).1) (Finset.mem_univ _)).trans (le_add_of_nonneg_left zero_le_one))⟩
lemma archFoam (L:Theatre H T p e E W)(h0:L.V.anchor≤m)(hv:l≤ h)(he:k≤l+e): skulk H F p l k (L.angle m h0) / (inkPin (L.angle m h0)).patch.L.val≤ Real.exp (-(arc L.V.draws.S m)/2):=by
   have he': (inkPin (L.angle m h0)).patch.L=(L.V.draws.S.block m):=by rw [(L.effort m h0).1]; rfl
   apply le_trans ((L.spend m h0).preS l k hv he); rw [arch,he']
-- abs rec. tower.
lemma Season (hp:i≤ e)(hk:k≤l+i)(ht:l≤h)(hf:∀ a l' r,oldJobs a l' r i l k→ Sees H T p e E W U' a l' r): ∃ V:Credit,Hanks H T p e E W V i l k :=by
    let Z:=blockAge G e E U'; let v:=portC H F p i k l hk; let C:= W.prodC (Z.powC v); let b:= W.plus C
    refine ⟨b.behind,fun L m h0 N g j hg=>?_⟩
    let V:=L.V
    suffices hh : ∀ m≤N,∀ h: L.V.anchor≤m,∀ j: Alma F,valence F j=l →Twig 0 (L.angle m h).lamp.exitS (b.tower Credit.liftA (V.y m)) ((L.lore N m).2 j i k) by exact Cork.cost (hh m g h0 j hg) (Credit.donation b _ Credit.lift_good _ (V.depth _ h0))
    intro n hn
    induction hn using Nat.decreasingInduction with
    | self=>
       intro a j h
       have hy:=V.depth N a; unfold Theatre.lore; rw [Peak_initial]; exact Cork.cost (umbral T p j i k _) (((L.spend N a).wells j i k hp (h.symm ▸ hk)).trans ((Credit.thickens _ hy).trans (Credit.raised b Credit.liftA _ Credit.lift_good hy)))
    | of_succ n he ih=>
       intro a j h
       let K:=L.angle n a; let y:= V.y n; let s:= V.y (n+1); let t:= K.lamp.input
       let d:= arc V.draws.S n
       let A:= b.tower Credit.liftA s; let B:= b.tower Credit.liftA y
       have hy:1≤ y:= V.depth n a; have hv:1≤ s:= L.V.depth (n+1) (by omega)
       have h₁:0≤A:= zero_le_one.trans ((b.purchase hv).trans (Credit.raised b Credit.liftA s Credit.lift_good hv))
       obtain ⟨u,q,w⟩:= buoyant L a hp he (le_refl N) (le_refl N) hf
       let T':= (L.lore N (n+1)).2
       let X:=Z.buy y
       have hb:= Z.purchase hy
       have hh : Plinth T' T' t i k l A 0:=by
          have hz i' (h:valence F i'=l): Twig 0 t A (T' i' i k):= Cork.mono (ih (by omega) i' h) (L.touch n a)
          exact ⟨hz,hz,fun i' _=>by rw [sub_self]; exact Cork.zero⟩
       obtain ⟨D,hD,pD⟩:= capState (k:=k) L a hp he.le
       have he':= (treadmill L a ht hp hk he (le_refl N) (le_refl N) hb h₁ hD u q w hh (fun i _=>pD i)).pose j h
       apply Cork.cost he'
       have h₂: skulk H F p l k K/(inkPin K).patch.L.val≤ Real.exp (-d/4):=(archFoam L a ht (hk.trans (by omega))).trans (Real.exp_le_exp.mpr (by have hx:0≤d:= arc_nn ..; change -d/2 ≤ -d/4; linarith))
       have h₃:hills H F p i k l hk K*X^v≤ C.buy y:= (mul_le_mul_of_nonneg_right ((L.spend n a).story _ k _ hp ht hk) (show 0≤ X^v from pow_nonneg (zero_le_one.trans hb) _)).trans_eq (by unfold C X; rw [Credit.products,Credit.power])
       exact (add_le_add (mul_le_mul_of_nonneg_right h₂ h₁) (h₃.trans (Credit.thickened _ hy))).trans (Credit.step_cap b hy hv (V.age n (n+1) a (by omega)) (arch_pos ..))
end YM.WilsonCoeffUV.Cosmos
