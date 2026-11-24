import YM.WilsonCoeffUV.Stable.RefundEstimate
/-!
# Poly energy of refunds and residual. Register cost Σ depends announced k, y endpoint.
-/
set_option autoImplicit false
set_option maxHeartbeats 510000
noncomputable section
namespace YM.WilsonCoeffUV.Shard
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {n:Side}{V:Type*}{r h D l j i e k a m b u N M c:ℕ} {G:Gauge}{F:Labels.Frame G h}{s A C t B x δ:ℝ}{H: Hol G}
variable {T:SectionData F}{p:h<D}{v: Rails h k u e}{E W K U':Credit}

lemma cargo_rise (R S:Coil F)(A B x:ℝ) (hx:0≤x)(w:0≤A)(q:0≤B)(hp:0≤δ)(g:∀ i≤ e,∀ j t,twain A δ (lineS R i j t) (lineS S i j t)) (u v:Verse F) (h:∀ i≤e,∀j, twain (B*x) δ (coeff i (u j)) (coeff i (v j))) (i:ℕ)(hi:i≤ e)(j'):
   twain ((∑ _ : Alma F,(e+1:ℕ)*(2*A*B))*x) δ (coeff i ((R*ᵥu) j')) (coeff i ((S*ᵥv) j')):=by
    unfold Matrix.mulVec dotProduct; rw [map_sum,map_sum, Finset.sum_mul]; apply twain.sum; intro j _; rw [coeff_mul,coeff_mul]; let T:= Finset.antidiagonal i; let Q:=2*(B*x)*A
    have hp': ∀ a∈ T, twain Q δ (coeff a.1 (R j' j)*coeff a.2 (u j)) (coeff a.1 (S j' j)*coeff a.2 (v j)) :=fun i p=> (g i.1 (by have he:= Finset.mem_antidiagonal.mp p; omega) j' j).mul (h _ (by have he:= Finset.mem_antidiagonal.mp p; omega) j)
    refine (twain.sum T hp').lift ?_ hp
    rw [Finset.sum_const, Finset.Nat.card_antidiagonal,nsmul_eq_mul]; apply (mul_le_mul_of_nonneg_right (show ((i+1:ℕ):ℝ)≤(e+1:ℕ) by exact_mod_cast Nat.add_le_add_right hi 1) (show 0≤ Q by unfold Q; positivity)).trans; exact le_of_eq (by unfold Q; ring)
lemma musicFund (A B:Cost)(U V x:ℝ) (hx:0≤x)(hu:0≤U)(hv:0≤V)(hp:0≤δ)(g:∀ i j:ℕ,i≤e→j≤e→ twain U δ (coeff i (A^j)) (coeff i (B^j))) (P Q:Verse F)(p:∀ i≤e,∀j,twain (V*x) δ (coeff i (P j)) (coeff i (Q j))) (i:ℕ)(hi:i≤ e)(j') :
   twain ((e+1:ℕ)*(2*U*V)*x) δ (coeff i (music A P j')) (coeff i (music B Q j')):=by
    let M:=2*U*(V*x); let S:= Finset.range (i+1); rw [music,music,reelQuote,reelQuote]
    have h (j)(p':j∈ S): j ≤ i:= Nat.le_of_lt_succ (Finset.mem_range.mp p')
    apply (twain.sum S (fun j hj=> (p j ((h j hj).trans hi) j').mul (g (i-j) j (le_trans (Nat.sub_le i j) hi) ((h j hj).trans hi)))).lift _ hp
    rw [Finset.sum_const,Finset.card_range,nsmul_eq_mul]; apply (mul_le_mul_of_nonneg_right (show ((i+1:ℕ):ℝ)≤ (e+1:ℕ) by exact_mod_cast Nat.add_le_add_right hi 1) (show 0≤ M by unfold M; positivity)).trans; exact le_of_eq (by unfold M; ring)
-- one more subset Ledger.
structure Chest (H:Hol G)(T:SectionData F)(p:h<D)(v:Rails h k u e)(E W K U:Credit) where
    I : Canopy H T p v E W K
    L : ChorusLine H T p e E W U
    agree : L.arch= I.L.L

namespace Chest
variable (C: Chest H T p v E W K U')
def quest : CourseS H T p e E W U':=⟨C.L,⟨C.I.R,C.I.m,C.I.c-C.I.m,C.I.N,C.I.M,C.I.b,C.I.ha,(show C.I.m+(C.I.c-C.I.m)≤C.I.b from by have h:=C.I.hv; have hp:=C.I.ht; omega),C.I.hn,C.I.hm⟩,by rw [C.agree]⟩
lemma at_eq : C.I.m+C.quest.length=C.I.c:= Nat.add_sub_of_le C.I.hv
lemma sub_p (g:C.I.m+i ≤ C.I.c): i≤ C.quest.length:=by linarith [C.at_eq]
lemma water (g:C.I.m+i ≤ C.I.c): C.I.R.y (C.I.m+i) ≤ C.quest.Age:= C.quest.I.covers (C.sub_p g)
lemma rateK : C.quest.cab = C.I.R.tempC C.I.c C.I.b:=by rw [← C.at_eq]; rfl
end Chest
-- Σ window actual counts
def pur (a:ℝ): Credit:=⟨0,max 1 a,le_max_left ..⟩
lemma pure_goal (a x:ℝ): a ≤ (pur a).buy x:=by simp [pur,Credit.buy]
lemma bootPaid (H:Hol G)(T:SectionData F)(p:h<D)(v:Rails h k u e)(E W K U:Credit) : ∃ C:Credit,∀ (L:Chest H T p v E W K U) (i:ℕ), L.I.m+i ≤ L.I.c →∀ j≤ e,∀ r:Alma F,
   let I:=L.I; let A:=I.R; let D:= I.m+i; twain ((C.buy L.quest.Age)*A.tempC D I.c*I.wealth) (A.tempC I.c I.b) (coeff j (boot A.draws A.paid T p I.N k I.c I.m i I.X r)) (coeff j (boot A.draws A.paid T p I.M k I.c I.m i I.Y r)):=by
    obtain ⟨X,P⟩ := SeasonM e H T p E W U
    obtain ⟨Y,Q⟩:= SeasonC e H T p E W U
    obtain ⟨V,B⟩:= barley_bill H T p v E W K
    let A0:ℝ:= ((e+1:ℕ):ℝ)* (2*∑ _ : Alma F, (e+1:ℕ)*(2:ℝ)); let C:=(((pur A0).prodC Y).prodC X).prodC V
    refine ⟨(Credit.leanC.prodC C),?_⟩; intro L i z j q r I R m
    let Z:= L.quest.Age; have hZ:1≤ Z:=L.quest.I.warm; let δ:=R.tempC I.c I.b; let x:= R.tempC m I.c*I.wealth; have hd:0≤ δ:= (trail_pos ..).le; have hx:0≤ x:= mul_nonneg (trail_pos ..).le I.ex.2.2.1
    let H0:= C.buy Z*x; have hH:0≤H0:= mul_nonneg (zero_le_one.trans (C.purchase hZ)) hx
    let u' (l:ℕ):=barley R.draws R.paid T p I.N k I.c I.X l; let v' (l:ℕ):=barley R.draws R.paid T p I.M k I.c I.Y l; let F'(l l'): Verse F:= steep R.draws R.paid T p I.N l l' (u' l); let G'(l l'): Verse F:= steep R.draws R.paid T p I.M l l' (v' l)
    have ht n (t:n∈ Finset.range i): twain H0 δ (coeff j (F' (I.m+n) (i-n) r)) (coeff j (G' (I.m+n) (i-n) r)):=by
        let b:= I.m+n; have hn:= Finset.mem_range.mp t; let L':= L.quest; let S:= i-n; have hu:n+S ≤ L'.length:= le_trans (Nat.le_of_eq (Nat.add_sub_of_le hn.le)) (L.sub_p z)
        let W:= L'.clipW hu; let T':CourseS H T p e E _ U:=⟨L.L, W,by unfold W L' CourseS.clipW; exact L.quest.peace⟩
        let y:= T'.Age; have hy:1≤ y:=T'.I.warm; let θ:=T'.cab
        obtain ⟨hr,hv⟩:=CourseS.cup L' hu; have hk:θ≤ δ:=hv.trans_eq L.rateK
        let M n:=bindingS R.draws R.paid T p n b S false; let A n:=relativeC R.draws R.paid n b S; let f:=u' b; let g:=v' b
        have he: T'.robe.arch.V=R:=by unfold T'; dsimp only; rw [L.agree]
        have hM i (w:i≤ e) j k : twain (X.buy Z) δ (lineS (M I.N) i j k) (lineS (M I.M) i j k):=by
            have ht:= ((P T' i w j k).wide hk).lift (X.elder hy hr) hd; unfold M; change twain _ _ (lineS (bindingS T'.vols.draws T'.vols.paid T p _ b S false) _ _ _) (lineS (bindingS T'.vols.draws T'.vols.paid T p _ b S false) _ _ _) at ht; unfold CourseS.vols at ht; rw [he] at ht; exact ht
        have hA i j (p':i≤e) (v:j≤e) : twain (Y.buy Z) δ (coeff i ((A I.N)^j)) (coeff i ((A I.M)^j)) :=by
            have H:= ((Q T' i j p' v).wide hk).lift (Y.elder hy hr) hd; unfold A; change twain _ _ (coeff i ((relativeC T'.vols.draws T'.vols.paid _ b S)^j)) (coeff i ((relativeC T'.vols.draws T'.vols.paid _ b S)^j)) at H; unfold CourseS.vols at H; rw [he] at H; exact H
        have hp : R.anchor ≤ b:= I.ha.trans (by unfold b; omega); have h': b< I.c:= lt_of_lt_of_le (Nat.add_lt_add_left hn _) z
        have hC i (q':i≤e) k: twain (V.buy Z*x) δ (coeff i (f k)) (coeff i (g k)):=by
            have hv := B { I with m:=b, ha:=hp,hv:=h'.le} h' i q' k; apply hv.lift _ hd; unfold x; rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (mul_le_mul (V.elder (R.depth b hp) (L.water h'.le)) (PathCost.narrow _ (Nat.add_le_add_left hn.le I.m) I.c) (trail_pos ..).le (zero_le_one.trans (V.purchase hZ))) I.ex.2.2.1
        let O:= (∑ _ : Alma F,(e+1:ℕ)*(2*X.buy Z*V.buy Z)); have hX:0≤X.buy Z:= zero_le_one.trans (X.purchase hZ); have hY:0≤ Y.buy Z:= zero_le_one.trans (Y.purchase hZ); have hV:0≤ V.buy Z:= zero_le_one.trans (V.purchase hZ); have hO:0≤ O:=by unfold O; positivity
        apply twain.lift (musicFund (A I.N) (A I.M) (Y.buy Z) O x hx hY hO hd hA (M I.N*ᵥ f) (M I.M*ᵥ g) (fun i h k=> cargo_rise (M I.N) (M I.M) (X.buy Z) (V.buy Z) x hx hX hV hd hM f g hC i h k) j q r) _ hd
        apply mul_le_mul_of_nonneg_right _ hx; unfold C; simp only [Credit.products];
        apply le_trans _ (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (pure_goal _ _) hY) hX) hV); unfold O A0; simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; exact le_of_eq (by ring)
    unfold boot; rw [Finset.sum_apply,map_sum,Finset.sum_apply,map_sum]; refine (twain.sum (Finset.range i) ht).lift ?_ hd
    rw [Finset.sum_const,Finset.card_range,nsmul_eq_mul]; have hg : (i:ℝ) ≤ Z:= (Nat.cast_le.mpr (L.sub_p z)).trans L.quest.I.buySpan; unfold H0 x; apply le_trans (mul_le_mul_of_nonneg_right hg hH); rw [Credit.products,Credit.lean_cost]; exact le_of_eq (by unfold H0 x Z I R; ring)
end YM.WilsonCoeffUV.Shard
