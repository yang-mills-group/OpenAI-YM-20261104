import YM.FormalBulk08.Aster.Peas

/-! Linear substitutions. Positive rank controlling sub. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Aster
open Function Filter Lava Gorge Wick Lattice Laurent Bloch Wilson Lotus Bank Glide Work.F08
open scoped Topology ENNReal BigOperators Classical
variable {X Z I J : Type} (t:Time X) {V U: X→Type}{m n r:ℕ} (σ δ : X→ℝ)
def ease (P:(x:X)→ Row (V x) (U x)):Prop := ∃ C:X→ℝ, Soft t C ∧ (∀ x, 0≤C x) ∧ ∀ x, (P x).strip (σ x) (C x)
structure Maori (P Q:(x:X)→ Row (V x) (U x)): Prop where
   left : ease t σ P
   right : ease t σ Q
   lamp : ∃ C:X→ℝ, Soft t C ∧ (∀ x,0≤C x) ∧ ∀ x,(minusRows (P x) (Q x)).strip (σ x) (C x*δ x)
variable {t σ δ} {P Q:(x:X)→ Row (V x) (U x)} {T W:(x:X)→Tile (Biglot (V x)) m}
lemma maori_constant (h:ease t σ P): Maori t σ δ P P:= by
    refine ⟨h,h,0,soft_coin _ _,by simp,fun i=>?_⟩; rw [Pi.zero_apply,zero_mul,show minusRows (P i) (P i)=0 by ext;simp [minusRows]]; exact stillborn le_rfl

variable [∀ i, Fintype (V i)] [∀ i,Fintype (U i)] (hV: Soft t (fun i=>(Fintype.card (V i):ℝ))) (hU:Soft t (fun i=>(Fintype.card (U i):ℝ))) (hs:∀ i,0≤σ i)
omit hs hU hV [∀ i,Fintype (U i)] [∀ i, Fintype (V i)] in
lemma splits {R:Reach I}{S:Reach J}{T W:Tile I m}{M:I→J→ℝ}{σ τ A B C D:ℝ}(L:Solar R S σ τ) (h:0≤τ)(p:Bail R σ T A)(q:Bail R σ W B)(u:Hill L.capsule M C D)(z:Fin m): pearl M T-pearl M W=pearl M (T-W) := by
    funext v; rw [Pi.sub_apply,pearl,pearl, ←Summable.tsum_sub ((toss_pearl M L _ _ _ p u).summable h z v) ((toss_pearl M L _ _ _ q u).summable h z v)]; apply tsum_congr; intro w; exact (sub_mul ..).symm
omit hs hU hV [∀ i,Fintype (U i)] [∀ i, Fintype (V i)] in
lemma joist {R:Reach I}{S:Reach J}{T W:Tile I m}{M:I→J→ℝ}{σ τ A B C D:ℝ}(L:Solar R S σ τ)(h:0≤τ)(p:Bail R σ T A)(q:Bail R σ W B)(u:Hill L.capsule M C D)(z:Fin m): pearl M T+pearl M W=pearl M (T+W) := by
    funext v; rw [Pi.add_apply,pearl,pearl,←Summable.tsum_add ((toss_pearl M L _ _ _ p u).summable h z v) ((toss_pearl M L _ _ _ q u).summable h z v)];apply tsum_congr;intro w; exact (add_mul ..).symm
omit hs hU hV [∀ i,Fintype (U i)] [∀ i, Fintype (V i)] in
lemma gleam [Fintype I][Fintype J] {T:Tile (Biglot I) m}{P Q: Row I J}{σ C A B:ℝ} (hp:0≤σ)(hP:P.strip σ C)(hQ:Q.strip σ C)(h:(minusRows P Q).strip σ B)(hc:0≤C)(hb:0≤B)(hs:Bail (fame _) σ T A):
     Bail (fame _) σ (pearl (lands P) T-pearl (lands Q) T) (m*(A*((Fintype.card I)*((Fintype.card J)^(m-1):ℝ))*(B*C^(m-1)))) := by
    let F(R:Fin m→Row I J):=prism (fun i=>lands (R i)) T
    have ha :=hs.1
    refine telescope_bail _ F (fun R=>R.strip σ C) P Q hP hQ (fun V hV i=> ?_) (by positivity);unfold F;rw [twin_arcs hp hc T hs i hP hQ V hV]; let W:= update V i (minusRows P Q); let b (j:Fin m):= if j=i then B else C
    have hv j : (W j).strip σ (b j):=by by_cases he:j=i <;> simp [b,W,he,h,hV]
    have he : ∏ j,b j=B*C^(m-1):= by
       rw [←Finset.mul_prod_erase (Finset.univ : Finset (Fin m)) _ (Finset.mem_univ i),show b i=B from if_pos rfl]; congr 1;rw [show ∏ j∈Finset.univ.erase i,b j=∏ _j∈Finset.univ.erase i,C from Finset.prod_congr rfl (fun j hj=> if_neg (Finset.ne_of_mem_erase hj))]; simp
    exact (pack_end W hp hv (fun j=>by unfold b;split <;> assumption) T hs _ (by positivity) he.le).bail
include hs hV hU
lemma cost_pearl (hP:ease t σ P)(H:Cost t (fun i=> fame (V i)) σ T): Cost t (fun i=>fame (U i)) σ (fun i=> pearl (lands (P i)) (T i)):=by
    obtain ⟨C,c,p,Q⟩:=hP; obtain ⟨A,a,L⟩:= H; exact ⟨_,(soft_coin t 1).times ((a.times (hV.times c)).times ((hU.times c).pows _)),fun i=>water_bills (Q i) (L i) (hs i) (p i)⟩
lemma dust_pearl (hP:ease t σ P)(H:Dust t (fun i=> fame (V i)) σ δ T): Dust t (fun i=>fame (U i)) σ δ (fun i=> pearl (lands (P i)) (T i)):=by
    obtain ⟨C,c,p,Q⟩:=hP; obtain ⟨A,a,h,L⟩:=H; refine ⟨_,(soft_coin t 1).times ((a.times (hV.times c)).times ((hU.times c).pows (m-1))),fun i=>?_,fun i=>?_⟩
    · have hx:=h i; have he:= p i; positivity
    convert water_bills (Q i) (L i) (hs i) (p i) using 1;ring
lemma pearl_delta (z:Fin m)(hp:Maori t σ δ P Q)(hd:∀ i,0≤δ i)(H:Totem t (fun i=> fame (V i)) σ δ T W) : Totem t (fun i=> fame (U i)) σ δ (fun i=> pearl (lands (P i)) (T i)) (fun i=>pearl (lands (Q i)) (W i)) := by
    refine ⟨cost_pearl hV hU hs hp.left H.left,cost_pearl hV hU hs hp.right H.right,?_⟩
    obtain ⟨C,c,p,hP⟩:= hp.left; obtain ⟨B,b,r,hQ⟩:= hp.right; obtain ⟨A,a,y,K⟩:=hp.lamp; obtain ⟨X,L,E⟩:= H.left;obtain ⟨Y,Y',Z⟩:= H.right
    have he (i): 0≤C i+B i:= add_nonneg (p i) (r i)
    have hh : Dust t (fun i=> fame (U i)) σ δ (fun i=> pearl (lands (P i)) (W i)-pearl (lands (Q i)) (W i)):= by
        refine ⟨_, (soft_coin t m).times ((Y'.times (hV.times (hU.pows (m-1)))).times (a.times ((c.plus b).pows (m-1)))),fun i=>by have h:=he i; have ht:= (Z i).1;have hu:= y i;positivity,fun i=>?_⟩
        convert gleam (hs i) (strip_mono (hP i) le_rfl (le_add_of_nonneg_right (r i))) (strip_mono (hQ i) le_rfl (le_add_of_nonneg_left (p i))) (K i) (he i) (mul_nonneg (y i) (hd i)) (Z i) using 1;ring
    convert (dust_pearl hV hU hs hp.left H.nebula).plus hh using 1; ext1 i
    rw [←splits (bridge _ _ _ (hs i)) (hs i) (E i) (Z i) (grad_line _ (hP i) (p i)) z, sub_add_sub_cancel]
end YM.FormalBulk08.Aster
