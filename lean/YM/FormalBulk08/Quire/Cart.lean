import YM.FormalBulk08.Quire.Cycler
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Quire
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Dawn Grail Palm Wine Rial Aster Roof
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {X I : Type*} {Y U:Type} {V W:X→ Type} {r m n:ℕ} {η σ A B C α β:ℝ}
lemma rose_bill {P:Reach Y}{R:Reach U}{x:Y}{y:U}(W:Solar P R η σ)(M:Fin m→Y→U→ℝ)(H:W.capsule x y=1) {F:Tile Y m}(h:Knoxville P η x F C){A B:Fin m→ℝ}(hp:∀ i,Hill W.capsule (M i) (A i) (B i))(he:∀ i,0≤A i): Allow R σ y (fun v t=> F t*∏ i,M i (t i) (v i)) (W.fare*(C*∏ i,A i)) := by
    refine ⟨mul_nonneg W.good (mul_nonneg h.1 (Finset.prod_nonneg fun i _=>he i)),?_⟩; rw [ENNReal.tsum_comm,ENNReal.ofReal_mul W.good, ENNReal.ofReal_mul h.1, ENNReal.ofReal_prod_of_nonneg (fun i _=>he i)]
    let N i (a:U) (b:Y):= W.capsule b a * ‖M i b a‖ₑ
    refine le_trans ?_ (mul_le_mul_right (mul_le_mul_left h.2 _) _)
    rw [←ENNReal.tsum_mul_right,←ENNReal.tsum_mul_left]; refine ENNReal.tsum_le_tsum fun v=>?_
    have hh : (∏ i:Fin m,∑' a, N i a (v i)) ≤ ∏ i:Fin m,ENNReal.ofReal (A i):= Finset.prod_le_prod' (fun i _=> (hp i).rows (v i))
    rw [←eun_tsum (fun i a=>N i a (v i))] at hh
    refine le_trans ?_ (mul_le_mul_right (mul_le_mul_right hh (penon P x η F v)) _)
    rw [←ENNReal.tsum_mul_left,←ENNReal.tsum_mul_left]; refine ENNReal.tsum_le_tsum fun t=>?_
    have hx:=W.carried (Fin.cons x v : chain Y (m+1)) (Fin.cons y t); simp only [Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ,H,one_mul] at hx; apply (mul_le_mul_left hx _).trans_eq
    have ht (s:Finset (Fin m)): ‖∏ i∈s,M i (v i) (t i)‖ₑ = ∏ i∈s, ‖M i (v i) (t i)‖ₑ := by induction s using Finset.induction <;> simp_all [enorm_mul]
    unfold penon N herb; change _ = _ *(_*(∏ i:Fin m, W.capsule (v i) (t i)*‖M i (v i) (t i)‖ₑ)); rw [enorm_mul,ht,Finset.prod_mul_distrib]; ring

-- input subtraction on absolute sums, root common type equality
variable [Fintype Y][Fintype U] {S R: Tile (Biglot Y) m}{P Q : Row Y U}{a:Biglot Y}
lemma hilly (P:Row Y U)(T:Tile (Biglot Y) m)(b:U)(h:Knoxville (fame _) η a T B) (hs:0≤η)(hp:P.strip η C)(hc:0≤C): Allow (fame _) η (a.1,b) (fun v t=> T t *∏ i,lands P (t i) (v i)) (1*(B*(Fintype.card U * C)^m)):= by
   exact quake (bridge Y U _ hs) _ (by simp [bridge,linkshine,Gorge.shine]) h (fun i=>grad_line P hp hc) (by positivity)
lemma haggle (b:U)(hs:Knoxville (fame _) η a S A)(h: Knoxville (fame _) η a R B)(hp:P.strip η α)(hα:0≤α)(he:0≤η): pearl (lands P) S-pearl (lands P) R=pearl (lands P) (S-R):= by
   funext v; unfold pearl; rw [Pi.sub_apply,← Summable.tsum_sub ((hilly P S b hs he hp hα).points he v).of_norm ((hilly P R b h he hp hα).points he v).of_norm]; refine tsum_congr fun k=>?_ ;exact (sub_mul ..).symm
lemma hurray (b:U)(hx:Knoxville (fame _) η a S A)(hs:0≤η)(hP:P.strip η α)(hQ:Q.strip η α)(h:(minusRows P Q).strip η β)(he:0≤α)(hp:0≤β): Knoxville (fame _) η (a.1,b) (pearl (lands P) S-pearl (lands Q) S) (m*(A*(Fintype.card U:ℝ)^m*(β*α^(m-1)))):= by
    let f(u:Finset (Fin m)) (i:Fin m):= if i∈u then P else Q
    let F(u):=prism (fun i=>lands (f u i)) S
    rw [show pearl (lands P) S= F Finset.univ by simp only [F,f,Finset.mem_univ,↓reduceIte];rfl, show pearl (lands Q) S= F ∅ by simp only [F,f,Finset.notMem_empty,↓reduceIte];rfl, show (m:ℝ)=(Finset.univ:Finset (Fin m)).card by simp];apply Grail.stitch; intro t ht i _ hi
    have hh j : (f t j).strip η α:= by unfold f;split<;> assumption
    rw [show F (insert i t)= prism (fun j=>lands (update (f t) i P j)) S from ?_,show F t = prism (fun j=>lands (update (f t) i Q j)) S from ?_, twin_arcs hs he S (penn_bail hx hs) i hP hQ (f t) hh]; rotate_left
    · unfold F; congr 1;ext1 j;by_cases h:j=i <;> simp [h,f,hi]
    · unfold F; congr 1;ext1 j;by_cases h:j=i <;> simp [h,f]
    let w(j:Fin m):= if i=j then β else α; let R:= update (f t) i (minusRows P Q); have hr j:(R j).strip η (w j):= by by_cases he:j=i <;> simp [he,h,Ne.symm,R,w,hh]
    have hT j:0≤w j:=by unfold w;split<;> assumption
    refine Knoxville.mono (rose_bill (y:=(a.1,b)) (bridge Y U _ hs) _ (by simp [bridge,linkshine,Gorge.shine]) hx (fun i=>grad_line _ (hr i) (hT i)) (fun i=> mul_nonneg (Nat.cast_nonneg _) (hT i))).bill ?_
    simp only [bridge,one_mul,Finset.prod_mul_distrib, Finset.prod_const,Finset.card_univ,Fintype.card_fin, mul_assoc]; apply le_of_eq; rw [←Finset.mul_prod_erase _ _ (Finset.mem_univ i),show w i=β from if_pos rfl] -- w i
    have hh : ∏ j∈Finset.univ.erase i,w j=∏ _∈Finset.univ.erase i,α:= Finset.prod_congr rfl (fun j hj=> if_neg (Ne.symm (Finset.ne_of_mem_erase hj)))
    rw [hh]; simp
end YM.FormalBulk08.Quire
