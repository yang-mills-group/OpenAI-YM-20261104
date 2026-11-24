import YM.FormalBulk08.Sable.Bazaar

/-!
Time capacities from exponential prepayments. Produce polynomial body
contacts ON marker root; not an assembly in the mixed norm of physical labels. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Tundra
open Reef Flat Lattice Laurent Bloch Exterior Filter Function Next.Free RG Precision Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Bank Work.F03 Work.F05 Work.F08 PowerSeries
open Quire Sable Aster
open scoped NNReal Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G:Gauge}{X I J :Type}{τ:Time X}{η σ:X→ℝ}
variable {u r m n D:ℕ}
lemma sackSoft (u:ℕ)(h:Soft τ (fun i=> (σ i)⁻¹)):Soft τ (fun i=>sack u (σ i)):= (soft_coin τ _).times (((soft_coin τ 1).plus h).pows u)
section
variable {A B :ℝ}{ε:ℝ≥0} {o:I} {R:Reach I} {T: Tile I m}{f:I→I→ℝ}{s : ℝ}
lemma glitter_b (v:chain I m)(h:0<s)(he:ε≤1):glitter (grain R ε) u T v ≤ ENNReal.ofReal (sack u s)*glitter R s T v:= by
    unfold glitter;rw [plume,←mul_assoc];apply mul_le_mul_left; unfold Gorge.shine;rw [←ENNReal.ofReal_mul (sack_pos u h)];exact ENNReal.ofReal_le_ofReal (sack_for u h he _)
lemma grainB (u:ℕ)(h:0<s)(hb:ε≤1)(hp:Bail R s T B) : Bail (grain R ε) u T (sack u s*B):= by refine ⟨mul_nonneg (sack_pos u h) hp.1,fun i x=>?_⟩;rw [ENNReal.ofReal_mul (sack_pos u h)]; refine le_trans ?_ (mul_le_mul_right (hp.2 i x) _);rw [←ENNReal.tsum_mul_left];exact ENNReal.tsum_le_tsum fun v=> glitter_b v.val h hb
lemma grainG (u:ℕ)(h:0<s)(hb:ε≤1)(hp:Grate R s f B):Grate (grain R ε) u f (sack u s*B):= by refine ⟨mul_nonneg (sack_pos u h) hp.1,fun x=>?_⟩;rw [ENNReal.ofReal_mul (sack_pos u h)];refine le_trans ?_ (mul_le_mul_right (hp.2 x) _);rw [←ENNReal.tsum_mul_left];apply ENNReal.tsum_le_tsum;intro i;rw [←mul_assoc];apply mul_le_mul_left; unfold Gorge.shine;rw [←ENNReal.ofReal_mul (sack_pos u h)];exact ENNReal.ofReal_le_ofReal (sack_for u h hb _)
end

section
variable {I V:X→Type} {U:X→Type*} {δ g : X→ℝ} {R:∀ i,Reach (I i)} {o:∀ i,U i→I i}
variable {b:∀ i,U i→ℝ} {T S:∀ i:X,U i→Tile (I i) n}{ε:X→ℝ≥0}
variable (h:Soft τ (fun i=> (σ i)⁻¹))(hs:∀ i,0<σ i)(hp:∀ i,ε i≤1)
include h hs hp
-- matter grain
lemma stain (u:ℕ)(ht:Bear τ R o σ b T): Bear τ (fun i=>grain (R i) (ε i)) o (fun _=>u) b T:= by
   obtain ⟨C,c,T,H⟩:=ht; refine ⟨_,(sackSoft u h).times c,fun i=>mul_nonneg (sack_pos _ (hs i)) (T i),fun i p=>?_⟩;rw [mul_assoc];exact sack_to u (hs i) (hp i) (H i p)
lemma stains (u:ℕ)(ht:Matched τ R o σ δ b T S): Matched τ (fun i=>grain (R i) (ε i)) o (fun _=>u) δ b T S:= ⟨stain h hs hp u ht.left,stain h hs hp u ht.right,stain h hs hp u ht.chalk⟩
lemma pennCost (u:ℕ){T:∀ i:X,Tile (I i) n}(ht: Cost τ R σ T): Cost τ (fun i=>grain (R i) (ε i)) (fun _=>u) T:= by obtain ⟨C,c,V⟩:= ht; exact ⟨_,(sackSoft u h).times c,fun i=>grainB u (hs i) (hp i) (V i)⟩
lemma pennCosts (u:ℕ){T S:∀ i:X,Tile (I i) n}(ht: Totem τ R σ δ T S): Totem τ (fun i=> grain (R i) (ε i)) (fun _=> u) δ T S:= by
   obtain ⟨C,c,w,H⟩:=ht.nebula; refine ⟨pennCost h hs hp u ht.left,pennCost h hs hp u ht.right,_, (sackSoft u h).times c,fun i=>mul_nonneg (sack_pos _ (hs i)) (w i),fun i=>?_⟩; rw [mul_assoc]; exact grainB u (hs i) (hp i) (H i)
lemma glar (u:ℕ){P:∀ i:X,I i→I i→ℝ}(ht:Aster.Silver τ R σ P) : Aster.Silver τ (fun i=>grain (R i) (ε i)) (fun _=>u) P := by obtain ⟨v,C,c,W⟩:=ht; exact ⟨v,_,(sackSoft u h).times c,fun i=>grainG u (hs i) (hp i) (W i)⟩
lemma classic (u:ℕ){P Q:∀ i:X,I i→ I i →ℝ}(ht:Gilt τ R σ δ P Q): Gilt τ (fun i=> grain (R i) (ε i)) (fun _=>u) δ P Q:= by
   obtain ⟨C,c,w,V⟩:=ht.haze; refine ⟨glar h hs hp u ht.left, glar h hs hp u ht.right, _, (sackSoft u h).times c,fun i=>mul_nonneg (sack_pos u (hs i)) (w i),fun i=>?_⟩; rw [mul_assoc]; exact grainG _ (hs i) (hp i) (V i)
end
section
variable {α β A B C s:ℝ} {R Q:Row I J}[Fintype I][Fintype J]{T:Tile (Biglot I) r}{o:Biglot I}{ε:ℝ≥0}
lemma chase (h: R.strip s A)(e:Q.strip s A)(ht:(minusRows R Q).strip s B)(hs:0<s)(hx:0≤A)(hy:0≤B)(hp:ε≤1) (a:J)(hf:Knoxville (grain (fame _) ε) u o T C):
    Knoxville (grain (fame _) ε) u (o.1,a) (pearl (lands R) T-pearl (lands Q) T) (r*(C*(sack u s *Fintype.card J)^r*(B*A^(r-1)))):= by
    let f(b:Finset (Fin r))(i: Fin r):= if i∈b then R else Q; let P(b):=prism (fun i=> lands (f b i)) T
    rw [show pearl (lands R) T=P Finset.univ by simp only [P,f,Finset.mem_univ,↓reduceIte];rfl, show pearl (lands Q) T=P ∅ by simp only [P,f,Finset.notMem_empty,↓reduceIte];rfl, show ↑r=(↑(Finset.univ:Finset (Fin r)).card:ℝ) by simp]; apply Grail.stitch; intro t hp' i _ hi
    have hh k: (f t k).strip s A:= by unfold f;split<;>assumption
    rw [show P (insert i t)=prism (fun j=> lands (update (f t) i R j)) T from ?_,show P t=prism (fun j=> lands (update (f t) i Q j)) T from ?_, twin_arcs (η:=0) le_rfl hx T (penn_bail (petris hf) le_rfl) i (strip_mono h hs.le le_rfl) (strip_mono e hs.le le_rfl) (f t) (fun j=>strip_mono (hh j) hs.le le_rfl)]; rotate_left
    · unfold P; congr 1; ext1 j; by_cases h:j=i <;> simp [h,f,hi]
    · unfold P; congr 1; ext1 j; by_cases h:j=i <;> simp [h,f]
    let w(j:Fin r):= if i=j then B else A; let r':= update (f t) i (minusRows R Q); have hr j:(r' j).strip s (w j):=by by_cases he:j=i <;>simp [r',w,he,Ne.symm,ht,hh]
    have hw j:0≤w j:=by unfold w;split<;>assumption
    apply Knoxville.mono (school _ _ _ a _ hf hs hp hr hw).bill; simp only [one_mul, ←mul_assoc (sack u s),Finset.prod_mul_distrib, Finset.prod_const,Finset.card_univ,Fintype.card_fin]
    apply le_of_eq; rw [←Finset.mul_prod_erase _ _ (Finset.mem_univ i),show w i=B from if_pos rfl]; have h' : ∏ j∈Finset.univ.erase i,w j=∏ _∈Finset.univ.erase i,A:= Finset.prod_congr rfl (fun j hj=>if_neg (Ne.symm (Finset.ne_of_mem_erase hj)));rw [h'];simp; ring
end
end YM.FormalBulk08.Tundra
