import YM.MS.RapidIntegration
import YM.MS.CompareSymbol
/-!
# Entire comparison of a single line, with tail at integration too

Keep `Like` estimates for the low-momentum evaluation (may still use
arguments anywhere in Euclidean space) and `Rapid` estimates on the
cut or full region as needed. These don't require momentum parity/readability.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS
open Function Set Real Filter MeasureTheory
open scoped Topology ContDiff
variable {ι E F G P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
variable {S : Scale ι} {a v w : ι → ℝ} {D : ι → Set E}
namespace Like
variable {l r : Kern ι E G}
lemma pull (h : Like S.full S a l r fun i _=>w i) (L : P→L[ℝ] E) : Like S.full S a (fun i p=>l i (L p)) (fun i p=>r i (L p)) fun i _=>w i :=
  ⟨Bound.linear L h.lat, Bound.linear L h.std, Bound.linear L h.gain⟩
lemma up (h : Like S.full S a l r fun i _=>w i) (H : ∀ i, a i ≤ v i) : Like S.full S v l r fun i _=>w i :=
  ⟨h.lat,h.std,h.gain.raise (Cost.of_le fun i p he=> mul_le_mul_of_nonneg_left (H i) (h.lat.nonneg i p he))⟩
end Like
namespace Line
variable {r : Kern ι E G}
lemma cut (h : Line S D r w) {D' : ι → Set E} (H : ∀ i,D' i ⊆ D i) : Line S D' r w := by
    refine fun b=> ⟨(h b).smooth,fun j=>?_⟩
    obtain ⟨C,hC,k,hk⟩:=(h b).quoted j
    exact ⟨C,hC,k,fun i p hp=> hk i p (H i hp)⟩
lemma L (h : Line S D r w) (A : G →L[ℝ] F) : Line S D (fun i p=>A (r i p)) w := fun j => (h j).L A
lemma monotone (h : Line S D r w) (H : ∀ i, w i ≤ v i) : Line S D r v := fun j=> (h j).raise (Cost.of_le (fun i p _=> div_le_div_of_nonneg_right (H i) (pow_nonneg (S.weight_pos i p).le _)))
lemma tail (h : Line S (fun _=>univ) r w) (hw : ∀ i, 0 ≤ w i) (hd : ∀ i p, p ∉ D i → 1 ≤ ‖p‖) (j : ℕ) : Line S (fun i=> (D i)ᶜ) r fun i=> w i*(S.length i ^ j)⁻¹ := by
   intro b; refine ((Line.cut h (D':=fun i=> (D i)ᶜ) (fun _=> subset_univ _)) (b+j)).raise (Cost.of_le (fun i p hp=> ?_))
   specialize hd i p hp; have he : S.length i ≤ S.weight i p:= by
      unfold Scale.weight; nlinarith [S.pos i]
   have hw := hw i; have hs:= S.weight_pos i p; have hp := S.pos i; dsimp only; simp only [pow_add,div_eq_mul_inv,mul_inv]; rw [show w i * ((S.weight i p ^ b)⁻¹ * (S.weight i p ^ j)⁻¹) = w i*(S.weight i p ^ j)⁻¹ * (S.weight i p ^ b)⁻¹ by ring]; gcongr
end Line

structure Sharp (S : Scale ι) (a : ι → ℝ) (D : ι → Set E) (l r : Kern ι E G) (w : ι → ℝ) : Prop where
   both : Like S.full S a l r (fun i _=>w i)
   lattice : Line S D l w
   std : Line S (fun _=>univ) r w
   close : Line S D (fun i p=>l i p-r i p) fun i=>w i*a i

structure Value (S : Scale ι) (a : ι → ℝ) (D : ι → Set E) (l r : Kern ι (E×F) G) (w : ι → ℝ) : Prop where
   lat : Rapid S D l w
   cont : Rapid S (fun _=>univ) r w
   close : Rapid S D (fun i p=>l i p-r i p) fun i=> w i*a i
   high : Rapid S (fun i=> (D i)ᶜ) r fun i=> w i*a i
namespace Sharp
variable {l r : Kern ι E G} (h : Sharp S a D l r w)
lemma linear (h : Sharp S a D l r w) (A : G →L[ℝ] F) : Sharp S a D (fun i p=>A (l i p)) (fun i p=>A (r i p)) w :=
   ⟨h.both.L A,h.lattice.L A,h.std.L A,by simpa only [map_sub] using h.close.L A⟩
lemma up (h : Sharp S a D l r w) (H : ∀ i, a i ≤ v i) : Sharp S v D l r w :=
   ⟨h.both.up H,h.lattice,h.std,h.close.monotone fun i=> mul_le_mul_of_nonneg_left (H i) (h.both.lat.nonneg i 0 trivial)⟩
lemma value (h : Sharp S a D l r w) {j:ℕ} (H : ∀ i, (S.length i ^ j)⁻¹ ≤ a i) (hD : ∀ i p, p ∉ D i → 1≤ ‖p‖) :
   Value S a D (fun i (p : E×F)=>l i p.1) (fun i (p : E×F)=>r i p.1) w :=
   ⟨h.lattice.rapid,h.std.rapid,h.close.rapid, ((h.std.tail (fun i=> h.both.lat.nonneg i 0 trivial) hD j).monotone fun i=> mul_le_mul_of_nonneg_left (H i) (h.both.lat.nonneg i 0 trivial)).rapid⟩
lemma zero (hw : ∀ i, 0 ≤ w i) (ha : ∀ i, 0 ≤ a i) : Sharp S a D (fun _ _=>(0:G)) (fun _ _=>(0:G)) w where
   both := Like.zero (fun i _ _=> hw i) ha
   lattice _ := Costs.zero fun i p _=> div_nonneg (hw i) (pow_nonneg (S.weight_pos i p).le _)
   std _ := Costs.zero fun i p _=> div_nonneg (hw i) (pow_nonneg (S.weight_pos i p).le _)
   close _ := by simp only [sub_self]; exact Costs.zero fun i p _=> div_nonneg (mul_nonneg (hw i) (ha i)) (pow_nonneg (S.weight_pos i p).le _)

end Sharp
namespace Value
variable {l r l' r' : Kern ι (E×F) G} {f g : Kern ι (E×F) P} (h : Value S a D l r w)
lemma bilinear {W: Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] (h : Value S a D l r w) (B : G →L[ℝ] P →L[ℝ] W) (H : Like S.full S a f g fun i _ => v i) :
    Value S a D (fun i p=>B (l i p) (f i p)) (fun i p=> B (r i p) (g i p)) (fun i=> w i*v i) := by
   refine ⟨h.lat.bilinear B H.lat,h.cont.bilinear B H.std, ?_, ?_⟩
   · let F : ι → ℝ := fun i=> w i*v i*a i
     have ht := (h.lat.bilinear B H.gain).monotone (Cost.of_le (fun i p _=> (mul_assoc _ _ _).symm.le : ∀ i p, p ∈ _ → _ ≤ F i)) -- tactic
     have hc := (h.close.bilinear B H.std).monotone (Cost.of_le (fun i p _=> (mul_right_comm _ _ _).le : ∀ i p,p ∈ _ → _ ≤ F i))
     convert ht.add hc using 1; ext; simp only [map_sub,_root_.sub_apply]; abel
   exact (h.high.bilinear B H.std).monotone (Cost.of_le fun i p _=> (mul_right_comm (w i) (a i) (v i)).le)
lemma mul {l r f g : Kern ι (E×F) ℂ} (h : Value S a D l r w) (H : Like S.full S a f g fun i _=>v i) :
    Value S a D (fun i x=> l i x * f i x) (fun i x =>r i x*g i x) (fun i=> w i*v i):= h.bilinear (ContinuousLinearMap.mul ℝ ℂ) H
lemma add (h : Value S a D l r w) (H : Value S a D l' r' w) : Value S a D (fun i x=>l i x+l' i x) (fun i x=>r i x+r' i x) w := by
    refine ⟨h.lat.add H.lat,h.cont.add H.cont,?_, h.high.add H.high⟩; simpa [add_sub_add_comm] using h.close.add H.close
lemma zero (hw :∀ i, 0 ≤ w i) (ha :∀ i, 0 ≤ a i): Value S a D (fun _ (_:E×F)=>(0:G)) (fun _ (_:E×F)=>0) w where
    lat _ := Costs.zero fun i p _=> div_nonneg (hw i) (pow_nonneg (S.weight_pos _ _).le _)
    cont _ := Costs.zero fun i p _=> div_nonneg (hw i) (pow_nonneg (S.weight_pos _ _).le _)
    close _ := by simp only [sub_self]; exact Costs.zero fun i p _=> div_nonneg (mul_nonneg (hw i) (ha i)) (pow_nonneg (S.weight_pos _ _).le _)
    high _ := Costs.zero fun i p _=> div_nonneg (mul_nonneg (hw i) (ha i)) (pow_nonneg (S.weight_pos _ _).le _)
lemma sum {I:Type*} (k: Finset I) {p q : I → Kern ι (E×F) G} (h : ∀ i∈k, Value S a D (p i) (q i) w) (hw : ∀ i, 0 ≤ w i) (ha : ∀ i, 0 ≤ a i) : Value S a D (fun i x=>∑ j ∈ k,p j i x) (fun i x=>∑ j∈k,q j i x) w := by
    classical
    induction k using Finset.induction with
    | empty => simpa using Value.zero (S:=S) (D:=D) (F:=F) (G:=G) hw ha
    | insert i k hz ih=> simpa only [Finset.sum_insert hz] using (h i (Finset.mem_insert_self ..)).add (ih (fun i hx=>h i (Finset.mem_insert_of_mem hx)))

variable [CompleteSpace G] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
theorem integrates (h : Value S a D l r w) (hw : ∀ i,0≤ w i) (ha : ∀ i,0≤ a i) (hD : ∀ i, MeasurableSet (D i)) (μ : Measure E) [μ.IsAddHaarMeasure] :
    Like S.full S a (fun i p=>∫ q in D i, l i (q,p) ∂μ) (fun i p=>∫ q, r i (q,p) ∂μ) fun i _=> w i*(S.length i ^ Module.finrank ℝ E)⁻¹ := by
   let b:=Module.finrank ℝ E + 1; have hb : Module.finrank ℝ E < b:= Nat.lt_succ_self _
   let μ' (i:ι) := μ.restrict (D i); let ω' (i:ι):= μ.restrict (D i)ᶜ
   let T i:=w i*(S.length i ^ Module.finrank ℝ E)⁻¹*a i
   have hr := Reserve.cutHaar (S:=S) (μ:=μ) hD b hb; have hv := Reserve.cover (S:=S) (μ:=μ) b hb; have hu : Reserve S (fun i=>(D i)ᶜ) ω' b:= Reserve.cutHaar (fun i=>(hD i).compl) b hb
   have hw' : ∀ i,0 ≤ w i*a i:= fun i=> mul_nonneg (hw i) (ha i)
   have L0 : Bound S (fun i p=> ∫ q, l i (q,p)-r i (q,p) ∂(μ' i)) T := (h.close.consumes hr hw' (Reserve.cutoff_mass b hb)).raise (Cost.of_le fun i p hp=> (mul_right_comm (w i) (a i) _).le)
   have L1 : Bound S (fun i p=> ∫ q, r i (q,p) ∂(ω' i)) T := (h.high.consumes hu hw' (Reserve.cutoff_mass b hb)).raise (Cost.of_le fun i p hp=> (mul_right_comm (w i) (a i) _).le)
   refine ⟨h.lat.consumes hr hw (Reserve.cutoff_mass b hb), h.cont.consumes hv hw (by simpa using Reserve.cutoff_mass (S:=S) (μ:=μ) (D:=fun _=>univ) (F:=F) b hb), ?_⟩
   convert! L0.sub L1 using 1; funext i p
   have H := h.cont.integrates hv i p; have H' := h.lat.integrates hr i p; dsimp only [μ',ω']; rw [integral_sub H' H.restrict,← integral_add_compl (hD i) H]; abel
end Value
end YM.MS
