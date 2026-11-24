import YM.WilsonBridge.Word
/-!
# Agreement of axial `View` and Gaussian integral pairing on all finite polynomials
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBridge.Based.Position
open MS MS.Book MS.Koszul MS.Swirl MS.Puff MS.Cylinder MS.Orbit
open Puff.Engine Puff.SplitP Puff.Actors Orbit.LogReal Orbit.Cog Book.Convolve
open PertExtension GaussianScore Orb Function Finset Lattice MeasureTheory WilsonBridge.Polynomial
open scoped BigOperators ContDiff Classical
variable {G:Gauge}{n:Side} (he : Even n.val)
local notation "V"=> Position.Letter G n
local notation "P"=> Position.Parity G n
local notation "K"=> noFP G he
local notation "ν"=> PertExtension.Chart.tangent G (Cotree n)
local notation "Φ"=> saddle (G:=G) he
local notation "ρ"=> Position.real_cov (G:=G) (n:=n)
local infixl:70 " ⋆ "=> product (Position.Parity G n)
local notation "z[" u "]"=> (fun i=> (Position.real_cov i u:ℂ))
local notation "W"=> View (noFP G he)
lemma letter_payment (x y:V): Chill K x y= ( (Φ).wick (ρ x) (ρ y) : ℝ) := by
  unfold Law.wick Chill noFP; rw [inverse_turn (Φ)]; ring
lemma notPaid (i:V)(hp:P i=true) : ρ i=0:= by
    rcases i with (i|i)|(i|i) <;> first| rfl| change false=true at hp; contradiction
lemma noFP_off (i j:V)(h:P j=true) : Chill K i j=0:= by rw [letter_payment,Law.wick,notPaid j h]; simp
lemma tied (x:Dir G n) : Tie P (fun _:Unit=>false) (chord z[x]) := by
    rintro i ⟨⟩ h; rcases hz:P i with _|_; · rfl
    exact False.elim (h (by change (( (real_cov i) x:ℝ):ℂ)=0; rw [notPaid i hz]; simp))
lemma witness : Clear P K ∧ Cog.Sym P K:= by
    refine ⟨?_,fun i j=> ?_⟩
    · rintro ((i|i)|(i|i)) ((j|j)|(j|j)) hv <;> first| rfl| simp [noFP,real_cov] at hv
    rcases hi:P i with _|_; · rw [cross_false,one_mul]; unfold noFP; rw [inverse_turn (Φ)];
    unfold noFP; rw [notPaid i hi]; simp
-- oriented Wick differentiation with a real (only even) line
local notation "D_[" i "]" => TraceD i (noFP G he)
lemma trace_part (i j:V)(F:Raw V ℂ) : D_[i] (atLetter j ⋆ F) = (Chill K i j) • F + atLetter j ⋆ D_[i] F:= by
    classical
    have H (x:V): Chill K i x • (MS.Koszul.sign P (P x) (atLetter j) ⋆ D x F)=Chill K i x • (atLetter j ⋆ D x F):= by
       cases h:P x; · rw [sign_id]
       rw [noFP_off he i x h,zero_smul,zero_smul]
    simp_rw [trdΩ,map_sum,map_smul,D_product,smul_add, H, Finset.sum_add_distrib]; congr 1; rw [Finset.sum_eq_single_of_mem j (mem_univ _),hear,coin_product,one_smul]; exact fun x _ h=> by rw [unheard _ h,map_zero,LinearMap.zero_apply,smul_zero]
lemma evaporate (i:V) : D_[i] (coin 1)=0:= by unfold TraceD; simp [LinearMap.sum_apply,coin_nod]
lemma trace_word (i:V)(m:ℕ)(x: Fin (m+1)→ V): D_[i] (word P (m+1) x)=∑ j:Fin (m+1),Chill K i (x j) • word P m (x∘j.succAbove) := by
    induction m with
    | zero => rw [word_cons, trace_part, word_zero, evaporate (G:=G),Fin.sum_univ_one]; simp only [map_zero, add_zero]; rfl
    | succ m ih=>
        rw [word_cons,trace_part, Fin.sum_univ_succ, ih, show (0:Fin (m+1+1)).succAbove=Fin.succ from funext Fin.zero_succAbove,map_sum]; congr 1; apply Finset.sum_congr rfl; intro j _; rw [map_smul, word_cons P (x ∘ (j.succ).succAbove)]; congr 3; simp [Function.comp_def]
lemma evaluate_word (m:ℕ)(f:Fin m→ V): W (word P m f)=gaussian he (Law.product (ρ ∘ f) univ) := by
    induction m using Nat.strong_induction_on with
    | _ m ih=>
      cases m with
      | zero=>
        rw [word_zero,minView, show Law.product (ρ ∘ f) univ= (1:Dir G n→ℝ) from funext fun i=> Finset.prod_empty]; unfold gaussian; rw [(Φ).empty,Complex.ofReal_one]
      | succ m =>
        let g := f ∘ Fin.succ; let L := f 0
        have hz : W (word P (m+1) f)= View K (D_[L] (word P m g)):= by
            rw [word_cons, ibpV (f 0) (witness he).1 (witness he).2 (word_symm _ m g) (minH (rank_limit (word_rank _ m g))), trdΩ]; simp_rw [map_sum,map_smul]; rfl
        have hv : Law.product (ρ ∘ f) univ=fun x=> Law.product (ρ ∘ g) univ x*ρ L x:= by funext i; unfold Law.product; rw [Fin.prod_univ_succ,mul_comm]; rfl
        rw [hz,hv,show gaussian he (fun x=> Law.product (ρ ∘ g) univ x*ρ L x)= ∑ i:Fin m, gaussian he (Law.product (ρ ∘ g) (univ.erase i))* (Φ).wick (ρ L) (ρ (g i)) from (Φ).recursion ν _ (ρ ∘ g) univ ]
        cases m with
        | zero=> change W (D_[L] (coin 1))=_; rw [evaporate]; simp
        | succ m=>
          rw [ trace_word he L m, map_sum, Complex.ofReal_sum]; apply Finset.sum_congr rfl; intro i _; rw [map_smul, ih m (by omega) _, smul_eq_mul,letter_payment ]; push_cast; rw [mul_comm]; congr 2 -- product
          congr 1; funext u; unfold Law.product; simp_rw [Fin.univ_succAbove (n:=m) i, erase_cons, Finset.prod_map ]; rfl

-- submodule packaging to avoid assigning a fake linear integral map outside its domain
private def density (F:Raw V ℂ)(x:Dir G n) := value z[x] F * ((Φ).kern x:ℂ) -- he implicit via hygiene
private def mass (G:Gauge) (e:Even n.val) : ℝ:= ∫ x:Dir G n, (saddle e).kern x ∂ PertExtension.Chart.tangent G _
def readsAt (F: Raw V ℂ) : Prop := Integrable (density he F) ν ∧ W F = (∫ x:Dir G n, density he F x ∂ν) / mass G he
lemma paysWord (m:ℕ) (f:Fin m→ V) : readsAt he (word P m f) := by
    let F:= Law.product (ρ ∘ f) univ
    have h (x:Dir G n): density he (word P m f) x=( (F x*(Φ).kern x:ℝ):ℂ):= by rw [density,word_value _ (tied x), ← Complex.ofReal_prod,← Complex.ofReal_mul]; rfl
    refine ⟨ (funext h) ▸ ?_, ?_⟩ -- rewrite backwards
    · exact ((Φ).integrable_entry ν (Law.product_bound _ _) (Law.product_cont _ _)).ofReal
    rw [evaluate_word he]; simp_rw [h]; rw [integral_complex_ofReal]; unfold gaussian Law.average mass; push_cast; rfl
private lemma expects (F H:Raw V ℂ): density he (F+H)=density he F+density he H:= by ext x; change value _ (F+H) * _=value _ F*_+ value _ H*_; rw [map_add,add_mul]
private lemma scalars (c:ℂ)(F:Raw V ℂ): density he (c • F)= c • density he F := by funext x; change value _ _ * _=c * (value _ _ * _); rw [map_smul,smul_eq_mul,mul_assoc]
private def Reads : Submodule ℂ (Raw V ℂ) where
    carrier := readsAt (G:=G) he
    zero_mem' := by
        have h : density (G:=G) he 0=0:= by funext x; simp [density]
        change readsAt he (0:Raw V ℂ); unfold readsAt; rw [h]; simp
    add_mem' {F H} hx hy:= by
        rcases hx with ⟨hf,h⟩; rcases hy with ⟨hk,hh⟩; change readsAt he _; unfold readsAt; rw [expects]; refine ⟨hf.add hk, ?_⟩; simp_rw [Pi.add_apply]; rw [integral_add hf hk,map_add,h, hh, add_div]
    smul_mem' c F he':= by
        rcases he' with ⟨hf,h⟩; change readsAt he _; unfold readsAt; rw [scalars]; refine ⟨ hf.smul _,?_⟩; simp_rw [Pi.smul_apply]; rw [integral_smul, map_smul,h,smul_eq_mul,smul_eq_mul,mul_div_assoc]
lemma evaluated {F:Raw V ℂ}(h:F∈ FeeP P): readsAt he F:= by
    obtain ⟨hx,k,h⟩:= fee_spec h; change F∈ Reads he; rw [limit_eq_rankSum _ h]; exact (Reads he).sum_mem fun i hi=> combination P (Reads he) i (fun f:Fin i→V=>paysWord he i f) (rankMod F i) (mask_symm hx)
lemma true_mean {F: Raw V ℂ}(h:F∈ FeeP P){A:Dir G n→ℝ}(heq:∀ x:Dir G n,value z[x] F=(A x:ℂ)): W F=gaussian he A:= by
    rw [(evaluated he h).2]; unfold density; simp_rw [heq,← Complex.ofReal_mul, integral_complex_ofReal, gaussian, Law.average, mass ]; push_cast; rfl
end YM.WilsonBridge.Based.Position
