import YM.MSbar.Pole.Symbol.Bind
/-! Mark dependence after one pairing including transverse Lorentz trace. -/
noncomputable section
set_option autoImplicit false
namespace YM.MSbar.Pole.Symbol.Chain
open Function Set Filter MeasureTheory Momentum Ambient Age Mellin place
open scoped Topology ContDiff BigOperators Classical InnerProductSpace
variable {I : Type} [Fintype I] {n : ℕ} {p q i a b:I}
private lemma horiz {x:External I n} (ha:i≠a)(hb:i≠b) (w v r : place n):
    joint a b (update x i w) v r=update (joint a b x v r) i w := by unfold joint; rw [update_comm hb,update_comm ha] -- which
private lemma forwards (x:External I n) (u:place n)(i:I): place.pad n ∘ update x i u=update (place.pad n∘x) i (place.pad n u):=by
  ext1 j; by_cases he:j=i; subst j; simp; simp [he]

lemma uses {K P:Finset I} {H:Cloud I} (h : Shape K P H) (Z:Chain I) (p:I) (hp:p∉P) (w:ℂ):
    Shape ((insert p (K \ Z.reads))) (P \ Z.reads) (term p w H Z) := by
  cases Z with
  | scalar => simp only [reads,Finset.sdiff_empty,term]; exact ⟨fun n x y ho=> h.sees n x y (fun i hi=> ho i (Finset.mem_insert_of_mem hi)), h.angle⟩
  | query i =>
    constructor
    · intro n x y hl; change H n _= H n _
      apply h.sees; intro j hj; by_cases he:j=i
      · subst j; simp only [update_self]; rw [hl p (by simp)]
      simp only [update_of_ne he]; rw [hl j (Finset.mem_insert_of_mem (by simp [hj,reads,he]))]
    intro j hj n x; obtain ⟨ha,hb⟩:=Finset.mem_sdiff.mp hj
    have he:j≠i:= by simpa [reads] using hb
    have hy:p≠j:=fun t=>hp (t.symm ▸ ha)
    unfold term
    simp_rw [update_of_ne hy, update_comm he]; exact h.angle j ha ..
  | pair i j =>
    have hf n x y (hx:∀ l∈insert p (K \ (pair i j).reads), (x:External I n) l=y l) u v:
        H n (joint i j x u v)=H n (joint i j y u v) := by
      apply h.sees; intro l hl; by_cases h₁:l=i; subst l; simp only [joint,update_self];
      by_cases h₂:l=j; subst l; simp only [joint,update_of_ne h₁,update_self];
      simp only [joint, update_of_ne h₁, update_of_ne h₂]; exact hx _ (Finset.mem_insert_of_mem <| Finset.mem_sdiff.mpr ⟨hl,by simp [reads,h₁,h₂]⟩)
    constructor
    · intro n x y hx; simp only [term,stroke,horizontal,vertical]; rw [hf (n+1) (place.pad n ∘ x) (place.pad n ∘ y) (fun l hl=> congr_arg (place.pad n) (hx l hl))]; congr 1
      exact Finset.sum_congr rfl fun k _=>hf n x y hx _ _
    intro l hl n x; obtain ⟨h₀,h₁⟩:= Finset.mem_sdiff.mp hl
    have hx:l≠i∧l≠j:=by simpa [reads] using h₁
    have hv : Along (fun t=>vertical i j H (update x l t)) := by
      unfold vertical; simp_rw [forwards, horiz hx.1 hx.2]; let Z(v):=update (joint i j (place.pad n ∘ x) (place.room n 1) (place.room n 1)) l (place.pad n v)
      have hb := h.angle l h₀ (n+1) (joint i j (place.pad n ∘ x) (place.room n 1) (place.room n 1)); let L:= hb.lift.comp (place.pad n).toLinearMap
      exact ⟨map_add L,map_smul L⟩
    refine Along.plus (h:=show Along (fun t=>horizontal i j H (update x l t)) from ?_) (p:=hv.scale _)
    exact Along.sum (F:= -- args
       fun m : Fin (2*n) => fun t => H n (joint i j (update x l t) (ortho n m) (ortho n m))) Finset.univ fun m _=> by
        simp_rw [horiz hx.1 hx.2]; exact h.angle l h₀ n _

lemma tips {F:Cloud I} (Z:Chain I) (p:I) (w:ℂ) (A:Finset I) (d:Age)(z:ℂ) (hp:p∈A) (h:Disjoint Z.reads A)
    (he : ∀ i∈Z.reads,Tone F i) (x:External I n) {r:ℝ} (hr:0<r) :
    (r:ℂ)^d.alpha z * term p w F Z n (move A r x) = (r:ℂ)^Z.demand * term p w (roll A d r (fun _=>F) z) Z n x:= by
  let c := (r:ℂ)^d.alpha z
  have hm {i:I} {m:ℕ} {x:External I m} (hi:i∈Z.reads) (v) : move A r (update x i v)=update (move A r x) i v:= by
    ext1 m; by_cases hz:m=i
    · subst m; simp only [move,if_neg (show i∉A from fun hk=>Finset.disjoint_left.1 h hi hk),update_self]
    by_cases hy:m∈A <;> simp [move,hz,hy]
  cases Z with
  | scalar=> simp [term,demand,roll]
  | query i =>
    have hi:i∈(query i).reads:=by simp [reads]
    have hh:move A r x p= r • x p := by simp [move,hp]
    simp only [term,demand,roll]; rw [hh]; change c*_= (r:ℂ)^1*(c*F n (move A r _))
    rw [hm hi]; rw [show F n _ = r • F n (update (move A r x) i (x p)) from (he i hi n (move A r x)).smul r (x p),Complex.real_smul]; ring
  | pair i j=>
    have hx:i∈ (pair i j).reads:=by simp [reads]
    have hy:j∈(pair i j).reads:=by simp [reads]
    simp only [term,stroke,horizontal,vertical,roll,demand,pow_zero,one_mul]; simp_rw [joint,hm hx,hm hy]; rw [← Finset.mul_sum, move_pad]; ring
end YM.MSbar.Pole.Symbol.Chain
