import YM.WilsonCoeffUV.Thermo.Prediction
import YM.WilsonCoeffUV.Thermo.Cover
/-!
# Joint cotangents packed. Eager, fluctuation vars z on all fine links. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Bank
open Filter Function Matrix Lattice Wilson RG Laurent Bloch Exterior Metric Blue FreeResolvent Work.F08 Precision
open Stationary
open scoped ContDiff Topology BigOperators
variable {L n f:Side} {U α β V ι : Type*}{k r l j:ℕ}

-- rectangular assembly blocks.
def pierL {X α β:Type*} (x:X×α): X×(α⊕β):=(x.1,.inl x.2)
def pierR {X α β:Type*} (x:X×β): X×(α⊕β):=(x.1,.inr x.2)
def upper (A:ropes U α α)(B:ropes U α β): ropes U α (α⊕β):= fun i j=> Sum.elim (fun b=>A i (j.1,b)) (fun b=>B i (j.1,b)) j.2
def stair (A:ropes U α ι)(B:ropes U β ι): ropes U (α⊕β) ι:= fun i j=> Sum.elim (fun b=>A (i.1,b) j) (fun b=> B (i.1,b) j) i.2
lemma chairL (A:ropes U α ι)(B:ropes U β ι) (i): stair A B (pierL i)=A i:=rfl
lemma chairR (A:ropes U α ι)(B:ropes U β ι)(i): stair A B (pierR i)= B i:=rfl
lemma handL (A:ropes U α α)(B:ropes U α β)(i j) : upper A B i (pierL j)= A i j:= rfl
lemma handR (A:ropes U α α)(B:ropes U α β)(i j) : upper A B i (pierR j)= B i j:=rfl
lemma upper_cap {A : ropes U α α}{B:ropes U α β}{s x y}{d:Distance U}(e:dragCup d s x A)(h:dragCup d s y B): dragCup d s (max x y) (upper A B):=by
  refine ⟨e.1.trans (le_max_left ..), ?_⟩; rintro i ⟨u,b|b⟩; exact (e.le (le_max_left x y)).2 i (u,b); exact (h.le (le_max_right x y)).2 i (u,b)
lemma strafe {A : ropes U α ι}{B:ropes U β ι}{s x y}{d:Distance U}(e:dragCup d s x A)(h:dragCup d s y B): dragCup d s (max x y) (stair A B):=by
  refine ⟨e.1.trans (le_max_left ..), ?_⟩; rintro ⟨u,b|b⟩ j; exact (e.le (le_max_left x y)).2 (u,b) j; exact (h.le (le_max_right x y)).2 (u,b) j

section floats
variable {G:Gauge}
lemma Pilots.silent : Pilots (fun _=> 0 : (n:Side) → ropes (Site n) α β) 0:= ⟨fun _ _=>tendsto_const_nhds,Eventually.of_forall fun _ _ _ _=>rfl,1,0,one_pos, Eventually.of_forall fun _=>dragCup.zero⟩
lemma Pilots.deck {P:(n:Side)→ ropes (Site n) α α}{Q:(n:Side)→ ropes (Site n) α β}{A:ropes Cover α α}{B:ropes Cover α β}(h:Pilots P A)(e:Pilots Q B): Pilots (fun n=> upper (P n) (Q n)) (upper A B):=by
  obtain ⟨s,x,hp,H⟩:=h.fees; obtain ⟨t,y,hq,J⟩:=e.fees
  refine ⟨?_,?_,min s t,max x y,lt_min hp hq,(H.and J).mono fun n ⟨hv,hf⟩=>upper_cap (hv.mono (min_le_left ..)) (hf.mono (min_le_right ..))⟩
  · rintro i ⟨j,v|v⟩; exact h.point i (j,v); exact e.point i (j,v)
  filter_upwards [h.move,e.move] with n hn hr; rintro b i ⟨j,v|v⟩; exact hn b i (j,v); exact hr b i (j,v)
lemma Pilots.deck' {P:(n:Side)→ ropes (Site n) α ι}{Q:(n:Side)→ ropes (Site n) β ι}{A:ropes Cover α ι}{B:ropes Cover β ι}(h:Pilots P A)(e:Pilots Q B): Pilots (fun n=> stair (P n) (Q n)) (stair A B):=by
  obtain ⟨s,x,hp,H⟩:=h.fees; obtain ⟨t,y,hq,J⟩:=e.fees
  refine ⟨?_,?_,min s t,max x y,lt_min hp hq,(H.and J).mono fun n ⟨hv,hf⟩=>strafe (hv.mono (min_le_left ..)) (hf.mono (min_le_right ..))⟩
  · rintro ⟨j,v|v⟩ i; exact h.point (j,v) i; exact e.point (j,v) i
  filter_upwards [h.move,e.move] with n hn hr; rintro b ⟨j,v|v⟩ i; exact hn b (j,v) i; exact hr b (j,v) i

-- right invariant rail from identity, use origin equality

def ladder [DecidableEq U][DecidableEq β] : ropes U β (α⊕β):= fun i j=> Sum.elim (fun _=> 0) (fun b=> (1:ropes U β β) i (j.1,b)) j.2
lemma ladder_amber [DecidableEq U][DecidableEq β]{d:Distance U}{σ}: dragCup d σ 1 (ladder:ropes U β (α⊕β)) := by
  refine ⟨zero_le_one,?_⟩; rintro i ⟨j,b|b⟩
  · change |(0:ℝ)| ≤ _; rw [abs_zero]; positivity
  exact dragCup.one.2 i (j,b)
lemma ladder_fold [DecidableEq β]: Pilots (fun n:Side=> ladder (U:=Site n) (α:=α) (β:=β)) ladder:= by
  let h:Pilots (fun n=> (1:ropes (Site n) β β)) 1:= Pilots.one
  refine ⟨?_,?_,1,1,one_pos,Eventually.of_forall fun _=> ladder_amber⟩
  · rintro i ⟨j,k|k⟩; exact tendsto_const_nhds; exact h.point i (j,k)
  filter_upwards [h.move] with n hn; rintro x i ⟨j,k|k⟩; rfl; exact hn x i (j,k)

-- reduced slots directly: read R(B,0) no graph.
def scoop (F:Ten V (U×(α⊕β)) r): Ten V (U×β) r:= fun i=> F (pierR ∘ i)
def sluice (F: Gen V (U×(α⊕β))): Gen V (U×β) := fun r=> scoop (F r)
variable [NormedAddCommGroup V]
lemma scrapC {F: Ten V (U×(α⊕β)) r}{D:Distance U}{s A}(h:Amber D s A F): Amber D s A (scoop F):=⟨h.1,fun x=> h.2 (pierR ∘ x)⟩
lemma scoopY [NormedSpace ℝ V]{P:raw (α⊕β) V r}{Q}(h:Yields P Q): Yields (fun n=> scoop (P n)) (scoop Q):=by
  have he n: dilute (fun n=> scoop (P n)) n=scoop (dilute P n):=by by_cases hv:r=0 <;> simp only [dilute,hv,↓reduceIte]; rfl
  obtain ⟨s,a,hp,H⟩:=h.fees; refine ⟨fun x=>?_, h.strolls.mono (fun n hn b x=>hn b (pierR ∘ x)),s,a,hp,H.mono fun n hn=> by rw [he n]; exact scrapC hn⟩
  simp_rw [he]; exact h.point (pierR ∘ x)

-- concrete cross completers
variable (g:Ratio n f)
local notation "I"=> (weaveFine g G)
local notation "T"=> (weaveH g G)

lemma cam_chart (M:Matrix (Woods G f) (Woods G n) ℝ): allotM I T (camber G M) = upper 1 (allotM I (Equiv.refl _) M) := by
  classical
  apply Matrix.ext
  intro i j; obtain ⟨u,rfl⟩ := (T).surjective j
  cases u with
  | inl u=>
    simp only [allotM,Matrix.submatrix_apply,Equiv.symm_apply_apply]; rw [show T _=pierL (I u) from rfl, handL, Matrix.one_apply]
    rw [camber,Matrix.add_apply,Matrix.mul_apply]; unfold rightFlag leftFlag; simp only [Matrix.of_apply,reduceCtorEq,↓reduceIte, mul_zero,Finset.sum_const_zero,add_zero, Sum.inl.injEq];
    split_ifs with h H H<;> first| rfl | simp_all
  | inr u=>
    simp only [allotM,Matrix.submatrix_apply,Equiv.symm_apply_apply]; rw [show T _=pierR u from rfl,handR]
    rw [camber]; simp [leftFlag,rightFlag,Matrix.mul_apply]
lemma ground_chart (M:Matrix (Woods G f) (Woods G n) ℝ){K: Matrix (Co n (Larvae G g.count)) (Woods G n) ℝ}: allotM I (Equiv.refl _) M=K →
     allotM T T (groundM G M)=stair (upper 1 K) ladder := by
    intro hk; subst K; apply Matrix.ext; intro i j
    obtain ⟨u,rfl⟩:= (T).surjective i; obtain ⟨v,rfl⟩:= (T).surjective j
    simp only [allotM,Matrix.submatrix_apply, Equiv.symm_apply_apply]; cases u with
    | inl u=>
      rw [show T _=pierL (I u) from rfl,chairL]; cases v with
      | inl v=> rw [show T _=pierL (I v) from rfl,handL]; simp only [Matrix.one_apply, (I).injective.eq_iff]; exact Matrix.one_apply ..
      | inr v=> rw [show T _=pierR v from rfl,handR]; rw [Matrix.submatrix_apply,Equiv.symm_apply_apply]; rfl
    | inr u=> cases v <;> rfl

lemma lamp_chart (M:Matrix (Woods G f) (Woods G f) ℝ): allotM T T (fillSlots (Woods G n) M)=stair (upper (allotM I I M) 0) 0 := by
    apply Matrix.ext; intro i j; obtain ⟨u,rfl⟩:= (T).surjective i; obtain ⟨v,rfl⟩:= (T).surjective j
    simp only [allotM, Matrix.submatrix_apply,Equiv.symm_apply_apply]; cases u with
    | inl u=> cases v with
              | inl v=> rw [show T _=pierL (I u) from rfl, show T _=pierL (I v) from rfl,chairL,handL, Matrix.submatrix_apply,Equiv.symm_apply_apply,Equiv.symm_apply_apply]; rfl
              | inr v=>rfl
    | inr u=>cases v <;> rfl
lemma into_shade [NormedSpace ℝ V] (P:Gen V (Joint G f n)): fade plug P= sluice (bend T P):=by
    ext i v; rw [fade_plug]; congr 1
end floats
end YM.WilsonCoeffUV.Bank
