import YM.Pert.Triangle.Incidence
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 310000
noncomputable section
namespace YM.Pert.Triangle.Receipt
open Maxwell Wick Function Set Classical Topology Finset Next.Rank.Normal
variable {G:Gauge} {J:Type} [Fintype J] (loc:J→Fin 3) (g:J→ℕ) (x:Points 3) (hx:x∈conf 3)
variable (L : (j:J)→Probe G (g j)) (j:J)
def neighbors := ∏k∈(Finset.univ.filter (fun t=>loc t=loc j)).erase j, symbol (g k) (L k)
lemma block_change (v : Probe G (g j)) : block loc g (update L j v) = update (block loc g L) (loc j) (neighbors loc g L j * symbol (g j) v) := by
  funext q; by_cases h :loc j=q
  · subst q
    let s := Finset.univ.filter (fun i=>loc i=loc j)
    let f i := symbol (g i) (update L j v i)
    unfold block; rw [update_self]
    change s.prod f = _
    rw [←Finset.mul_prod_erase s f (show j∈s from Finset.mem_filter.mpr ⟨Finset.mem_univ j,rfl⟩), show f j=symbol (g j) v from congrArg (symbol (g j)) (update_self ..),mul_comm]
    congr 1
    exact Finset.prod_congr rfl (fun i hi=> congrArg (symbol (g i)) (update_of_ne (Finset.mem_erase.mp hi).1 v L))
  rw [update_of_ne (Ne.symm h)]
  unfold block
  exact Finset.prod_congr rfl (fun i hi=> congrArg (symbol (g i)) (update_of_ne (fun t : i=j=>h (t ▸ (Finset.mem_filter.mp hi).2)) v L))
def drawMap : Probe G (g j) →ₗ[ℝ] ℂ :=
  (((Wick.moment G x).toLinearMap (block loc g L) (loc j)).restrictScalars ℝ) ∘ₗ (LinearMap.mulLeft ℂ (neighbors loc g L j) |>.restrictScalars ℝ) ∘ₗ lineAt g j
lemma draw_eval (v : Probe G (g j)) : drawMap loc g x L j v=draw loc g (update L j v) x := by rw [draw,block_change];rfl

variable (P:Equiv.Perm J) (hp:P∈register loc univ)
def seeds := univ.filter (fun u=>loc u<loc (P u))
lemma is_seed (q) : q∈seeds loc P ↔ loc q<loc (P q) := mem_filter.trans (and_iff_right (mem_univ _))
include hp
lemma partition : P j ∈ seeds loc P ↔ j∉seeds loc P := by
   obtain ⟨_,h1,h2,_⟩:=mem_filter.mp hp
   rw [is_seed, is_seed,not_lt]
   rw [show P (P j)=j from congrArg (fun P:Equiv.Perm J=>P j) h1]
   exact ⟨fun h=>h.le,fun h=>lt_of_le_of_ne h (h2 j (mem_univ _))⟩

def partnerWindow : J := if j∈seeds loc P then j else P j
lemma window_self : partnerWindow loc j P∈seeds loc P := by
  unfold partnerWindow; by_cases he : j∈seeds loc P <;> simp [he,partition loc j P hp] 
omit hp
lemma orientation_edge : (partnerWindow loc j P=j ∧ j∈seeds loc P) ∨ (partnerWindow loc j P=P j ∧ j∉seeds loc P) := by
  by_cases he : j∈seeds loc P
  · exact Or.inl ⟨if_pos he,he⟩
  exact Or.inr ⟨if_neg he,he⟩
def edgeTerm (k:J) : ℂ := ↑(legKernel (L k) (L (P k)) (x (loc k)-x (loc (P k))))
include hp
lemma fix_ribs (v) {k} (hk:k ∈(seeds loc P).erase (partnerWindow loc j P)) :
    edgeTerm loc g x (update L j v) P k=edgeTerm loc g x L P k := by
  obtain ⟨_,h1,h2,_⟩:=mem_filter.mp hp
  have hj := Finset.mem_erase.mp hk
  have he : k≠j := fun t=> Or.elim (orientation_edge loc j P) (fun h=>hj.1 (t.trans h.1.symm)) (fun u=>u.2 (t ▸ hj.2))
  have he' : P k≠j := by
     intro h
     rcases orientation_edge loc j P with ⟨ht,hw⟩|⟨ht,-⟩
     · subst j
       exact (partition loc k P hp).1 hw (hj.2)
     · exact hj.1 ((congrArg (fun P:Equiv.Perm J=>P k) h1).symm.trans (by change P (P k)=_ ;rw [h,← ht]))
  unfold edgeTerm; rw [update_of_ne he,update_of_ne he']

include hx
lemma fundamental : ∃ M : Probe G (g j) →ₗ[ℝ]ℂ, ∀ v, edgeTerm loc g x (update L j v) P (partnerWindow loc j P)=M v := by
  let q := P j
  let t := x (loc j) - x (loc q)
  have h := Finset.mem_filter.mp hp |>.2.2.1 j (Finset.mem_univ j)
  have he : q≠j := fun e=> h (congrArg _ e)
  have ht : t≠0 := sub_ne_zero.mpr (hx.ne h.symm) -- hx def conf
  have turn : P q=j := calls loc (Finset.mem_filter.mp hp).2 j
  rcases orientation_edge loc j P with ⟨hj,-⟩|⟨hj,-⟩
  · rw [hj]
    refine ⟨Complex.ofRealLI.toLinearMap ∘ₗ (pairing (G:=G) (l:=g q) (j:=g j) (show t∈away from ht)).flip (L q),fun v=>?_⟩
    rw [edgeTerm,update_self,show P j=q from rfl, update_of_ne he]; rfl
  rw [hj]
  refine ⟨Complex.ofRealLI.toLinearMap ∘ₗ (pairing (G:=G) (l:=g j) (j:=g q) (show -t∈away from neg_ne_zero.mpr ht)) (L q), fun v=>?_⟩
  rw [edgeTerm,show P j=q from rfl,turn,update_self,update_of_ne he]
  dsimp; rw [show x _-x _ = -t from (neg_sub ..).symm]; rfl

lemma tourLinear : ∃ M : Probe G (g j) →ₗ[ℝ]ℂ, ∀ v, M v=tours loc g (update L j v) x P := by
   obtain ⟨M,hm⟩ := fundamental loc g x hx L j P hp
   refine ⟨ (LinearMap.toSpanSingleton ℂ ℂ (∏k∈(seeds loc P).erase (partnerWindow loc j P), edgeTerm loc g x L P k) |>.restrictScalars ℝ) ∘ₗ M, fun v=>?_⟩
   change (M v • _ : ℂ) = ∏ i∈seeds loc P,edgeTerm loc g x (update L j v) P i
   rw [← Finset.mul_prod_erase _ (fun k=>edgeTerm loc g x (update L j v) P k) (window_self loc j P hp), hm v, Finset.prod_congr rfl (fun k hk=>fix_ribs loc g x L j P hp v hk)]
   rfl
omit hp
lemma toursLinear : ∃ M : Probe G (g j) →ₗ[ℝ]ℂ, ∀ v, M v=sumTours loc g (update L j v) x := by
  have h := fun R hR=>tourLinear loc g x hx L j R hR
  classical
  let M : Equiv.Perm J → Probe G (g j) →ₗ[ℝ]ℂ := fun R=> if hr:R∈register loc univ then (h R hr).choose else 0
  refine ⟨∑ R∈register loc univ,M R,fun v=>(LinearMap.sum_apply ..).trans ?_⟩
  unfold sumTours
  apply Finset.sum_congr rfl; intro k hk; dsimp only [M]; rw [dif_pos hk]; exact (h k hk).choose_spec v
end YM.Pert.Triangle.Receipt
