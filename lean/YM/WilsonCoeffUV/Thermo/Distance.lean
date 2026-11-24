import YM.WilsonCoeffUV.Step.Source
import YM.Push.FREE_RESOLVENT.Torus
/-!
# Period meshes and true-diameter currencies

In this interface ranks fixed finite; winding convergence at FIXED geography.
Raw ranks zero are extensive; normalize/divide for cover transfer individually.
Widths used in Yields are existence at this gear/history only; power-counting
prices are separate on TRUE distances and-before/after block fixed as documented
at endpoints. Schur or rooted Laurent conversions shrink by fixed demand only.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Bank
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent
open scoped Topology BigOperators
variable {n:Side}{U α β V ι : Type*}{k r:ℕ} {A B σ η : ℝ}

abbrev Cloth (α:Type*) := Cover×α
-- position equivalence

def jog [AddGroup U] (u:U) : U×α ≃ U×α := (Equiv.addLeft u).prodCongr (Equiv.refl _)
def foldUnder (n:Side) (x:Cloth α) : Co n α:= (wrap n x.1,x.2)
lemma fold_move (n:Side) (x:Cover)(p:Cloth α) : foldUnder n (jog x p)=jog (wrap n x) (foldUnder n p) := Prod.ext (map_add _ _ _) rfl

lemma lift_ready (z:Cover) : ∀ᶠ n : Side in atTop, lift (wrap n z)=z:= by
  let R : Side:=⟨2*size z+1, Nat.zero_lt_succ _⟩
  filter_upwards [eventually_ge_atTop R] with n hn; exact size_centers n z le_rfl hn
lemma fold_faith (p q:Cloth α) : ∀ᶠ n : Side in atTop, foldUnder n p=foldUnder n q ↔ p=q:= by
  filter_upwards [lift_ready p.1,lift_ready q.1] with n hn he
  refine ⟨fun h=>Prod.ext ?_ (show (foldUnder n p).2= (foldUnder n q).2 from congr_arg Prod.snd h),congr_arg _⟩
  rw [← hn,← he]; exact congr_arg lift (congr_arg Prod.fst h)

-- use ℕ lengths
structure Distance (U:Type*) where
  gap : U→U→ℕ
  self x : gap x x=0
  swap x y : gap x y=gap y x
  tri a b c : gap a c ≤ gap a b + gap b c

def tor (n:Side) : Distance (Site n) where
  gap x y:=size (lift (y-x))
  self x:= by simp [size,lift]
  swap x y:= by have h := (taxi n).comm x y; simp only [taxi] at h; exact_mod_cast h
  tri a b c:= by have h := (taxi n).triangle a b c; simp only [taxi] at h; exact_mod_cast h

def terrain : Distance Cover where
  gap x y:=size (y-x)
  self x:= by simp [size]
  swap x y:= by rw [← size_neg (y-x),neg_sub]
  tri x y z:= by rw [show z-x=(y-x)+(z-y) by abel]; exact size_add ..

lemma now_gap (x y:Cover): ∀ᶠ n:Side in atTop,(tor n).gap (wrap n x) (wrap n y)=terrain.gap x y:=by
  filter_upwards [lift_ready (y-x)] with n hn
  simp only [map_sub] at hn; change size (lift (wrap n y-wrap n x))=size (y-x); rw [hn]

-- unrooted max pair. no intrinsic reorder.
def league [Fintype ι] (d:Distance U) (x:ι→U): ℕ:= Finset.univ.sup fun i=> Finset.univ.sup fun j=>d.gap (x i) (x j)
lemma leg_le [Fintype ι] (d:Distance U) (x:ι→U)(i j): d.gap (x i) (x j)≤league d x:= le_trans (Finset.le_sup (f:=fun j=>d.gap (x i) (x j)) (Finset.mem_univ j)) (Finset.le_sup (f:=fun i=>Finset.univ.sup (fun j=>d.gap (x i) (x j))) (Finset.mem_univ i))
lemma league_le [Fintype ι] (d:Distance U)(x:ι→U){m:ℕ}(h:∀ i j,d.gap (x i) (x j)≤m): league d x≤m:= Finset.sup_le fun i _=>Finset.sup_le fun j _=> h i j
lemma league_comp [Fintype α] [Fintype β](d:Distance U)(x:α→U)(f:β→α): league d (x ∘ f)≤league d x:=league_le d _ fun i j=>leg_le d x (f i) (f j)
lemma league_equiv [Fintype α] [Fintype β](d:Distance U)(x:α→U)(f:β ≃ α): league d (x ∘ f)=league d x:= le_antisymm (league_comp ..) (by simpa only [comp_assoc,Equiv.self_comp_symm, Function.comp_id] using league_comp d (x ∘ f) f.symm)

abbrev soar {U α : Type*}{ι:Type*}[Fintype ι](d:Distance U)(x:ι→U×α) := league d (Prod.fst ∘ x)
abbrev course {U α β I J:Type*} [Fintype I][Fintype J](d:Distance U)(x:I→U×α)(y:J→U×β) := league d (Sum.elim (Prod.fst ∘ x) (Prod.fst ∘ y))
lemma touched [Fintype ι] (x:ι→Cloth α): ∀ᶠ n:Side in atTop,soar (tor n) (foldUnder n ∘ x)=soar terrain x:=by
  have h i: ∀ᶠ n:Side in atTop,∀ j:ι,(tor n).gap (wrap n (x i).1) (wrap n (x j).1)=terrain.gap (x i).1 (x j).1:= eventually_all.mpr fun j=>now_gap _ _
  filter_upwards [eventually_all.mpr h] with n hn
  refine le_antisymm (league_le _ _ fun i j=>?_ ) (league_le _ _ fun i j=>?_)
  · exact (hn i j).le.trans (leg_le terrain (Prod.fst ∘ x) _ _)
  exact (hn i j).ge.trans (leg_le (tor n) (Prod.fst ∘ foldUnder n ∘ x) _ _)

/- width point currency; monotone; count from single roots later. -/
variable {d:Distance U}

def stroll [AddGroup U] (F:Ten V (U×α) r): Prop:= ∀ b:U,∀ x,F (jog b ∘ x)=F x
variable [NormedAddCommGroup V]

def Amber (d: Distance U)(σ A:ℝ)(F:Ten V (U×α) r): Prop:= 0≤A ∧ ∀ x,‖F x‖ ≤ A * Real.exp (-σ * soar d x)
variable {F H:Ten V (U×α) r}
lemma Amber.le (a:Amber d σ A F)(b:A≤B): Amber d σ B F:= ⟨a.1.trans b,fun x=>(a.2 x).trans (mul_le_mul_of_nonneg_right b (by positivity))⟩
lemma Amber.mono (a:Amber d σ A F)(h:η≤σ):Amber d η A F:=⟨a.1,fun x=>(a.2 x).trans (mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right (neg_le_neg h) (by positivity))) a.1)⟩
lemma Amber.add (a:Amber d σ A F)(b:Amber d σ B H):Amber d σ (A+B) (F+H):=⟨add_nonneg a.1 b.1,fun x=>(norm_add_le ..).trans ((add_le_add (a.2 x) (b.2 x)).trans_eq (by rw [add_mul]))⟩
lemma Amber.neg (a:Amber d σ A F):Amber d σ A (-F):= ⟨a.1,fun x=> by rw [Pi.neg_apply,norm_neg]; exact a.2 x⟩
lemma Amber.sub (a:Amber d σ A F)(b:Amber d σ B H):Amber d σ (A+B) (F-H):= by rw [sub_eq_add_neg]; exact a.add b.neg
lemma Amber.zero : Amber d σ 0 (0:Ten V (U×α) r):=by simp [Amber]
lemma Amber.sum (s:Finset ι){P:ι→Ten V (U×α) r}{M:ι→ℝ}(h:∀ i∈s,Amber d σ (M i) (P i)): Amber d σ (∑ i∈s,M i) (∑ i∈s,P i):= by
  classical
  induction s using Finset.induction_on with
  | empty=> simp only [Finset.sum_empty]; exact Amber.zero
  | @insert i s he H=> rw [Finset.sum_insert he,Finset.sum_insert he]; exact (h i (Finset.mem_insert_self ..)).add (H fun j hj=>h j (Finset.mem_insert_of_mem hj))

/-- X,Y raw HIGH kernels converge on wraps (scalar divided by sites). -/
abbrev raw (α V:Type*)(r:ℕ):= (n:Side)→ Ten V (Co n α) r
variable [NormedSpace ℝ V]
def dilute {r}(P:raw α V r)(n:Side) : Ten V (Co n α) r := if r=0 then (Fintype.card (Site n):ℝ)⁻¹ • P n else P n
structure Yields (P:raw α V r) (Q:Ten V (Cloth α) r) : Prop where
  point : ∀ x,Tendsto (fun n=> dilute P n (foldUnder n ∘ x)) atTop (𝓝 (Q x))
  strolls : ∀ᶠ n in atTop, stroll (P n)
  fees : ∃ σ A:ℝ,0<σ ∧ ∀ᶠ n in atTop, Amber (tor n) σ A (dilute P n)

lemma Amber.smul (a:Amber d σ A F)(c:ℝ): Amber d σ (|c| *A) (c•F):= ⟨mul_nonneg (abs_nonneg _) a.1,fun x=> by rw [Pi.smul_apply,norm_smul, Real.norm_eq_abs,mul_assoc]; exact mul_le_mul_of_nonneg_left (a.2 x) (abs_nonneg _)⟩
variable {P X:raw α V r}{Q Q': Ten V (Cloth α) r}
lemma Yields.unique (h:Yields P Q)(g:Yields P Q'): Q=Q':=funext fun x=> tendsto_nhds_unique (h.point x) (g.point x)
lemma Yields.cover (h:Yields P Q):∃ σ A:ℝ,0<σ ∧ Amber terrain σ A Q:=by
  obtain ⟨s,a,he,H⟩:=h.fees
  obtain ⟨w,hw⟩:=H.exists
  refine ⟨s,a,he,hw.1,fun x=>le_of_tendsto (h.point x).norm ?_⟩
  filter_upwards [touched x,H] with n hn hp
  rw [← hn]; exact hp.2 _
lemma Yields.road (h:Yields P Q) : stroll Q:=by
  intro b x; refine tendsto_nhds_unique (h.point (jog b ∘ x)) ((h.point x).congr' ?_)
  filter_upwards [h.strolls] with n hn
  have he : foldUnder n ∘ (jog b ∘ x)=jog (wrap n b) ∘ (foldUnder n ∘ x) := funext fun i=>fold_move n b (x i)
  change dilute P n _ = dilute P n _; rw [he]; by_cases ha:r=0 <;> simp [dilute,ha,hn _ _]
lemma Yields.congr (h:Yields P Q)(he:∀ᶠ n in atTop, P n=X n):Yields X Q:= by
  obtain ⟨s,a,hp,H⟩ :=h.fees
  refine ⟨fun x=>(h.point x).congr' ?_,he.mp (h.strolls.mono fun n hn hh=>hh ▸ hn), s,a,hp,?_⟩
  · filter_upwards [he] with n hn
    simp only [dilute,hn]
  filter_upwards [he,H] with n hn hx; simp_rw [dilute,hn] at hx; exact hx
lemma dilute_add (P X:raw α V r)(n:Side):dilute (P+X) n=dilute P n+dilute X n:= by by_cases h:r=0<;>simp [dilute,h,smul_add]
lemma Yields.add (h:Yields P Q)(g:Yields X Q'): Yields (P+X) (Q+Q'):=by
  obtain ⟨s,a,hp,H⟩ :=h.fees; obtain ⟨t,b,ht,J⟩:=g.fees
  refine ⟨fun x=>?_, ?_,min s t, a+b,lt_min hp ht,?_⟩
  · simp_rw [dilute_add,Pi.add_apply]; exact (h.point x).add (g.point x)
  · filter_upwards [h.strolls,g.strolls] with n hn hv
    intro b x; simp only [Pi.add_apply]; rw [hn b x,hv b x]
  filter_upwards [H,J] with n hn hv; rw [dilute_add]; exact (hn.mono (min_le_left ..)).add (hv.mono (min_le_right ..))
lemma dilute_smul (P:raw α V r)(b:ℝ)(n:Side): dilute (b•P) n=b•dilute P n:= by
  by_cases h:r=0
  · rw [dilute,dilute,if_pos h,if_pos h,Pi.smul_apply,smul_comm]
  simp [dilute,h]
lemma Yields.smul (h:Yields P Q)(b:ℝ): Yields (b•P) (b•Q):= by
  obtain ⟨s,a,hp,H⟩:=h.fees
  refine ⟨fun x=>?_, ?_,s,|b| *a,hp,H.mono (fun n hn=>by rw [dilute_smul]; exact hn.smul b)⟩
  · simp_rw [dilute_smul,Pi.smul_apply]; exact tendsto_const_nhds.smul (h.point x)
  filter_upwards [h.strolls] with n hn; intro b x; simp only [Pi.smul_apply]; rw [hn b x]
lemma Yields.neg (h:Yields P Q): Yields (-P) (-Q):= by simpa only [neg_one_smul] using h.smul (-1)
lemma Yields.sub (h:Yields P Q)(g:Yields X Q'): Yields (P-X) (Q-Q'):=by simpa only [sub_eq_add_neg] using h.add g.neg
lemma Yields.zero : Yields (0:raw α V r) 0:=by
  have h n : dilute (0:raw α V r) n=0:=by by_cases h:r=0 <;> simp [dilute,h]
  refine ⟨fun x=>?_,Eventually.of_forall fun _ _ _=>rfl,1,0,one_pos, Eventually.of_forall fun n=>by rw [h]; exact Amber.zero⟩
  simp_rw [h,Pi.zero_apply]; exact tendsto_const_nhds
lemma Yields.sum (s:Finset ι){P:ι→ raw α V r}{F:ι→Ten V (Cloth α) r}(h:∀ i∈s,Yields (P i) (F i)): Yields (∑ i∈s,P i) (∑ i∈s,F i):=by
  classical
  induction s using Finset.induction_on with
  | empty=> simp only [Finset.sum_empty]; exact Yields.zero
  | @insert i s he H=> rw [Finset.sum_insert he,Finset.sum_insert he]; exact (h i (Finset.mem_insert_self ..)).add (H fun j hj=>h j (Finset.mem_insert_of_mem hj))
lemma Yields.sym (h:Yields P Q)(e:∀ᶠ n in atTop, Smooth (P n)): Smooth Q:= by
  intro q x
  refine tendsto_nhds_unique (h.point (x ∘ q)) ((h.point x).congr' ?_)
  filter_upwards [e] with n hn
  change dilute P n (foldUnder n ∘ x)= dilute P n ((foldUnder n ∘ x) ∘ q)
  apply Eq.symm; apply (show Smooth (dilute P n) from ?_) q
  unfold dilute; split; exact hn.smul _
  exact hn
end YM.WilsonCoeffUV.Bank
