import YM.RG02.Degree.Link
import YM.RG02.Wick.Program

/-!
Degree after extraction. Connected log on fields already gaussian-normalized.
**Not** a degree truncation of the actual correlation. Polynomial costs are
on the formal implementation inputs relative to one standard Gaussian; even
tag covariance changes with same constant normalizer aren't automatically
bounded by these (use first symmetry/branch independence).
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG02.Shear
open Finset Marker Multi Extra.Trajectories Marks Grade Filter Function MeasureTheory
open Next.Rank Next.Rank.Normal Wick PertExtension GaussianScore PowerSeries
open scoped BigOperators

variable {X E I:Type}[NormedAddCommGroup X][NormedSpace ℝ X][NormedAddCommGroup E][NormedSpace ℝ E]
variable {A : Type}[DecidableEq I][Fintype I]{T : Census I}
variable [FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E]

omit [MeasurableSpace E][BorelSpace E] in
private lemma same_script (Γ:Law E)(f:E→Script T) : script dot (E:=fun _=>E) (fun _=>Γ) (fun _=>f)= made Γ fun y=> Grade.exponential (f y) := by
   ext i s
   rw [script,mix_part];
   have h (a : ℂ) : dot (fun _=>a)=a := by rw [show (fun _:Dot=>a) = a • 1 by funext p; simp,map_smul,choose_dot.1];simp
   exact h _

variable (μ : Measure E) [μ.HasTemperateGrowth][μ.IsAddRightInvariant][NeZero μ]
include μ

omit μ [MeasurableSpace E][BorelSpace E] [Fintype I] in
private lemma compressed {k : Multi.Hot T→ℕ} {K : ℕ}{n: Multi.Hot T→ℕ} (s : T.Mode)
    (G:X→Poly T) (v:(i:Multi.Hot T)→Fin (n i)→Vertex X E)(h : ∀ i j,(v i j).Counts (k i))
    (hk : ∀ p∈shards T s,tax p k≤K)(Γ:Law E)
    (hv : ∀ x,G x=substitute T (connected (stellar dot (fun _=> coloring Γ (id (α:=Module.Dual ℝ E))) (fun i _=>∑ j:Fin (n i),(v i j).cost x)))) : Payment K fun x=> (G x).part s := by
   simp_rw [hv,Multi.substituted]
   apply Payment.plane (shards T s) (fun p x=> _) (fun p hi=> ?_)
   exact (others _ v p k (fun i _ j=>h i j)).raise (hk p hi)

theorem driverTax (f : X → E → Script T) (Γ : Law E)(he : ∀ x,Edged (f x))(hp : ∀ x u,basepoint (f x u)=0)
    (r : ℕ)(k : Multi.Hot (mixed r T)→ℕ)(S : (mixed r T).Mode)
    (H : ∀ i, Rolls (k i) (fun p : X×E=> (Grade.encode r (f p.1 p.2)).part i.val))
    (K : ℕ)(hK : ∀ p∈shards (mixed r T) S,tax p k≤K) :
    Payment K fun x=> (Grade.encode r (Grade.logarithm (made Γ (fun y=> Grade.exponential (f x y))))).part S := by
   choose n v hv hV using H
   let G (x:X)(i : Multi.Hot (mixed r T)) (_:Dot):= ∑ j:Fin (n i),(v i j).cost x
   let s: Module.Dual ℝ E → Module.Dual ℝ E:= id
   have hg x : models (E:=fun _=>E) r (fun _=> s) (fun _=> f x) (G x) := by
      rintro u i; funext e
      have heq := congr_arg (fun f : X×E→ℂ=> f (x,e)) (hv i)
      simp only [Finset.sum_apply] at heq
      rw [heq]; unfold G Wick.paint; simp only [map_sum]; rfl
   have hh (x:X) : Grade.encode r (Grade.logarithm (made Γ (fun y=> Grade.exponential (f x y)))) = substitute (mixed r T) (connected (stellar dot (fun _=> coloring Γ s) (G x))) := by
      rw [← same_script Γ (f x)]
      exact program_log (fun _=> μ) choose_dot.1 (fun _=>he x) (fun _=>hp x) r _ (hg x)
   exact compressed S (fun x=> Grade.encode r (Grade.logarithm (made Γ (fun y=> Grade.exponential (f x y))))) v hV hK Γ hh

omit μ [Fintype I] in
lemma minimum_copies (n : ℕ)(t : T.Mode) : ∃ p : (mixed n T).Mode, (Pair.fst p).val.card=n ∧ Pair.snd p=t :=
   let P : (Marks.full (Fin n)).Mode:= ⟨univ,by unfold Marks.full; simp⟩
   ⟨Marks.Pair.mk P t,by rw [Pair.fst_mk]; dsimp only [P]; simp,Pair.snd_mk ..⟩

def vertexRate (r : ℕ)(m : ℕ)(p : Multi.Hot (mixed r T)) : ℕ :=
    (Pair.fst p.val).val.card + (if Pair.snd p.val=T.quiet then 2 else m)

omit μ [Fintype I] in
private lemma counts {J : Type}[DecidableEq J]{B:Census J}(p : (together B T).Mode)(s : (parts (together B T)).Mode)(hs : s∈shards (together B T) p) :
    ∑ i∈s.val,(Pair.fst i.val).val.card=(Pair.fst p).val.card := by
    have hi (b : (together B T).Mode) (i : J) : i ∈ (Pair.fst b).val↔ Sum.inl i∈ b.val:= by simp [Pair.fst]
    have hu : s.val.biUnion Multi.Hot.sites=p.val := congr_arg Subtype.val ((Multi.chooses ..).mp hs)
    have he : s.val.biUnion (fun x=>(Pair.fst x.val).val)=(Pair.fst p).val := by
       ext1 i; rw [Finset.mem_biUnion,hi,← hu, Finset.mem_biUnion]; exact exists_congr fun k=> and_congr Iff.rfl (hi ..)
    rw [← he,Finset.card_biUnion];
    intro i hv j hj hh
    exact disjoint_left.mpr fun k hk h => disjoint_left.mp (parts_wise s hv hj hh) ((hi ..).mp hk) ((hi ..).mp h)

-- `tax` useful even for all-empty p or k; marked top consumes k+h
omit μ [Fintype I] in
lemma tax_pair {J : Type}[DecidableEq J]{B:Census J}(p : (together B T).Mode)(s : (parts (together B T)).Mode)(hs : s∈shards (together B T) p) (m : ℕ) :
    tax s (fun i=> (Pair.fst i.val).val.card + (if Pair.snd i.val=T.quiet then 2 else m)) ≤ (Pair.fst p).val.card+
       if Pair.snd p=T.quiet then 2 else m*((Pair.snd p).val.card) := by
   
   unfold tax; rw [sum_add_distrib, counts p s hs]
   let Hot := fun i : Multi.Hot (together B T) => Pair.snd i.val ≠ T.quiet
   let x:= s.val.filter Hot
   let y:= s.val.filter fun i=>¬ Hot i
   let d:= x.card
   have hu : s.val.biUnion Multi.Hot.sites=p.val := congr_arg Subtype.val ((Multi.chooses ..).mp hs)
   have hi (b : (together B T).Mode) (i:I) : i∈(Pair.snd b).val ↔ Sum.inr i∈ b.val := by simp [Pair.snd]
   have he : x.biUnion (fun i => (Pair.snd i.val).val)=(Pair.snd p).val := by
      ext1 i; rw [Finset.mem_biUnion,hi, ← hu, Finset.mem_biUnion]; constructor
      · rintro ⟨j,hj,h⟩; exact ⟨j,(Finset.mem_filter.mp hj).1,(hi j.val i).mp h⟩
      rintro ⟨j,hj,h⟩; have h := (hi ..).mpr h
      exact ⟨j, Finset.mem_filter.mpr ⟨hj,fun H=> notMem_empty _ (H ▸ h)⟩,h⟩
   have hv : d ≤ (Pair.snd p).val.card := by
      unfold d; rw [← he,Finset.card_biUnion,Finset.card_eq_sum_ones]
      · refine sum_le_sum fun i hi=> ?_; refine Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr ?_)
        exact fun H=> (Finset.mem_filter.mp hi).2 (Subtype.ext H)
      intro i ha j hb hj
      exact disjoint_left.mpr fun k hk h => disjoint_left.mp (parts_wise s (mem_filter.mp ha).1 (mem_filter.mp hb).1 hj) ((hi ..).mp hk) ((hi ..).mp h)
   have hm : (∑ i∈s.val,(if Pair.snd i.val=T.quiet then 2 else m)) = d*m+y.card*2 := by
      let F (i:Multi.Hot (together B T)):= if Pair.snd i.val=T.quiet then 2 else m
      rw [← Finset.sum_filter_add_sum_filter_not s.val Hot F]
      have he' : ∑ i∈x,F i=d*m := by
         unfold d
         rw [← smul_eq_mul,← Finset.sum_const]
         exact sum_congr rfl fun j hj => if_neg (mem_filter.mp hj).2
      change _ + _ = _
      rw [he']
      have hf : ∑ i∈y,F i=y.card*2 := by
         rw [← smul_eq_mul,← Finset.sum_const]
         exact sum_congr rfl fun j hj => if_pos (Classical.not_not.mp (mem_filter.mp hj).2)
      rw [hf]
   have HD : d+y.card=s.val.card := Finset.card_filter_add_card_filter_not ..
   rw [hm]
   split
   next hb => rw [hb] at hv; change d ≤ 0 at hv; rw [Nat.eq_zero_of_le_zero hv,zero_mul]; omega
   next hh =>
      have hh : 0<d := by
         have hl := Finset.nonempty_iff_ne_empty.mpr (show (Pair.snd p).val≠∅ from fun h=> hh (Subtype.ext h))
         rw [← he] at hl
         refine Nat.pos_of_ne_zero fun hj => Finset.not_nonempty_iff_eq_empty.mpr ?_ hl
         rw [Finset.card_eq_zero.mp hj, Finset.biUnion_empty]
      have hv:= Nat.mul_le_mul_left m hv; rw [mul_comm m d] at hv; omega

set_option maxHeartbeats 600000 in
omit μ in
lemma tax_rate (r : ℕ)(p : (mixed r T).Mode)(s : (parts (mixed r T)).Mode)(hs : s∈shards (mixed r T) p) (m : ℕ) :
    tax s (vertexRate r m) ≤ (Pair.fst p).val.card+
       if Pair.snd p=T.quiet then 2 else m*((Pair.snd p).val.card) := by
   have _ := (inferInstance : Fintype I)
   exact tax_pair (I:=I) (J:=Fin r) (T:=T) (B:=Marks.full (Fin r)) p s hs m

set_option maxHeartbeats 600000 in
theorem budgets (f : X → E → Script T)(Γ : Law E)(he : ∀ x,Edged (f x))(hp : ∀ x u,basepoint (f x u)=0)
    (r : ℕ)(m : ℕ)(H : ∀ i, Rolls (vertexRate r m i) (fun x : X×E=> (Grade.encode r (f x.1 x.2)).part i.val)) (s : T.Mode) :
    Payment (r + if s=T.quiet then 2 else m*s.val.card) (fun x=> (PowerSeries.coeff r (Grade.logarithm (made Γ (fun y=> Grade.exponential (f x y))))).part s) := by
   obtain ⟨p,ha,hj⟩ := minimum_copies r s
   have h i (hi : i∈ shards (mixed r T) p) : tax i (vertexRate r m) ≤ r+if s=T.quiet then 2 else m*s.val.card:= by
      have H := show tax i (vertexRate r m) ≤ (Pair.fst p).val.card + if Pair.snd p=T.quiet then 2 else m*(Pair.snd p).val.card from tax_pair (I:=I) (J:=Fin r) (T:=T) (B:=Marks.full (Fin r)) p i hi m
      rwa [ha,hj] at H
   have hh := driverTax μ f Γ he hp r (vertexRate r m) p H _ h
   convert! hh.scale (r.factorial:ℂ)⁻¹ using 1
   funext x; rw [Pi.smul_apply]
   simp only [smul_eq_mul,Grade.encode_part,ha,hj,inv_mul_cancel_left₀ (show (r.factorial:ℂ) ≠0 from by exact_mod_cast (Nat.factorial_ne_zero r))]
end YM.RG02.Shear
