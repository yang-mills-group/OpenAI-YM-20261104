import YM.FormalOPE.RG10.Profile.Press
/-! # Exact finite unit identity with **finite** (not integral) marginal. Includes vacuum. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Profile
open Function Maxwell Labels Extraction Filter Finset Extra.FD PertExtension MeasureTheory
    Topology Metric PertExtension.Position PertExtension.Physical PowerSeries Triangle
    InversionTop LatticePT Lattice Grid FlatFeed RG10.Position
open scoped Topology BigOperators ContDiff Classical
variable {G:Gauge}{F:Frames G}{n d:ℕ}(P : Plan F)(q:ℕ+)(m:ℕ)
local notation "T" => offsets q
local notation "ε" => epsilon q m
local notation "σ" => Grid.sample q m

lemma routine {I F:Type*}[Fintype I][AddCommMonoid F](W:(Fin (n+1)→I)→ F):
    ∑ x,W x=∑ y:Fin n→ I,∑ i:I, W (Fin.cons i y) := by
 let e:(I×(Fin n→ I))≃ (Fin (n+1)→I) := ⟨fun p=>Fin.cons p.1 p.2,fun q=>(q 0,Fin.tail q),fun _=>by simp,fun _=>by simp⟩
 rw [← Equiv.sum_comp e,Fintype.sum_prod_type]; exact sum_comm

private lemma summed {I F:Type*}[Fintype I][AddCommMonoid F](f:I→F):
    ∑ i:Fin 1→ I,f (i 0) = ∑ i,f i := by
 let e : (Fin 1→I) ≃ I := ⟨fun p=>p 0,fun q _=> q,fun _=>funext (fun i=>by simp [Subsingleton.elim i 0]),fun _=>rfl⟩
 exact Equiv.sum_comp e f

variable (t:Test (n+1)) (u: Fin n→ Deck F d)
lemma begun : P.begins q m d (task t (Fin.cons (Deck.start F d) u)) = P.begins q m d (task (takings t q m) u) := by
 ext i : 1
 rw [bill,bill]; -- instance
 rw [routine]; apply sum_congr rfl; intro k _
 have he (i: Native q m) : σ (Fin.cons i k)=Points.cons (point q m i) (σ k):= by
   ext1 p; refine Fin.cases ?_ (fun i=> ?_) p <;> simp [Grid.sample_eq,Points.cons]
 simp_rw [he,singular,Fin.tail_cons, takings_at]
 rw [summed (fun i:Native q m=> t (Points.cons (point q m i) (σ k)))]
 simp_rw [Complex.real_smul,Complex.re_ofReal_mul,Complex.re_sum,mul_sum,sum_mul]
 apply sum_congr rfl; intro s _; ring

lemma without {Z:Type*}[Fintype Z](Y: Mark Z PertExtension.Physical.Profile.n →fps) (u:Test n)(A:FrameAt Z fps)(w:Fin n→ Z)(z₀:Z) (hh:∀ z,A z₀ z= if z=z₀ then 1 else 0)
   (he:∀ v:Fin n→ Z, Y (task t (Fin.cons z₀ v))= Y (task u v)):
    PertExtension.Position.insert Z _ Y A (task t (Fin.cons z₀ w))= PertExtension.Position.insert Z _ Y A (task u w) := by
 let B (n:ℕ)(u: Fin n→ Z)(v:Fin n→ Z):= ∏ i, A (u i) (v i)
 change ∑ v:Fin (n+1)→Z, Y (task t v)* B _ (Fin.cons z₀ w) v= ∑ v:Fin n→ Z,Y (task u v)* B _ w v
 rw [routine]; apply sum_congr rfl; intro i _;
 unfold B; simp_rw [Fin.prod_univ_succ, Fin.cons_zero,Fin.cons_succ,hh]
 rw [sum_eq_single_of_mem z₀ (mem_univ _) ]
 · rw [if_pos rfl,one_mul,he]
 intro j _ hj; simp [hj]

lemma begins_empty (t: Test 0) (u: Fin 0→Deck F d) : P.begins q m d (task t u)= C (t 0).re := by
 ext i:1; rw [bill]; simp_rw [dark, Subsingleton.elim (α:= Points 0) (σ _) 0]; cases i <;> simp

lemma empty {Z:Type*}[Fintype Z](Y: Mark Z PertExtension.Physical.Profile.n →fps)(t:Test 0)(A:FrameAt Z fps)(u:Fin 0→ Z):
    PertExtension.Position.insert Z _ Y A (task t u)= Y (task t u):= by
 change ∑ v:Fin 0→ Z,Y (task t v)* (∏ i,A (u i) (v i))=_; simp [Subsingleton.elim u default]

lemma collect_vac (t: Test 0) (u: Fin 0→Deck F d) : Plan.collect F P q m d (task t u) = C (t 0).re := by rw [Plan.collect,show P.dressed q m d (task t u)= P.begins q m d (task t u) from empty _ t (P.poses q m d) _,begins_empty,Peal.action_on,subst_C]; rfl

lemma collect_unit (h: Official P.stock) : Plan.collect F P q m d (task t (Fin.cons (Deck.start F d) u)) = Plan.collect F P q m d (task (takings t q m) u) := by
 have hh (z) : P.poses q m d (Deck.start F d) z = if z=Deck.start F d then 1 else 0:= by
    ext i:1; obtain ⟨a,ha,hb,hc⟩:= Plan.state h q m d i; have he:=congr_fun₂ hc (Deck.start F d) z
    split <;> rename_i hx <;> cases i <;> simpa [Physical.diag, hx, eq_comm, hb] using he
 exact congr_arg (Peal.Xaction F (P.dressed q m 6)) (show P.dressed q m d _ = P.dressed q m d _ from without t (P.begins q m d) _ (P.poses q m d) u _ (fun z=> by convert! hh z using 1; congr! 1) (fun w=> begun P q m t w))
end YM.FormalOPE.RG10.Profile
