import YM.FormalBulk08.Roof.Mirror

/-! Field temporal expenses. `p` includes arbitrary profiles (and origin
within-preimages, as needed). `b` buys decay and readable covector norm.
NO Fk inference here. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Quire
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Dawn Grail Palm Wine Rial Aster Roof
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {X I : Type*}{Y U: X→Type*}{r m:ℕ}(τ:Time X)(R:∀ x, Reach (Y x))(o:∀ x,U x→Y x)(η δ:X→ℝ)(b:∀ x,U x→ℝ)
-- o dependent incl closure anchor; pp

def Bear (T:∀ x:X,U x→Tile (Y x) r):Prop:= ∃ C:X→ℝ,Soft τ C ∧ (∀ i,0≤C i) ∧ ∀ i p, Knoxville (R i) (η i) (o i p) (T i p) (C i*b i p)
variable {S T:∀ x:X,U x→Tile (Y x) r}
structure Matched (T S: ∀ x:X,U x→Tile (Y x) r) :Prop where
   left : Bear τ R o η b T
   right : Bear τ R o η b S
   chalk : Bear τ R o η (fun i p=> δ i*b i p) (fun i p=>T i p-S i p)
variable {τ R o η δ b}
lemma bear_void (τ:Time X)(R:∀ x,Reach (Y x))(o: ∀ x, U x→Y x) (η)(b)(r): Bear τ R o η b (fun i _=>(0:Tile (Y i) r)):= by refine ⟨_,soft_coin τ 0,fun _=>le_rfl,fun i p=>?_⟩;rw [zero_mul];exact Knox_zeros _
lemma mates_void (τ:Time X)(R:∀ x,Reach (Y x))(o: ∀ x,U x→ Y x)(η δ)(b)(r:ℕ): Matched τ R o η δ b (fun i _=>(0:Tile (Y i) r)) (fun _ _=>0):=⟨bear_void ..,bear_void ..,by simp_rw [sub_self];exact bear_void ..⟩
lemma Matched.constant (h: Bear τ R o η b T): Matched τ R o η δ b T T:= ⟨h,h,by simp_rw [sub_self];exact bear_void ..⟩
lemma Bear.below {c:∀ x,U x→ℝ}(h:Bear τ R o η b T)(he:∀ i j,b i j ≤ c i j): Bear τ R o η c T:= by
    obtain ⟨C,hp,P,H⟩:=h; exact ⟨_,hp,P,fun i j=>(H i j).mono (mul_le_mul_of_nonneg_left (he _ _) (P i))⟩
lemma Bear.plus (h: Bear τ R o η b T)(e:Bear τ R o η b S): Bear τ R o η b (fun i p=> T i p+S i p):= by
    obtain ⟨C,h,P,H⟩:=h; obtain ⟨A,u,W,Z⟩:=e; refine ⟨_,h.plus u, fun i=> add_nonneg (P i) (W i),fun i p=>?_⟩; rw [add_mul]; exact (H i p).add (Z i p)
variable {f g:X→ℝ}
lemma Bear.amp (h: Bear τ R o η b T)(hp:Soft τ f): Bear τ R o η b (fun i p=> f i • T i p):= by
    obtain ⟨C,h,P,H⟩:=h; refine ⟨_,hp.radius.times h,fun i=>mul_nonneg (abs_nonneg _) (P i),fun i p=>?_⟩; rw [mul_assoc]; exact (H i p).smul _
lemma Bear.minus (h:Bear τ R o η b T)(ht: Bear τ R o η b S): Bear τ R o η b (fun i p=> T i p-S i p):= by simp_rw [sub_eq_add_neg];exact h.plus (by simpa only [neg_one_smul] using ht.amp (soft_coin τ (-1)))
lemma Bear.pay (h: Bear τ R o η b T)(hp: Faint τ δ f): Bear τ R o η (fun i p=>δ i*b i p) (fun i p=>f i • T i p):= by
    obtain ⟨C,h,P,H⟩:=h; obtain ⟨A,hA,Q,L⟩:=hp; refine ⟨_,hA.times h,fun i=>mul_nonneg (Q i) (P i),fun i p=>?_⟩; exact ((H i p).smul _).mono ((mul_le_mul_of_nonneg_right (L i) (H i p).1).trans_eq (by ring))
lemma Bear.lengthen (h:Bear τ R o η b T)(he:r=m) : Bear τ R o η b (fun i p=>lengthen he (T i p)):= by subst r; exact h
lemma Bear.polish (h:Bear τ R o η b T) : Bear τ R o η b (fun i p=> sand (T i p)):= by obtain ⟨C,h,P,H⟩:= h; exact ⟨_,h,P,fun i p=> (H i p).polish⟩

variable {T' S': ∀ x:X,U x→Tile (Y x) r}
lemma Matched.plus (h: Matched τ R o η δ b T S)(e:Matched τ R o η δ b T' S'): Matched τ R o η δ b (fun i p=>T i p+T' i p) (fun i p=> S i p+S' i p):= by
   refine ⟨h.left.plus e.left,h.right.plus e.right,?_⟩; convert h.chalk.plus e.chalk using 1; ext1 i;ext p v; simp only [Pi.add_apply,Pi.sub_apply]; ring
lemma Matched.amp (h: Matched τ R o η δ b T S)(e:Pact τ δ f g): Matched τ R o η δ b (fun i p=>f i • T i p) (fun i p=>g i • S i p):= by
   refine ⟨h.left.amp e.left,h.right.amp e.right,?_⟩; convert ((h.chalk.amp e.left).plus (h.right.pay e.blur)) using 1; ext1 i;ext1 p; rw [smul_sub,Pi.sub_apply,sub_smul]; abel
lemma Matched.lengthen (h: Matched τ R o η δ b T S)(he:r=m): Matched τ R o η δ b (fun i p=> lengthen he (T i p)) (fun i p=> lengthen he (S i p)):= by subst r; exact h
lemma Matched.polish (h: Matched τ R o η δ b T S): Matched τ R o η δ b (fun i p=>sand (T i p)) (fun i p=>sand (S i p)):= by
    refine ⟨h.left.polish,h.right.polish,?_⟩; convert h.chalk.polish using 1;ext i p v;simp [sand, Finset.sum_sub_distrib,sub_div]
lemma matched_sums (P: Finset I){T S:I→∀ x:X,U x→ Tile (Y x) r}(h:∀ i∈P, Matched τ R o η δ b (T i) (S i)): Matched τ R o η δ b (fun i p=>∑ j∈P,T j i p) (fun i p=>∑ j∈P,S j i p):= by
   induction P using Finset.induction with
   | empty=>simp only [Finset.sum_empty];apply mates_void
   | @insert i P he ih=>simp_rw [Finset.sum_insert he]; exact (h i (Finset.mem_insert_self ..)).plus (ih fun j hj=> h j (Finset.mem_insert_of_mem hj))
lemma bear_sums (P: Finset I){T:I→∀ x:X,U x→Tile (Y x) r}(h:∀ i∈P,Bear τ R o η b (T i)): Bear τ R o η b (fun i p=>∑ j∈P,T j i p):= (matched_sums (δ:= η) P (fun i hi=>Matched.constant (h i hi))).left
lemma v_sum_high {J: X→Type*}[∀ i,Fintype (J i)]{o:∀ i, U i→Y i} (h: Soft τ (fun i=>(Fintype.card (J i):ℝ))) {T:∀ x:X,U x × J x→Tile (Y x) r} (e:Bear τ R (U:= fun i:X=>U i × J i) (fun i p=>o i p.1) η (fun i p=>b i p.1) T): Bear τ R o η b (fun i p=>∑ j:J i,T i (p,j)):= by
    obtain ⟨C,hc,P,H⟩:=e
    let c(i:X):= (Fintype.card (J i):ℝ)*C i
    refine ⟨c,h.times hc,fun i=>mul_nonneg (Nat.cast_nonneg (Fintype.card (J i))) (P i),fun i p=>?_⟩
    let T'(j:J i):=T i (p,j)
    have he (j:J i): Knoxville (R i) (η i) (o i p) (T' j) (C i*b i p):= H i (p,j)
    have hW : Knoxville (R i) (η i) (o i p) (∑ j:J i,T' j) (∑ _:J i, C i*b i p):=knox_sum Finset.univ (K:=fun _=>C i*b i p) (fun j _=>he j)
    rw [Finset.sum_const,nsmul_eq_mul,Finset.card_univ,←mul_assoc] at hW
    exact hW
lemma m_sum_high {J : X→Type*}[∀ i,Fintype (J i)]{o:∀ i,U i→Y i}(h:Soft τ (fun i=>(Fintype.card (J i):ℝ))){T S:∀ x:X,U x× J x→Tile (Y x) r} (e:Matched τ R (U:=fun i:X=>U i× J i) (fun i p=>o i p.1) η δ (fun i p=>b i p.1) T S) : Matched τ R o η δ b (fun i p=>∑ j:J i,T i (p,j)) (fun i p=>∑ j:J i,S i (p,j)):= by
    refine ⟨v_sum_high (o:=o) (T:=T) (b:=b) h e.left,v_sum_high (o:=o) (T:=S) (b:=b) h e.right,?_⟩; have hv:= v_sum_high (o:=o) (T:=fun i p=>T i p-S i p) (b:=fun i p=>δ i*b i p) h e.chalk; simp_rw [Finset.sum_sub_distrib] at hv; exact hv

end YM.FormalBulk08.Quire
