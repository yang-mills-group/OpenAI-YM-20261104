import YM.MS.Wind.Unique
/-!
# The LPT orbit seeds and all coefficients (not just Taylor jets)

Length ODE chooses uniquely within explicit capacity. Positions flow also uses
 these on unmarked/single mark cover, independent of finite IR. Mark input already
 arbitrary radius per label/order. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Wind
open Function Filter Set Finset Plane Koszul Flux MeasureTheory
open Landau Native Lattice Tone Momentum Heat Real Frame Wire Color Detect Native.Wilsonian Paint
open Book Convolve City Logarithm Program
open Complex (I)
open scoped Topology ContDiff
variable {G: Gauge}{p:Team}{φ: Actor G}{F H: Dec G}{u:ℤ}

-- one extra loop lines orientation first unmarked. use packed function arith.
def path (c:ℝ)(n k:ℕ)(F H:Dec G): Pack G:= c • ∑ i∈Domain.paths n k, (fun x:ℝ=> treeP G (F (n-i) x) (H i x))
lemma path_c (c:ℝ)(n k:ℕ)(F H:Dec G){b:Bool}(h:∀ i∈Domain.paths n k,Fees true 0 (F (n-i)))(he:∀ i∈Domain.paths n k,Fees b u (H i)): Fees b u (path c n k F H):= Fees.fare (Fees.sum _ (fun i hi=> by simpa only [zero_add] using busyPack (h i hi) (he i hi))) c
lemma path_eq (c:ℝ)(n k:ℕ){F H Q W:Dec G}(h:∀ i∈Domain.paths n k,F (n-i)=H (n-i))(he:∀ i∈Domain.paths n k, Q i=W i): path c n k F Q=path c n k H W:=by unfold path; congr 1; apply Finset.sum_congr rfl; intro i hi; rw [h i hi,he i hi]
lemma path_in {i n r:ℕ}(h: i∈Domain.paths n r): r ≤ i ∧ i<n := Finset.mem_Ico.mp h

-- exists all stencil orders. generic sequential choices proof.
theorem diagonal_pick {V:Type}[Inhabited V]{D: ℕ→ (ℕ→ V) → V → Prop } (h: ∀ i f g, (∀ j < i,f j=g j) → ∀ v,D i f v → D i g v) (H:∀ n f,∃ v,D n f v) : ∃ f, ∀ n,D n f (f n):= by
    classical
    choose T ht using H; let f := fun i=> Nat.strongRecOn i (motive:=fun _=>V) (fun i H=> T i (fun j=> if h : j < i then H j h else default)); refine ⟨f,fun i=>?_⟩; nth_rw 1 [show f i=T i (fun j=>if _h:j < i then f j else default) from ?_]; swap; · unfold f; rw [Nat.strongRecOn_eq]
    exact h i (fun j=> if _h : j < i then f j else default) f (fun j hj=>dif_pos hj) _ (ht i _)

structure PC (G:Gauge)(p:Team)(F:Dec G): Prop where
   owes (n): Fees true 0 (F n)
   free : F 0=0
   recu (n) (H:0<n)(x:ℝ): Sat (run (style G p x n)) (F n x) (path (1/2) n 1 F F x)
-- structure includes zero. param affects table λ y.
structure PM (φ:Actor G)(F H:Dec G)(v:ℤ): Prop where
   owes n : Fees false v (H n)
   recu n (x:ℝ): Sat (run (φ x n)) (H n x) (path 1 n 0 F H x)
private abbrev E0 (b:Bool)(G: Gauge)(q:ℤ) := {p:Pack G // Fees b q p}
private instance (b:Bool)(G:Gauge)(q:ℤ): Inhabited (E0 b G q):= ⟨⟨0,Fees.zero q G⟩⟩
theorem space_H (G : Gauge)(p:Team): ∃ F: Dec G,PC G p F:= by
    let V := E0 true G 0; let T (u:ℕ→V):Dec G:=fun i=> (u i).val; let W n v (V:E0 true G 0): Prop:= if n=0 then V.val=0 else ∀ x:ℝ, Sat (run (style G p x n)) (V.val x) (path (1/2) n 1 (T v) (T v) x)
    suffices he: ∃ F,∀ n,W n F (F n) by
        obtain ⟨F,hF⟩:= he; refine ⟨T F,fun n=>(F n).property,?_,?_⟩; simpa [W,T] using hF 0; intro i hi x; have hx:=hF i; unfold W at hx; rw [if_neg (Nat.ne_of_gt hi)] at hx; exact hx x
    refine diagonal_pick (D:=W) ?_ (fun i f=>?_)
    · intro i f g h v; unfold W; split; exact fun x=>x; have he j (hj : j∈Domain.paths i 1): T f j=T g j:= congr_arg Subtype.val (h j (path_in hj).2)
      have hz j (hj:j∈Domain.paths i 1): i-j < i:= by have he:=path_in hj; omega
      rw [path_eq (1/2) i 1 (F:=T f) (H:=T g) (fun j hj=> congr_arg (·.val) (h (i-j) (hz j hj))) he] -- infer
      exact fun x=>x
    unfold W; by_cases hh:i=0; simp_rw [if_pos hh]; exact ⟨default,rfl⟩; simp_rw [if_neg hh]; obtain ⟨F,hd,hb⟩:= Sats (openOrigin _ i (core_circle G p)) (path_c (1/2) i 1 (T f) (T f) (fun j _=> (f _).property) (fun j _=> (f _).property)); exact ⟨⟨F,hd⟩,hb⟩
theorem member (h:PC G p F)(hH:Circle G φ false u): ∃ K:Dec G, PM φ F K u:= by
    let V:=E0 false G u; let T(v:ℕ→V):Dec G:=fun i=>(v i).val; let W n v (X:E0 false G u): Prop:= ∀ x:ℝ, Sat (run (φ x n)) (X.val x) (path 1 n 0 F (T v) x)
    suffices he:∃ f,∀ n, W n f (f n) by obtain ⟨f,hf⟩:= he; exact ⟨T f,fun n=> (f n).property,hf⟩
    refine diagonal_pick (D:=W) (fun i f g H v h=>?_) (fun i f=>?_); swap; · obtain ⟨F,hd,hb⟩:= Sats (openOrigin _ i hH) (path_c 1 i 0 F (T f) (fun j _=>h.owes _) (fun j _=>(f _).property)); exact ⟨⟨F,hd⟩,hb⟩
    intro x; rw [← path_eq 1 i 0 (F:=F) (fun _ _=>rfl) (Q:=T f) (W:=T g) (fun j hj=> congr_arg (·.val) (H j (path_in hj).2))]; exact h x
end YM.MS.Wind
