import YM.FormalOPE.RG10.Horizon.Logs

/-!
# Mixed-label insertions in continuum arrays after frame conversion

A real-labeled branch. Includes actual reading at *one* height, then real horizon promotion with
zeros, never setting unrelated fields equal. No cost uniform in the arity. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalOPE.RG10.Panel
open Position Position.Grade Apertures Function Finset Maxwell Labels Extraction Filter Extra.FD
open PertExtension MeasureTheory Topology Metric Matrix PertExtension.Position PertExtension.Physical Triangle
open scoped Topology BigOperators ContDiff Classical
open PowerSeries
variable {G:Gauge}{F:Frames G}{R:Rails F} {P:Plan F}{Y:Drivers}{Z:Patience P Y}
variable {A B : Type*}[Fintype A][Fintype B]{n:ℕ}

section rows
variable {g:A→B}(hp:Injective g)

def Keep (g : A→B) (v:A→fps)(w:B→fps) : Prop:= (∀ i, w (g i)=v i) ∧ ∀ j∉Set.range g,w j=0
include hp in
lemma loyal {T: Matrix A A fps}{L: Matrix B B fps}{v:A→fps}{w:B→fps}(hc : Keep g v w)
   (ht:lowers g L) (h : T = L.submatrix g g) : Keep g (v ᵥ* T) (w ᵥ* L) := by
 let J := univ.image g
 have he(j) : (w ᵥ* L) j=∑ i,v i * L (g i) j := by
   rw [Matrix.vecMul,dotProduct, ← sum_subset (subset_univ J)];
   · unfold J; rw [Finset.sum_image hp.injOn]; simp_rw [hc.1]
   intro i _ hi; rw [hc.2 i (by rintro ⟨i,rfl⟩; simp [J] at hi), zero_mul]
 constructor
 · intro i; rw [he,h]; rfl
 intro i h; rw [he]; simp_rw [ht _ i h, mul_zero,Finset.sum_const_zero]

def valuation (a : (Fin n→A)→fps)(v: Fin n→ A→fps) := ∑ b, a b * ∏ i, v i (b i)
-- field linearity at any coefficient order

def program (a : (Fin n→A)→fps) : MultilinearMap fps (fun _:Fin n=> (A→fps)) fps :=
  ∑ i:(Fin n→A), a i • (MultilinearMap.mkPiAlgebra fps (Fin n) fps).compLinearMap (fun j=> LinearMap.proj (i j))
lemma program_eq (a : (Fin n→A)→fps) (v) : program a v=valuation a v:= by rw [program, _root_.sum_apply]; rfl

include hp in
lemma inserted (a: (Fin n→B)→fps){v : Fin n→ A→fps}{w:Fin n→B→ fps} (h:∀ i,Keep g (v i) (w i)): valuation a w= valuation (fun i=>a (g ∘ i)) v:= by
 let f(i:Fin n→A):= g ∘ i; have hf : Injective f:=fun _ _ h=>funext fun i=>hp (congr_fun h i)
 let U:= univ.image f; unfold valuation; rw [← sum_subset (subset_univ U)]
 · unfold U; rw [sum_image hf.injOn]; unfold f; simp_rw [Function.comp_apply, (h _).1];
 intro i _ hi; apply mul_eq_zero_of_right;
 have he:∃ j:Fin n,i j∉Set.range g:= by contrapose! hi; choose x hx using hi; exact mem_image.mpr ⟨x,mem_univ _,funext hx⟩
 obtain ⟨j,hj⟩:=he; exact Finset.prod_eq_zero (mem_univ j) ((h j).2 _ hj)

lemma reassign (t:Profile)(a:Mark A Profile.n→fps)(v:Fin (Profile.n t)→ A→fps) (L:Matrix A A fps) :
    valuation (fun x=> PertExtension.Position.insert _ _ a L ⟨t,x⟩) v= valuation (fun x=>a ⟨t,x⟩) (fun i=>v i ᵥ* L) := by
  unfold valuation PertExtension.Position.insert; simp_rw [Finset.sum_mul,Matrix.vecMul,dotProduct]
  -- disambiguate using local function values of matrix in FrameAt convention
  let f (i j:A):= L i j
  change ∑ x:Fin t.n→A,∑ y:Fin t.n→A,(a ⟨t,y⟩*∏ i,f (x i) (y i))*(∏ i,v i (x i))=∑ y:Fin t.n→A,a ⟨t,y⟩*∏ i,∑ j,v i j * f j (y i)
  rw [sum_comm]; apply sum_congr rfl; intro i _; rw [Fintype.prod_sum, Finset.mul_sum]; apply sum_congr rfl; intro x _; rw [prod_mul_distrib]; ring

end rows
variable {i j:ℕ}
open Deck
abbrev Seats (F:Frames G) (i:ℕ):= Deck F i→fps
variable (Z R) in
def detect (t:Test n) (v:Fin n→ Seats F i): fps:= valuation (fun w=>R.adjust Z i ⟨⟨n,t⟩,w⟩) v

-- the chosen insertion at its own horizon extended into the field space using precisely this projector

def promote (h:i≤j) (v : Seats F i) : Seats F j := ∑ k:Deck F i, Pi.single (climb F h k) (v k)
lemma proceeds (h:i≤j) (v: Seats F i) : Keep (climb F h) v (promote h v) := by
  constructor
  · intro k; unfold promote; rw [Finset.sum_apply, Finset.sum_eq_single_of_mem k (mem_univ _), Pi.single_eq_same];
    intro i _ hi; exact Pi.single_eq_of_ne ((Deck.climb_inj F h).ne (Ne.symm hi)) ..
  intro k hk; unfold promote; rw [Finset.sum_apply]; apply sum_eq_zero; intro i _; exact Pi.single_eq_of_ne (fun h=> hk ⟨i,h.symm⟩) ..
omit [Fintype A][Fintype B] in
lemma unique {x:A→fps}{y z:B→fps}{g:A→B}(h:Keep g x y)(k:Keep g x z):y=z:= by
  funext i; by_cases hj:i∈Set.range g; obtain ⟨i,rfl⟩:=hj; exact (h.1 i).trans (k.1 i).symm
  exact (h.2 i hj).trans (k.2 i hj).symm

lemma composed {k:ℕ} (hi:i≤j)(hj:j≤k)(v:Seats F i): promote hj (promote hi v)= promote (hi.trans hj) v:= by
 apply unique _ (proceeds _ _); constructor
 · intro u; rw [show climb F (hi.trans hj) u= climb F hj (climb F hi u) by cases u; rfl,(proceeds ..).1 (climb F hi u),(proceeds ..).1 u]
 intro u hu; by_cases h:u∈ Set.range (climb F hj); swap; · exact (proceeds ..).2 u h
 obtain ⟨u,rfl⟩:=h; rw [(proceeds ..).1 u, (proceeds ..).2 u (by rintro ⟨u,rfl⟩; exact hu ⟨u,rfl⟩)]
lemma pad {A} [Zero A] {M:Matrix (Deck F j) (Deck F j) A} (hl:∀ i k, Deck.price F j i < Deck.price F j k→ M i k=0) (he:i ≤ j) : lowers (climb F he) M := by
 intro i k h; apply hl; rw [Deck.price_climb]; exact lt_of_le_of_lt (Deck.price_bound ..) (lt_of_not_ge (fun z => h (of_price F he z)))
variable (Z)
lemma stationed (R:Rails F) (t:ℝ) (h:i≤j) (v:Seats F i): promote h v ᵥ* R.drive t j = promote h (v ᵥ* R.drive t i):= by
 apply unique _ (proceeds ..); refine loyal (climb_inj F h) (proceeds ..) (pad (layer_cut (R.route j|>.station_block _)) h) ?_; unfold Rails.drive Passe.drive; rw [← R.nested i j h t]; exact tile_across (w:=price F j) (v:=price F i) (f:=⟨_,climb_inj F h⟩) (fun i=>rfl) _
lemma across (R:Rails F) (t:Test n)(h:i ≤ j)(v : Fin n→Seats F i) : detect R Z t (fun i=> promote h (v i))=detect R Z t v:= by
 unfold detect; rw [R.across Z h] -- rhs bigger
 exact inserted (climb_inj F h) _ (fun _=>proceeds h _)
variable {Z}
lemma warp (h:Street Z R) (t : Test n)(v:Fin n→Seats F i) (s:ℝ) :
    R.flow.warp s (detect R Z t v) = detect R Z (Next.UVStress.dilate (Real.exp_pos (-s)) t) (fun j=> (R.flow.warp s ∘ v j) ᵥ* R.drive s i) := by
 let T:= Next.UVStress.dilate (Real.exp_pos (-s)) t
 have hk(w: Fin n→ Deck F i): R.flow.warp s (R.adjust Z i ⟨⟨n,t⟩,w⟩)=PertExtension.Position.insert _ _ (R.adjust Z i) (R.drive s i) ⟨⟨n,T⟩,w⟩:=
   (congr_fun (R.relocation h s) (Sigma.mk (β:=fun p:Profile=> Fin p.n → Deck F i) ⟨n,t⟩ w)).trans (congr_fun (Position.move (R.adjust Z i) (R.drive s i) s) (Sigma.mk (β:=fun p:Profile=>Fin p.n→Deck F i) ⟨n,t⟩ w))
 unfold detect valuation; simp_rw [map_sum,map_mul,map_prod,hk]
 exact reassign ⟨n,T⟩ (R.adjust Z i)  (fun x:Fin n=> R.flow.warp s ∘ v x) (R.drive s i)
end YM.FormalOPE.RG10.Panel
