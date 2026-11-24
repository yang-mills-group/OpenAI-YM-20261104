import YM.SchemeConversionRG11.FirstW.Lien.Note
/-! Interpolate polynomial weights of the *lattice* correction; no DR hypotheses. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.FirstW
open Function Filter Set MeasureTheory Lattice Pert Align Topology Deck Maxwell Extra.FD RawLabels MvPolynomial
open scoped BigOperators Classical
variable {G : Gauge} {i j k : ℕ}
lemma chooses_pair (p: Rhythm G) (e:ToneR p k) (ht:k≤4) (i j:ℕ) (hij:i+1+(j+1)=k) (hi:i+1≤4)(hj:j+1≤4) :
    ∃ (L:Field4 G →ₗ[ℝ] Nu G (i+1))(F:Field4 G →ₗ[ℝ] Nu G (j+1))(q: Reel G),
     (∀ u v:Field4 G, chord u v q.val=(1/2:ℂ)*(patchR p _ _ hi hj (L u) (F v) +patchR p _ _ hi hj (L v) (F u))) ∧
     (∀ u:Nu G (i+1),∀ v:Nu G (j+1), patchR p _ _ hi hj (L u.val) v=patchR p _ _ hi hj u v) ∧
     (∀ u:Nu G (i+1),∀ v:Nu G (j+1), patchR p _ _ hi hj u (F v.val)=patchR p _ _ hi hj u v) := by
  let P:=patchR p _ _ hi hj
  have hh:= lamp p e (i+1) (j+1) hij.le hi hj
  obtain ⟨_,⟨L,rfl⟩,Hl⟩:= easeR (G:=G) i
  obtain ⟨_,⟨B,rfl⟩,H⟩:= easeR (G:=G) j
  let f:=L.comp (flute i); let g:=B.comp (flute j)
  obtain ⟨t,hT⟩:= recital ((P.comp L).compl₂ B)
  let q:Reel G:= ⟨t.val,room _ _ _ (by omega : i+j+4≤6) t.property⟩
  refine ⟨f,g,q,fun x y=>?_,fun x y=>?_, fun x y=>?_⟩
  · have hs (x:Field4 G): sun x q.val= P (f x) (g x):= hT (stageW G x)
    rw [chord_at,hs,hs,hs]; change _=(1/2:ℂ)* (P (f x) (g y)+ P (f y) (g x)); simp only [map_add,LinearMap.add_apply];ring
  · have he:P (f x.val-x) y=0:= hh (f x.val-x) y (Or.inl (Hl x)); rw [map_sub,LinearMap.sub_apply] at he; exact sub_eq_zero.mp he
  have he:P x (g y.val-y)=0:= hh x (g y.val-y) (Or.inr (H y)); rw [map_sub] at he; exact sub_eq_zero.mp he
lemma steady0 (A : la G)(h:A.val∈cabin G 0): quietly A.val := by
 have he (v:Cover)(i:Axis): A.val (v,i)=A.val (0,i):= loft_basis (cabin_floor h i) _
 intro i j x; unfold Bare.wideCurl; rw [he x i,he (x+step i) j,he (x+step j) i,he x j];abel
lemma pursues (p : Rhythm G) (h:ToneR p k) (q:Reel G)
   (hp : ∀ (a b : ℕ), (a ≤ b) → (a + b ≤ k) → 1 ≤ a → ∀ x y : la G, x.val ∈ cabin G a → y.val ∈ cabin G b → p y x = chord y.val x.val q.val) : ripple _ p q k := by
  have hP (i j:ℕ)(he:i≤j)(H:i+j≤k)(a b:la G)(ha:a.val∈cabin G i)(hb:b.val∈cabin G j) : p b a=chord b.val a.val q.val := by
    by_cases hu:1 ≤ i; · exact hp i j he H hu a b ha hb
    obtain rfl:= show i=0 by omega
    rw [(h b a).1,(h _ _).2 0 j H ha hb (steady0 a ha), chord_com, dead_note a (steady0 a ha) q b.val]
  intro i j hij a b ha hb
  rcases le_total i j with hi|hi
  · rw [(h a b).1,hP i j hi hij a b ha hb,chord_com]
  exact hP j i hi (by omega) b a hb ha
end YM.RG11.FirstW
