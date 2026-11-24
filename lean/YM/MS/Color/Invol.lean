import YM.MS.Color.Pigment
/-!
# Position reality without specialization to parity signs on the Lie colors

Mean over this real involution after color.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Color
open Function Filter Set Finset Plane Koszul Real Momentum Wire Tensor Submodule
open Landau Local BV Woven -- ambiguity Realm
open Complex (I)
open scoped Topology ContDiff ComplexConjugate
variable {G : Gauge} {A D P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {F H : Score G A P}
-- Semilinear over ℂ conj ring hom starRingEnd; use starRingEnd ℂ.
def invert (i : Note G A P): Note G A P:= (i.1,-i.2)
def overC : Score G A P →ₛₗ[starRingEnd ℂ] Score G A P where
   toFun F i:= star (F (invertMom i))
   map_add' f g:= funext fun i=> star_add _ _
   map_smul' c f:= by ext i; exact star_mul' _ _
omit [NormedSpace ℝ P] in
lemma over_at (F:Score G A P) i: overC F i=star (F (invertMom i)):=rfl

section
omit [NormedSpace ℝ P]
lemma over_D (i:Note G A P): Koszul.D i (overC F) = overC (Koszul.D (invert i) F):= rfl
lemma over_cycle : overC (overC F)=F:= by
    ext i; rw [over_at,over_at]; simp [invertMom, List.map_map,Function.comp_def]
lemma over_k (u:G.El) : repeatC u (overC F)=overC (repeatC u F):= by
    ext i; rw [over_at]; induction i generalizing F with
    | nil=>rfl
    | cons i l ih=>
       unfold invertMom at *; rw [repeat_cons,List.map_cons,repeat_cons,star_sum]; refine Finset.sum_congr rfl fun k _=>?_; rw [over_D, ih (F:=Koszul.D (invert (setLeg i k)) F), star_mul', star_weight]; rfl

lemma over_sym (hf : Koszul.Symm (field Landau.parity) F) : Koszul.Symm (field Landau.parity) (overC F):= by
    intro l i j r; unfold field; simp only [over_at,invertMom,List.map_append,List.map_cons]
    rw [hf,star_mul']; unfold field; have hk (p q:Bool) : star (cross p q:ℂ) = cross p q:=by cases p <;> cases q <;> simp
    rw [hk]
lemma over_bud {f:Local.Twig (Branch G A) P} : overC (bud f F)=bud (fun i=>star (f (invert i))) (overC F):=by
    ext l; cases l with
    | nil=> simp [over_at,invertMom]
    | cons i w=> simp only [over_at, invertMom,List.map_cons, bud_cons, invert,star_mul']
lemma over_line {n : ℕ} (f : Fin n→ Local.Twig (Branch G A) P): overC (Local.line n f)=Local.line n (fun j i=>star (f j (invert i))):= by
   induction n with
   | zero => rw [line_zero,line_zero]; ext; simp [Local.hit,over_at,invertMom]
   | succ n ih=> rw [line_bud,line_bud,over_bud,ih]; rfl
end

section ward
open Detect
variable {f : Grade G} {K: Law G} {h q:ℤ} {r : ℕ}
def over : Grade G→ₛₗ[starRingEnd ℂ] Grade G where
   toFun f i:= star (f (invert i))
   map_add' f g:= by ext; exact star_add ..
   map_smul' c f:= by ext; exact star_mul' ..
lemma painted (f:Grade G) i: over f i= star (f (invert i)):= rfl
lemma over_price (hF:f ∈ yields h q): over f∈ yields h q:= seedStar.mpr ⟨fun i=> by
   let F:=fun p:FourP=>f (i,p); have H : Plane.Shape F (h-mslug i):=(seedStar.mp hF).form i
   change Plane.Shape (fun p=> star (F (-p))) _; refine ⟨Complex.conjCLE.contDiff.comp (H.smooth.comp contDiff_neg),?_,?_⟩
   · intro hv; rw [H.charge hv]; simp; rfl
   intro u x; rw [← smul_neg, H.scale, star_smul, star_trivial], fun i he=> by rw [painted,(seedStar.mp hF).real' (invert i) he]; simp⟩
lemma over_count : Q (over f)=over (Q f):= by
    ext ⟨⟨⟨_|i,_|_⟩,c⟩,p⟩
    · change Q _ (C c p)=star (Q _ (C c (-p))); simp_rw [movesC,star_sum,star_mul',painted]; simp [invert]
    · change Q _ (S c p)=star (Q _ (S c (-p))); simp [movesS]
    · change Q _ (W i c p)=star (Q _ (W i c (-p))); simp_rw [movesA,star_sum,star_mul',k_even,star_neg]; simp [painted,invert]
    change Q _ (U i c p)=star (Q _ (U i c (-p))); simp [painted,movesU,invert,star_mul']

lemma stand (hF: K∈ Carry G h r): overC K∈Carry G h r:= by
    suffices he : Carry G h r≤ Submodule.comap overC (Carry G h r) from he hF
    rw [Carry,span_le]; rintro X ⟨p,w,h,hx,rfl⟩; rw [SetLike.mem_coe,Submodule.mem_comap,over_line]; exact subset_span (mem_setOf.mpr ⟨fun i=> over (p i), w, fun i=> ⟨over_price (h i).1,by rw [over_count, (h i).2,map_zero]⟩, hx,rfl⟩)
lemma staid (hF: K∈ Bed G h q r): overC K∈ Bed G h q r:= by
    suffices he: Bed G h q r ≤ Submodule.comap overC (Bed G h q r) from he hF
    refine bed_le _ ?_; rintro f x y H rfl rfl hv; rw [Submodule.mem_comap, over_line]; exact tileCub.mpr (line_in _ _ (p:=fun i=> over (f i)) (fun i=> seedStar.mp (over_price (H i))))
omit [NormedSpace ℝ P] in
lemma token_real [Fintype A] [DecidableEq A] (f:P→Momentum A) (H':∀ p,f (-p)= -f p) (i j : Branch G A) p: star ((send f).table i j p)=(send f).table i j (-p):= by
    rcases i with ⟨⟨_|i,_|_⟩,c⟩ <;> rcases j with ⟨⟨_|j,_|_⟩,u⟩ <;> by_cases hc:c=u <;> simp [send,bare,choir, *,mul_comm] -- combine simp loops
omit [NormedSpace ℝ P] in
lemma over_act [Fintype A] [DecidableEq A] (f:P→Momentum A) (H':∀ p,f (-p)= - f p): overC ((send f).raise F)=(send f).raise (overC F):= by
    ext w; induction w generalizing F with
    | nil=> simp [Charge.raise,invertMom,over_at]
    | cons a w ih=>
       rcases a with ⟨i,p⟩; rw [Charge.act_at, over_at]; unfold invertMom; rw [List.map_cons,Charge.act_at,star_add,star_mul',star_sum,over_D,← ih]; congr! 1
       · simp only [star_mul',token_real f H',neg_neg]; rfl
       rw [show star (cross true (Landau.parity (i,p).1):ℂ)=cross true (Landau.parity i) from by simp [cross,apply_ite]; split <;> tauto]; rfl
end ward
end YM.MS.Color
