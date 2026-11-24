import YM.RG11Proof.Rigidity.Ice.JetShift
import YangMills.WilsonProof.NativeSupport.YM.Next.MAXWELL.Ends

/-!
# Charge ledger, at one order's leading detector ambiguity
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Rigidity.Ice
open Fields Horizon Labels Pert.Position Pert Maxwell Function Extra.FD Reads Maxwell.Free Crowd Prism
open scoped Classical BigOperators InnerProductSpace
variable {G:Gauge}{F:Frames G}{d j:ℕ}
local notation "V"=>G.Color
local notation "Long"=> V→L[ℝ] V

lemma shows_film (v : Shell G j) (u : Long) (p : Flavor j) : available (faceMap j u v) p = u (available v p) := by
  have he (k:G.ColorIndex) : faceMap j (cp k) (faceMap j u v) =∑ i : G.ColorIndex,
      (u (unitColor G i) k) • faceMap j (cp i) v := by
    apply Subtype.ext; funext a b; ext1 z
    simp_rw [AddSubmonoidClass.coe_finsetSum,SetLike.val_smul,Finset.sum_apply,sum_apply,Pi.smul_apply,smul_apply,face_eval]
    change u _ k=_
    conv_lhs=>rw [← color_sum (G:=G) (v.val a b z),map_sum]
    simp_rw [WithLp.ofLp_sum,Finset.sum_apply,map_smul,PiLp.smul_apply]
    exact Finset.sum_congr rfl (fun i _=> mul_comm ..)
  ext1 k
  change p (faceMap _ _ _) = _
  rw [he]; conv_rhs=>rw [← color_sum (G:=G) (available v p),map_sum]
  simp only [map_sum,map_smul,WithLp.ofLp_sum,Finset.sum_apply,PiLp.smul_apply]
  exact Finset.sum_congr rfl fun _ _=>mul_comm ..

abbrev quoteL (F:Frames G)(n:ℕ)(Q:TaylorTower G): E F d→ₗ[ℂ] ℂ:= (probe Q).toLinearMap ∘ₗ (Reads.top n) ∘ₗ (writes F d)
-- (the proposition, not a group instance)
def Feasible (b : Buffer F d)(t : ℝ) (O : Long): Prop:=
  (∀ a a':V,inner ℝ (O a) (O a')=inner ℝ a a') ∧
    ∀ i:News F d,∀ Q:TaylorTower G, quoteL F i.n Q i.v = quoteL F i.n (films O Q) (drive b.val i.v t)

lemma Frigid.feasible {b : Buffer F d}(h:Frigid b)(hd:4≤d)(hG:G.Simple)(t:ℝ): ∃ O : Wheel G, Feasible b t (steers O):=by
  obtain ⟨O,hO⟩:= gr_paint h hd hG t
  refine ⟨O,O.inner_map_map,fun i Q=>?_⟩
  change probe _ (MvPolynomial.weightedHomogeneousComponent _ _ (writes F _ i.v)) = _
  rw [MvPolynomial.weightedHomogeneousComponent_eq_self i.gr]; exact hO i Q

abbrev adSpin (u : G.El) := (G.adjoint u).toContinuousLinearMap
lemma top_hide (i : ℕ)(v:E F d)(u:G.El)(Q:TaylorTower G):
    quoteL F i (films (adSpin u) Q) v = quoteL F i Q v:=by
  let B := tower F d
  suffices hh : quoteL F (d:=d) i (films (adSpin u) Q)=quoteL F i Q by rw [hh]
  apply B.b.ext; intro p
  let X:= writes F d (B.b p)
  change probe (shade u Q) (Reads.top i X) = probe Q (Reads.top i X)
  rw [← pigment_action]
  have H:= web_grains B p
  by_cases ht:i=(B.w p).1
  · subst i
    have hs : X∈shellSector G d:= (exactField F d (B.b p)).property
    rw [show Reads.top _ X=X from MvPolynomial.weightedHomogeneousComponent_eq_self H, (sector.mp hs).2 u]
  have hz : Reads.top i X=0:= MvPolynomial.weightedHomogeneousComponent_eq_zero' i _ (fun w hw=>by rw [H (MvPolynomial.mem_support_iff.mp hw)]; exact Ne.symm ht)
  rw [hz,map_zero]

lemma adSpin_iso (u : G.El)(x y : V): inner ℝ (adSpin u x) (adSpin u y)=inner ℝ x y:=
  LinearIsometry.inner_map_map (f:= (⟨G.adjoint u,G.norm_adjoint u⟩: V→ₗᵢ[ℝ] V)) _ _

lemma Feasible.vol {b:Buffer F d}{t:ℝ}{O : Long}(h:Feasible b t O)(v:G.El):Feasible b t ((adSpin v).comp O):=by
  constructor
  · intro a c; rw [ContinuousLinearMap.comp_apply,ContinuousLinearMap.comp_apply, adSpin_iso,h.1]
  intro i Q; rw [← reel_film,top_hide,h.2]

lemma Feasible.adjust {b:Buffer F d}{t:ℝ}{O S P : Long}(h:Feasible b t O)(H:Feasible b 0 S)(hg : S.comp P = .id ℝ V) (hP:∀ i j:V,inner ℝ (P i) (P j)=inner ℝ i j): Feasible b t (O.comp P):=by
  constructor
  · intro a c; rw [ContinuousLinearMap.comp_apply,ContinuousLinearMap.comp_apply,h.1,hP]
  intro i Q
  have hh := H.2 i (films P Q); rw [starts,reel_film,hg,films_self] at hh
  rw [← hh,h.2,reel_film] -- ψ source to ψ at O(P Q). 
end YM.RG11.Rigidity.Ice
