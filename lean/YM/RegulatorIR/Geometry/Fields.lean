import YM.RegulatorIR.Geometry.Dune

/-!
# Haar integration and zero uniqueness on the step tree

Never slice over homogeneous connections. Haar forest change on any indicated
root-compatible quotient forest. Includes bounded or integrable tests. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Geometry
open Function Lattice Wilson PertExtension Orb Gauge Tree Tree.Forest MeasureTheory Filter Field
open scoped ENNReal NNReal BigOperators Classical Topology Matrix.Norms.Frobenius
variable {c f : Side}{g:Ratio c f} {F:Forest g} {G:Gauge}

def goat (k:Site f→ G.El)(U:spins G f) : spins G f := fun i=> Lattice.gauge k (orbLift U) i.val
lemma goat_at (k:Site f→ G.El)(U:spins G f)(i:OEdge f): goat k U i=k i.val.1*U i*(k (i.val.1+step i.val.2))⁻¹:=by unfold goat Lattice.gauge orbLift; rw [lift_at]
lemma goat_lift (k:Site f→ G.El) (U:spins G f)(h:compatible k): orbLift (goat k U)=Lattice.gauge k (orbLift U):=funext (fun i=>(path_law k U h i).symm)
lemma goat_pair (k v:Site f → G.El)(U:spins G f): goat k (goat v U)=goat (k * v) U:=by ext1 i; simp_rw [goat_at,Pi.mul_apply]; group
lemma goat_one (U:spins G f): goat 1 U=U:=by ext i; rw [goat_at]; simp

lemma root_fold (U: Config G f)(h:∀ i:↥F.trunks,U i.val=1) (x:Site f): F.foldAt U x=1:=by
 have hx: F.foldAt U = F.foldAt 1:= F.names U 1 fun z he=> h ⟨z,he⟩
 have hz (i: Site f)(w:Walk):travel (1:Config G f) i w=1:=by induction w generalizing i with
  | nil=> rfl
  | cons a v ih=>simp only [travel,ih,mul_one,Step.read]; split <;> simp
 rw [hx,Forest.foldAt,hz,inv_one]
lemma folded_null (h:Square F) (u:spins G f)(hh:∀ i : Knot F,u i.val=1): F.foldAt (orbLift u)=1:=by
 funext x; apply root_fold
 intro i
 unfold orbLift liftLinks
 split
 · exact hh ⟨_,(Field.bone h i.val).mpr i.property⟩
 rw [show u (index _)=1 from hh ⟨_,(Field.bone h i.val).mpr i.property⟩,inv_one]
-- if tree slice inputs centered on orbit and fine gauge equivalent by preserving roots they agree
lemma rooted_eq (h:Square F) {U V: spins G f}{k:Site f→ G.El} (he:compatible k)(hv: V=goat k U) (hc:∀ x : Site c,k (g.embed x)=1)
  (hU:∀ i: Knot F,U i.val=1)(hV:∀ i: Knot F,V i.val=1): U=V:=by
 have hx x := congr_fun (folded_null h U hU) x; have hp x := congr_fun (folded_null h V hV) x
 have hk:k=1:=by
   funext i; specialize hx i; specialize hp i;rw [hv, goat_lift _ _ he, foldAt,Lattice.travel_gauge] at hp
   have hy:= inv_eq_one.mp (show (travel (orbLift U) i (F.hike i))⁻¹=1 from hx)
   simpa only [hy, F.hike_root, hc,Pi.one_apply,inv_one, mul_one,inv_eq_one] using hp
 rw [hv,hk,goat_one]

-- measurable map on independent slots
abbrev shellMeasure (G:Gauge)(X:Type)[Fintype X]: Measure (X→ G.El) := Measure.pi fun _=>G.probHaar
def spinsMeasure (G:Gauge) (f:Side): Measure (spins G f):= shellMeasure G _
instance (G:Gauge)(f:Side): IsProbabilityMeasure (spinsMeasure G f):= inferInstanceAs (IsProbabilityMeasure (shellMeasure G _))

lemma perm_goat (k: Site f→ G.El):MeasurePreserving (goat k) (spinsMeasure G f) (spinsMeasure G f):=by
 rw [show goat k=(fun U i=> k i.val.1* U i*(k (i.val.1+step i.val.2))⁻¹) from funext fun U=>funext fun i=> goat_at k U i]
 exact measurePreserving_pi _ _ (fun i:OEdge f=>G.preserve_two_sided (k i.val.1) ((k (i.val.1+step i.val.2))⁻¹))

def goatHom (k: Site f→ G.El): spins G f≃ᵐ spins G f where
 toFun:=goat k
 invFun:=goat k⁻¹
 left_inv U:=by rw [goat_pair,inv_mul_cancel,goat_one]
 right_inv U:=by rw [goat_pair,mul_inv_cancel,goat_one]
 measurable_toFun:= (perm_goat k).measurable
 measurable_invFun:= (perm_goat k⁻¹).measurable

namespace Field
variable (F) (G)
-- F Fintype implied?

def pin (F:Forest g)(G:Gauge): Measure (Knot F→ G.El):=shellMeasure G _
def orbOrder (F:Forest g)(G:Gauge): Measure (Wind F→G.El):=shellMeasure G _
instance : IsProbabilityMeasure (pin F G):=by unfold pin;infer_instance
instance : IsProbabilityMeasure (orbOrder F G):=by unfold orbOrder;infer_instance

def rags : (spins G f)≃ᵐ ((Knot F→ G.El)×(Wind F→G.El)):= MeasurableEquiv.piEquivPiSubtypeProd _ _
variable {G}
def cloth (z:Wind F→ G.El):spins G f:=(rags F G).symm (1,z) -- correct dot namespace
-- rags not in Forest
lemma cloth_at (z:Wind F→G.El)(j:Wind F): cloth F z j.val=z j:= congr_fun (congr_arg Prod.snd ((rags F G).apply_symm_apply (1,z))) j
lemma cloth_far (z:Wind F→G.El)(j:Knot F):cloth F z j.val=1 :=congr_fun (congr_arg Prod.fst ((rags F G).apply_symm_apply (1,z))) j
lemma cloth_cont : Continuous (cloth (G:=G) F):=by
 apply continuous_pi; intro i; by_cases he: branch F i
 · simp_rw [fun z=> show cloth (G:=G) F z i=1 from cloth_far F z ⟨i,he⟩]; exact continuous_const
 simp_rw [fun z=> show cloth (G:=G) F z i=z ⟨i,he⟩ from cloth_at F z ⟨i,he⟩]; exact continuous_apply _

def warp (k:Site f→G.El) : (Wind F → G.El) ≃ᵐ (Wind F→ G.El) where
 toFun U i:= k i.val.val.1*U i*(k (i.val.val.1+step i.val.val.2))⁻¹
 invFun U i:=(k i.val.val.1)⁻¹*U i*k (i.val.val.1+step i.val.val.2)
 left_inv := by intro u; funext i; group
 right_inv:= by intro u; funext i; group
 measurable_toFun:=by simp only [Equiv.coe_fn_mk]; fun_prop
 measurable_invFun:=by simp only [Equiv.coe_fn_symm_mk]; fun_prop
lemma permutes (k:Site f→G.El): MeasurePreserving (warp F k) (orbOrder F G) (orbOrder F G) := measurePreserving_pi _ _ (fun i:Wind F=>G.preserve_two_sided (k i.val.val.1) ((k (i.val.val.1+step i.val.val.2))⁻¹))
end Field
end YM.RegulatorIR.Geometry

namespace YM.RegulatorIR.Geometry.Field
open Function Lattice Wilson PertExtension Orb Gauge Tree Tree.Forest MeasureTheory Filter
open scoped ENNReal NNReal BigOperators Classical Topology Matrix.Norms.Frobenius
variable {c f:Side}{g:Ratio c f}{F: Forest g} {G:Gauge}

lemma measured_rags : MeasurePreserving (rags F G) (spinsMeasure G f) ((pin F G).prod (orbOrder F G)):= by
 unfold rags spinsMeasure pin orbOrder
 exact measurePreserving_piEquivPiSubtypeProd (fun _=>G.probHaar) (branch F)
lemma fixed_uses (b:Knot F→G.El)(h:Square F)(hv:Even f.val): ∃ k:Site f→ G.El,compatible k ∧ (∀ i,k (g.embed i)=1) ∧ ∀ x:Wind F→G.El,goat k ((rags F G).symm (b,x))=cloth F (warp F k x):=by
 let U (x:Wind F→G.El):=(rags F G).symm (b,x)
 let k:= F.foldAt (orbLift (U 1)); have hk : compatible k:= lifts_fold h (U 1) hv
 refine ⟨k,hk,fun i=> F.fold_root _ i,?_⟩
 intro x;ext1 i; by_cases hh:branch F i
 · rw [show cloth F _ i=1 from cloth_far F _ ⟨i,hh⟩]
   change Lattice.gauge k (orbLift (U x)) _=1;rw [show k= F.foldAt (orbLift (U x)) from ?_]
   · exact F.compress _ _ hh
   apply F.names
   intro z hz
   let j:Knot F:=⟨index z,(Field.bone h _).mpr hz⟩
   have H (p): U p j.val=b j:=congr_fun (congr_arg Prod.fst ((rags F G).apply_symm_apply (b,p))) j
   change liftLinks _ _=liftLinks _ _; unfold liftLinks; split
   · exact (H _).trans (H _).symm
   exact congr_arg (·⁻¹) ((H _).trans (H _).symm)
 let j: Wind F:=⟨i,hh⟩; change goat k (U x) i = cloth F (warp F k x) i
 rw [goat_at, show U x i=x j from congr_fun (congr_arg Prod.snd ((rags F G).apply_symm_apply (b,x))) j]
 exact (cloth_at F (warp F k x) j).symm

lemma orchard (D:spins G f→ℝ)(h:Integrable D (spinsMeasure G f)) (hp:Square F) (hm:Even f.val)
 (H:∀ k:Site f→G.El,compatible k→ (∀ i,k (g.embed i)=1) →∀ U,D (goat k U)=D U): (∫ U,D U ∂spinsMeasure G f) = ∫ x,D (cloth F x) ∂orbOrder F G:=by
 let P:=pin F G;let Q:=orbOrder F G
 have ht:= measured_rags (F:=F) (G:=G)
 have ha: Integrable (fun x=>D ((rags F G).symm x)) ((pin F G).prod (orbOrder F G)):= (ht.symm.integrable_comp_emb (rags F G).symm.measurableEmbedding).mpr h
 rw [← ht.symm.integral_comp' D, integral_prod _ ha]
 have hh (b:Knot F→G.El):(∫ x,D ((rags F G).symm (b,x)) ∂orbOrder F G)=∫ x,D (cloth F x) ∂orbOrder F G:=by
    obtain ⟨k,hk,hz,hx⟩:= fixed_uses b hp hm
    have ht x : D ((rags F G).symm (b,x))=D (cloth F (warp F k x)):=by rw [← hx,H k hk hz]
    simp_rw [ht]; exact (permutes F k).integral_comp' (fun x=>D (cloth F x))
 change (∫ b, ∫ x, D ((rags F G).symm (b,x)) ∂orbOrder F G ∂pin F G)=_
 simp_rw [hh]; simp
end YM.RegulatorIR.Geometry.Field
