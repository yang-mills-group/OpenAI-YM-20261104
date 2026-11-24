import YM.FormalBulk08.City.Mural

/-! Divergence form: synthesized pastures. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.City
open Reef Lava Lattice Laurent Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 PowerSeries
open Lotus Shore Mesa
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G : Gauge} {m : Type} {n : Side} (i : hue G)

abbrev Pane (G : Gauge)(m : Type):=m×TypeFace 1× hue G
def driftP (p : Pap (wire G n))(l:Bool) (u:wire G n):=yaw u p * spinP i u l
def backwards {x : Type} [AddCommGroup x] [One x] (a : Four x) (v : TypeFace 1):= a-step (axisEquiv.symm v)

lemma environs (x : Site n) (p : Pap (wire G n)) (h : Rite p p 1 0) (hp : ∀ v,step v≠(0:Site n)) :
   (∑ v: TypeFace 1 × hue G,(driftP i p true (x,v)+driftP i p false (backwards x v.1,v)))=0:= by
   have hh:=shedder i x p h hp; rw [←hh,Finset.sum_add_distrib];simp_rw [mul_add, Finset.sum_add_distrib];congr 1
   · symm;rw [Fintype.sum_prod_type, Finset.sum_comm]; apply Finset.sum_congr rfl; intro j _
     rw [Finset.sum_eq_single x]; exact (by rw [if_pos rfl];rfl); intro b _ hb; rw [if_neg hb,mul_zero];simp
   symm;rw [Fintype.sum_prod_type, Finset.sum_comm]; apply Finset.sum_congr rfl; intro j _
   rw [Finset.sum_eq_single (backwards x j.1)]; exact (by simp [backwards,driftP]); swap; · simp
   intro b _ hb; rw [if_neg (fun he=> hb (eq_sub_of_add_eq he)),mul_zero]

-- stencils homogeneous ord=k pre arity split.
def hill (v:Pane G m)(l:Bool)(k r:ℕ) : Tile (Pane G m) r:= fun w=> ∑ a:chain (hue G) r, if rowD v ∘ a=w then rancho (paste (will i l v.2.2)) k r a else 0
lemma spinnery (v:wire G n)(l:Bool)(k r:ℕ) : rancho (spinP i v l) k r=hill i v l k r := by
   rw [rancho,spinP,coeff_map]; change marble r ((MvPolynomial.rename (rowD v)) _)=_; rw [pebble]; funext w;rw [cores_here,hill];refine Finset.sum_congr rfl fun j _=> ?_; by_cases hj: rowD v ∘ j=w <;> simp only [hj,rancho,originP,↓reduceIte]
lemma hill_empty (v:Pane G m) (l:Bool)(k r : ℕ) (h:r≠k) : hill i v l k r=0:= by
   have he : rancho (paste (will i l v.2.2)) k r=0:= (marble_eq_zero_iff _ _).mpr (by rw [MvPolynomial.homogeneousComponent_of_mem (paste_grade _ k),if_neg h]); funext a; simp only [hill,he,Pi.zero_apply,ite_self,Finset.sum_const_zero]
lemma hill_base (v:Pane G m) (l:Bool) (a) : hill i v l 0 0 a=(if l then 1 else -1)* dotI i v.2.2 := by
   have he (x:chain (hue G) 0) := congr_fun (show rancho (paste (will i l v.2.2)) 0 0=marble 0 (MvPolynomial.C ((if l then 1 else -1)*dotI i v.2.2)) by rw [rancho,paste_first,will_at]) x
   let A := (if l then (1:ℝ) else -1)* dotI i v.2.2
   have hx : marble 0 (MvPolynomial.C (σ:=hue G) A)=fun _=> A:= facade_unique (marble_agate _ _) (fun _ _=> rfl) (by rw [marble_grade, MvPolynomial.homogeneousComponent_eq_self (MvPolynomial.isHomogeneous_C _ _), facade_eq]; simp [cards])
   have hb (b:chain (hue G) 0): rowD v ∘ b=a:=Subsingleton.elim ..
   unfold A at hx
   change (∑ b, if rowD v∘ b=a then _ else _)=_; simp only [hb,↓reduceIte,he,hx]; simp

abbrev diagD (r : ℕ):= {a // a∈Finset.antidiagonal r}
def plaster (v : Pane G m) (l:Bool)(k:ℕ) {r : ℕ} (a : diagD r) (T : Tile (Pane G m) (a.1.1+1)) :=
   ((a.val.1+1:ℕ):ℝ) • lengthen (Finset.mem_antidiagonal.mp a.property) (sand (clutch (shed T v) (hill i v l k a.val.2)))
def shapeD (v : Pane G m) (l:Bool)(a : ℕ×ℕ)(r : ℕ)(U: OrbitV (Pane G m)):Tile (Pane G m) r:=
   ∑ t∈(Finset.antidiagonal r).attach,plaster i v l a.2 t (U a.1 (t.val.1+1))
lemma rank_grade (v : wire G n) (p : Pap (wire G n)) (l:Bool)(a:ℕ×ℕ)(r:ℕ) : marble r (coeff a.1 (yaw v p)*coeff a.2 (spinP i v l))=shapeD i v l a r (rancho p) := by
   apply facade_unique (marble_agate _ _) (Agate.sums _ (fun _ _=> (length_agate _ (agate_sand _)).smul _))
   rw [marble_grade, comp_glue, map_sum]; simp_rw [map_smul,facade_length,sand_facade, facade_clutch, MvPolynomial.smul_eq_C_mul,←mul_assoc]; simp_rw [←spinnery]
   have hh (t : diagD r) := facade_slope v (T:=rancho p a.1 (t.val.1+1)) (marble_agate _ _)
   simp_rw [←hh, rancho, marble_grade,yaw, coeff_shaft, comp_fuses]; exact (Finset.sum_attach (Finset.antidiagonal r) (fun t=> MvPolynomial.pderiv v (MvPolynomial.homogeneousComponent (t.1+1) (coeff a.1 p))*MvPolynomial.homogeneousComponent t.2 (coeff a.2 (spinP i v l)))).symm -- dep

def cruisesD {M : Type} [AddCommGroup M][One M] (x : Four M) (a : ℕ ×ℕ) (r:ℕ) (U : OrbitV (Pane G (Four M))) :=
   ∑ v:TypeFace 1 × hue G,(shapeD i (x,v) true a r U+shapeD i (backwards x v.1,v) false a r U)
lemma apex (x : Site n)(e r:ℕ)(p : Pap (wire G n)) (h:Rite p p 1 0) (hp:∀ v,step v≠(0:Site n)) : ∑ a∈Finset.antidiagonal e,cruisesD i x a r (rancho p)=0 := by
    have he:= congr_arg (canyon (V:=wire G n) r) (congr_arg (coeff e) (environs i x p h hp))
    simp only [map_sum,map_zero,map_add,driftP,coeff_mul,canyon_eq,rank_grade] at he; rw [←he]; unfold cruisesD; rw [Finset.sum_comm]; simp_rw [Finset.sum_add_distrib]
end YM.FormalBulk08.City
