import YM.FVA2.Coordinate
import YM.PertExtension.OrbExpansion

/-!
# Geometry common to the rooted and minimal calculations

Full periodic and the `b=true` inversion-quotient chart as two actual `Ends`.
Top sign is exponent sign, exactly one face of the ordinary Wilson action
per inversion orbit (thus half the full exponent on lifted variables).
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Inversion
open Finset Set Function Filter Lattice Wilson Gauge
open MS MS.Native MS.Book MS.Koszul MS.Cylinder MS.Bare MS.Cylinder.Taylor
open ArrayMap PertExtension PertExtension.Orb
open scoped Classical Topology ContDiff Matrix.Norms.Frobenius

variable {n : Side} {G:Gauge}
/-- Independent ghosts. Use one (at 0) fewer because we're splitting the
residual constant gauge factor from the Wick calculation. -/
abbrev Vert (n : Side) := {x : Site n // vertex x=x ∧ x≠0}

def locate (x: Site n) : Option (Vert n) :=
  if h:vertex x=0 then none else some ⟨vertex x,vertex_vertex x,h⟩
lemma locate_at (x : Vert n) : locate x.val=some x := by
  have he : vertex x.val≠0:=by rw [x.property.1]; exact x.property.2
  unfold locate; rw [dif_neg he]; congr; exact x.property.1
@[simp] lemma locate_zero : locate (0:Site n)=none := by simp [locate]
lemma locate_neg (x:Site n) : locate (-x)=locate x := by
  unfold locate; simp only [vertex_neg]
lemma locate_rep (x:Site n) : locate (vertex x)=locate x := by
  rcases vertex_spec x with h|h; rw [h]; rw [h,locate_neg]

abbrev FullX (G:Gauge) (n:Side) := Ends.Links G (Edge (Site n))
abbrev FullY (G:Gauge) (n:Side) := Ends.Links G (Site n)
abbrev RootX (G:Gauge) (n:Side) := Ends.Links G (OEdge n)
abbrev RootY (G:Gauge) (n:Side) := Ends.Links G (Vert n)

def full (n:Side) : FVA2.Ends (Edge (Site n)) (Site n):=
  ⟨fun i=>some i.1, fun i=> some (i.1+step i.2)⟩
def root (n:Side) : FVA2.Ends (OEdge n) (Vert n):=
  ⟨fun i=> locate i.val.1, fun i=>locate (i.val.1+step i.val.2)⟩

def incl (G:Gauge) (n:Side) : RootX G n →ₗ[ℝ] FullX G n where
  toFun u x := if eR x=x then u (Orb.index x) else -u (Orb.index x)
  map_add' u v := by funext x; split_ifs <;> simp [*,add_comm]
  map_smul' c u := by funext x; split_ifs <;> simp [*]

lemma agree_ref (e:Edge (Site n)) : index (reflect e)=Orb.index e := Subtype.ext (eR_reflect _)
lemma lifted (u:RootX G n)(e:OEdge n) : incl G n u e.val=u e := by
  unfold incl; simp only [LinearMap.coe_mk,AddHom.coe_mk,if_pos e.property]
  rw [show index e.val=e from Subtype.ext e.property]
lemma refl_lift (even : Even n.val) (u:RootX G n)(x:Edge (Site n)) :
    incl G n u (reflect x)= -(incl G n u x) := by
  unfold incl; simp only [LinearMap.coe_mk, AddHom.coe_mk,eR_reflect, agree_ref]
  rcases eR_spec x with h|h
  · simp only [h,if_neg (no_fixed_edge even x).symm, ↓reduceIte]
  simp only [h,if_neg (no_fixed_edge even x), ↓reduceIte,neg_neg]
lemma lifted_physical (u:RootX G n) : Ends.exp_A (incl G n u)= Orb.liftLinks (Ends.exp_A u) := by
  funext x; unfold Ends.exp_A incl liftLinks; dsimp only [comp_apply, LinearMap.coe_mk,AddHom.coe_mk]
  split; rfl; exact Next.SectorChange.exp_negative ..

lemma sum_edges {Q:Type*}[AddCommMonoid Q](f:Edge (Site n)→Q)(he: Even n.val) :
    ∑ x:Edge (Site n), f x = ∑ i:OEdge n,(f i.val + f (reflect i.val)) := by
  let U (i:OEdge n):=(i.val:Edge _)
  let e : OEdge n ⊕ OEdge n → Edge (Site n):= Sum.elim U (reflect∘U)
  have hb : Bijective e := by
    constructor
    · rintro (a|a) (b|b) ht
      · exact congr_arg Sum.inl (Subtype.ext ht)
      · exfalso
        change a.val=reflect b.val at ht
        have hv:=a.property; rw [ht,eR_reflect,b.property] at hv; exact no_fixed_edge he b.val hv.symm
      · exfalso
        change reflect a.val=b.val at ht
        have hv:=b.property; rw [← ht,eR_reflect,a.property] at hv; exact no_fixed_edge he a.val hv.symm
      exact congr_arg Sum.inr (Subtype.ext ((Involutive.injective reflect_reflect) ht))
    intro b; rcases eR_spec b with h|h
    · exact ⟨Sum.inl (index b),h⟩
    exact ⟨Sum.inr (index b),(congr_arg reflect h).trans (reflect_reflect b)⟩
  rw [←Equiv.sum_comp (Equiv.ofBijective e hb),Fintype.sum_sum_type,Finset.sum_add_distrib]; rfl

def pin (G:Gauge) (n:Side) : RootY G n →ₗ[ℝ] FullY G n where
  toFun u x := (locate x).elim 0 u
  map_add' u v := by funext x; cases he:locate x <;> simp [he]
  map_smul' c u := by funext x; cases he:locate x <;> simp [he]

lemma pin_at (u:RootY G n) (x : Vert n) : pin G n u x.val=u x := by unfold pin; dsimp only [LinearMap.coe_mk,AddHom.coe_mk]; rw [locate_at]; rfl
@[simp] lemma pin_zero (u:RootY G n) : pin G n u 0=0 := by simp [pin]
lemma pin_even (u:RootY G n) (x:Site n) : pin G n u (-x)=pin G n u x := by unfold pin; simp [locate_neg]

def priorFull (G:Gauge) (n:Side) (u : FullX G n) := -Wilson.energy (Ends.exp_A u)

def priorRoot (G:Gauge) (n:Side)(u : RootX G n) :=
  -(Wilson.energy (Orb.liftLinks (Ends.exp_A u))/2)
lemma prior_one (u : RootX G n) : priorRoot G n u = (2:ℝ)⁻¹ * priorFull G n (incl G n u):= by
  unfold priorRoot priorFull; rw [lifted_physical]; ring

lemma based_group (t : Vert n→G.El) (u:OEdge n→G.El) :
    let T : Site n → G.El:= fun x => ((locate x).elim 1 t)⁻¹
    Lattice.gauge T (Orb.liftLinks u) = Orb.liftLinks ((root n).action_by t u) := by
  intro T
  funext x; rw [path_law T u (fun x=>by simp [T,locate_neg])]
  congr; funext e
  unfold Lattice.gauge; rw [lift_at]
  change _ * _ * (((locate (e.val.1 + _)).elim 1 t)⁻¹)⁻¹ = _
  rw [inv_inv]; rfl

lemma root_inv (U : Config G n→ℝ)
    (h : ∀ u:Site n→G.El,(∀ x,u (-x)=u x)→∀ q,U (Lattice.gauge u q)=U q) :
    (root n).invariant (U ∘ Orb.liftLinks) := by
  intro u v; simp_rw [comp_apply]; rw [← based_group u v]; exact h _ (fun x=>by rw [locate_neg]) _
lemma prior_root_inv : (root n).invariant (fun u:OEdge n→G.El=> -(Wilson.energy (liftLinks u)/2)) :=
  root_inv (fun x:Config G n=> -(energy x/2)) (fun t _ x=>by rw [Wilson.energy_gauge])

lemma prior_full : priorFull G n = MS.Native.Chart.rent (G:=G) (MS.Native.Chart.drive n) :=
   funext fun x=> (MS.Native.Chart.original_W x).symm
lemma energy_unit (G:Gauge)(n:Side) : Wilson.energy (1: Config G n)=0 := by
  have he:= flat_at_zero (n:=n) (G:=G); rw [show links 1 (1:Cotree n→G.El)=1 from ?_] at he; exact he
  funext i; unfold links liftLinks splitLink; split<;> split<;> simp
lemma exp_A0 {I:Type} : Ends.exp_A (0:I→G.Color)=1 := by funext i; exact mat_lieExp_zero _
lemma prior_full_prop (G:Gauge) (n:Side) : (full n).Action (priorFull G n) := by
  have hp : germ (priorFull G n) := by rw [prior_full]; exact Native.Chart.rent_s _
  have ht : priorFull G n 0=0:= by unfold priorFull; rw [exp_A0,energy_unit,neg_zero]
  refine ⟨ht, ?_,hp,(full n).inert_from (F:=fun b:Edge (Site n)→G.El=> -Wilson.energy b) ?_ hp⟩
  · have hL : IsLocalMax (priorFull G n) 0 := Eventually.of_forall fun x=>by
              change priorFull G n x ≤ priorFull G n 0; rw [ht]; exact neg_nonpos.mpr (Wilson.energy_nonneg _)
    exact hL.fderiv_eq_zero
  intro u v
  have hk : (full n).action_by u v = Lattice.gauge u⁻¹ v:=by funext e; unfold Lattice.gauge full Ends.action_by; simp
  rw [hk]; simp [Wilson.energy_gauge]

lemma prior_root_prop (G:Gauge) (n:Side) : (root n).Action (priorRoot G n) := by
  have hp : germ (priorRoot G n):= by
    let U:RootX G n →L[ℝ] FullX G n := (incl G n).toContinuousLinearMap
    rw [show priorRoot G n = fun x=> (2:ℝ)⁻¹ * priorFull G n (U x) from funext prior_one];
    exact contDiffAt_const.mul ((show ContDiffAt ℝ ω (priorFull G n) (U 0) from by rw [map_zero]; exact (prior_full_prop G n).smooth).comp 0 U.contDiff.contDiffAt)
  have hx : priorRoot G n 0=0:= by rw [prior_one,map_zero,(prior_full_prop G n).base,mul_zero]
  refine ⟨hx,?_,hp,(root n).inert_from _ prior_root_inv hp⟩
  have he : IsLocalMax (priorRoot G n) 0:=Eventually.of_forall fun x=> by
                  change priorRoot G n x≤priorRoot G n 0; rw [hx]; exact neg_nonpos.mpr (div_nonneg (Wilson.energy_nonneg _) (by norm_num))
  exact he.fderiv_eq_zero


open Ends

lemma fullEnd0 (u : FullY G n) (x:Edge (Site n)) :
    (full n).flow 0 u x=u (x.1+step x.2)-u x.1 :=
  Maurer.volt_zero _
lemma rootEnd0 (u:RootY G n) (e:OEdge n) :
    (root n).flow 0 u e= pin G n u (e.val.1+step e.val.2)-pin G n u e.val.1 :=
  Maurer.volt_zero _

lemma root_gradient (he: Even n.val)(u:RootY G n) :
    incl G n ((root n).flow 0 u)= (full n).flow 0 (pin G n u) := by
  funext e
  have hx (x : OEdge n): incl G n ((root n).flow 0 u) x.val=(full n).flow 0 (pin G n u) x.val:= by
    rw [lifted,rootEnd0,fullEnd0]
  rcases eR_spec e with h|h
  · exact hx ⟨e,h⟩
  rw [← neg_inj, ← refl_lift he]
  rw [hx ⟨reflect e,by rw [eR_reflect,h]⟩,fullEnd0,fullEnd0]; unfold reflect;
  dsimp only
  rw  [sub_add_cancel, show -e.1-step e.2= -(e.1+step e.2) from (by abel),pin_even,pin_even]; abel
open Matrix
abbrev incidenceLift := coordinate (incl G n)
abbrev chartPin := coordinate (pin G n)
lemma lifted_gradient (he: Even n.val) :
    coordinate (incl G n) * gradientGraph (G:=G) (root n) =
      gradientGraph (G:=G) (full n)*coordinate (pin G n) := by
  rw [← dGraph,← dGraph,← coordinate_mul,← coordinate_mul]; exact congr_arg coordinate (LinearMap.ext fun x=> root_gradient he x)
lemma hessian_ratio : costMatrix (priorRoot G n) = (2:ℝ)⁻¹ •
    ((coordinate (incl G n))ᵀ * costMatrix (priorFull G n) * coordinate (incl G n)) := by
  let U:RootX G n→L[ℝ] FullX G n:=(incl G n).toContinuousLinearMap
  let S:= priorFull G n
  have hv:= (prior_full_prop G n).smooth
  have he : germ (S ∘ U):=(show ContDiffAt ℝ ω S (U 0) from by rw [map_zero]; exact hv).comp 0 U.contDiff.contDiffAt
  rw [show priorRoot G n=(2:ℝ)⁻¹ • (S ∘ U) from funext prior_one,costs_smul (S∘U) (2:ℝ)⁻¹ he,costs_comp U S hv]; rfl

end YM.FVA2.Inversion
