import YM.PertExtension.OrbTree
import YM.Pert.Lattice.GaugeFix
import YangMills.WilsonProof.NativeSupport.YM.MS.Bare.Shadows
/-!
# Root convention and plaquette coordinates of gauges near the flat orbit

One log-link per inversion orbit of unoriented positive edges. One local gauge-color chart per
free vertex orbit (by orbit, not "free action": fixed loci are included) except the root `0`.
The common global gauge is NOT in our gauge parameters. Follow `MS`'s orientation convention:
parameters act on the right (leftmost factor in gauge product per link is the inverse).
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Orbit
open Function Set Filter Finset Topology Lattice PertExtension PertExtension.Orb
open scoped ContDiff Topology BigOperators Classical
variable {G:Gauge} {n:Side}
/-- One gauge angle per vertex orbit, except the root at 0. -/
abbrev Away (n:Side) := {p:Site n // vertex p=p ∧ p≠0}
abbrev Root (G:Gauge) (n:Side) := Away n→G.Color
abbrev Rep (G:Gauge) (n:Side) := OEdge n→G.Color
local notation "T" => Site n
local notation "L" => Edge T
local notation "V" => Rep G n
local notation "R" => Root G n
local notation "Z" => Pert.Orb.Parameter G n
local notation "U" => Pert.Orb.Potential G n

/-- Evaluate a rooted log-gauge at a site. -/
def atSite (p:T) : Root G n→ₗ[ℝ] G.Color := if h:vertex p ≠ 0 then LinearMap.proj ⟨vertex p, vertex_vertex _,h⟩ else 0
lemma atSite_eq (i : Away n)(p:R) : atSite i.val p=p i:= by unfold atSite; simp [i.property.1,i.property.2]
lemma site_neg (p:T) : atSite (G:=G) (-p)=atSite p:= by unfold atSite; simp
@[simp] lemma site_central : atSite (G:=G) (0:T)=0:= by simp [atSite]
@[simp] lemma at_cent (p:R) : atSite (0:T) p=0:= by rw [site_central]; rfl
lemma roots_even (p : Z)(x : T) : p.val (-x) = p.val x := (show _ ∧ _ from p.property).1 x

def gaugeAngles (G:Gauge)(n:Side) : Root G n ≃ₗ[ℝ] Pert.Orb.Parameter G n where
  __ := (LinearMap.pi (atSite (G:=G) (n:=n))).codRestrict (Pert.Orb.Zero G n) (fun p=>by
    refine ⟨fun x=>?_,?_⟩
    · simp [site_neg]
    exact at_cent p)
  invFun p i := p.val i.val
  left_inv p := funext fun i=> atSite_eq i p
  right_inv p := Subtype.ext (funext (fun x=> by
    change atSite x (fun i : Away _=> p.val i.val)=_
    unfold atSite
    split
    · apply (show p.val (vertex x) = _ from ?_); rcases vertex_spec x with e|e <;> simp [e,roots_even]
    next hx => have h := vertex_eq_iff.mp (not_ne_iff.mp hx); subst x; exact (Pert.Orb.atZ p).symm))
lemma angles_eq (p:R)(x:T) : (gaugeAngles G n p).val x = atSite x p:= rfl

-- links.
def touches (G:Gauge)(n:Side) : Pert.Orb.Potential G n →ₗ[ℝ] Rep G n :=
  (LinearMap.pi fun i: OEdge n=> LinearMap.proj i.val).comp (Pert.Orb.LinkP G n).subtype
lemma touch_eq (p:U)(i:OEdge n) : touches G n p i=p.val i.val:=rfl
lemma reflection : reflect (n:=n) = Pert.Orb.image := rfl
lemma reflect_at (p:U)(l:L) : p.val (reflect l)= -p.val l := p.property l
lemma read_link (p:U)(l:L) : p.val l = if eR l=l then p.val (eR l) else -(p.val (eR l)):= by
  split
  next h=> rw [h]
  next h=> rw [(eR_spec l).resolve_left h, reflect_at, neg_neg]
lemma rep_inj : Injective (touches G n) := by
  intro p q H; apply Subtype.ext; funext x; rw [read_link p x,read_link q x, show p.val (eR x) = q.val (eR x) from congr_fun H (index x)]

/-- Linear extension of all rep logs; Even is used precisely here. -/
def fan (e:Even n.val)(p:V) : U :=
 ⟨fun i=>if eR i=i then p (index i) else -p (index i), fun i=>by
   change (if eR (reflect i)=reflect i then _ else _)= _
   have hz:=no_fixed_edge e i
   dsimp only; unfold Pert.Orb.image; rw [show (-i.1-step i.2,i.2)=reflect i from rfl, eR_reflect, show index (reflect i)= index i from Subtype.ext (eR_reflect i)]
   rcases eR_spec i with h|h <;> simp only [h,hz,hz.symm,neg_neg,↓reduceIte]⟩
lemma read_fan (e:Even n.val)(p:V) : touches G n (fan e p)=p:= by funext i; rw [touch_eq]; change (if eR i.val=i.val then p (index i.val) else _) = _; rw [if_pos i.property]; rw [show index i.val=i from Subtype.ext i.property]
def fanEquiv (e:Even n.val) : U≃ₗ[ℝ]V := LinearEquiv.ofBijective (touches G n) ⟨rep_inj,fun p=> ⟨fan e p,read_fan e p⟩⟩
lemma touchesE (e:Even n.val)(p:U) : fanEquiv e p= touches G n p:= rfl
lemma turned (e:Even n.val)(p:V) : (fanEquiv (G:=G) e).symm p=fan e p:= (fanEquiv e).injective ((LinearEquiv.apply_symm_apply ..).trans (read_fan e p).symm)

/-- Extend representative logs to config. -/
def ignite (p:V) : Wilson.Config G n := liftLinks (G.lieExp ∘ p)
lemma lit (p:U) : ignite (touches G n p)=Pert.Orb.positiveLinks p:= by
  funext i
  unfold ignite liftLinks
  change (if _ then G.lieExp (p.val (eR i)) else _) = G.lieExp (p.val i)
  split
  next h=> rw [h]
  next h=> rw [(show p.val i= -p.val (eR i) from (read_link p i).trans (if_neg h)),YM.Next.SectorChange.exp_negative]; rfl
end YM.FVA2.Orbit
