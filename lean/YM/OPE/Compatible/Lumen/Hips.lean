import YM.OPE.Compatible.Lumen.Bud
/-!
# Boost gauge charge, using product | | of color. Left exact inverse up to torus scalar Pin.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade.Glass
open Function Filter Set Lattice Laurent Tree Woody Weir MeasureTheory Exterior Bloch Score Libra Votive Matrix
open scoped Topology BigOperators ComplexConjugate Classical ContDiff Matrix.Norms.Frobenius RealInnerProductSpace
variable {G:Gauge}{n:Side}
open RG Bid Pressure Precision FreeResolvent WithLp Next.Free Frequency Streamer Terp
open PertExtension Series Asymptotics MSbar.Tree MSbar.Tree.Resolvent
attribute [local instance] Gauge.frobInner
variable (H: Even n.val)
local notation "TK" => Keys G (Limb H)
local notation "VK" => Keys G (Node H)
-- energy exactly normalized. site divergence map π.
def bedLoad (v:VK)(i:G.ColorIndex): form 0 n:=fun p=> v (crumb H p.1) i
lemma galaxyTilt (v:VK)(i:G.ColorIndex): parts G _ (cloak H ((Pond H).galaxy G v)) i= -(grad n*ᵥ bedLoad H v i):=by
    ext p; obtain ⟨p,rfl⟩:=addressR.surjective p
    have he:= descends H p; have hv:=finale H p; change (cloak H ((Pond H).galaxy G v) (p.1,Exterior.coord p.2)) _= -(d 0 n*ᵥ _) (p.1, Exterior.coord p.2); rw [cloak_at,d_sites,Prod.mk.eta]; unfold hover bedLoad; simp only; rw [he,hv]; split
    next h=> rfl
    next h=> change ((v _-v _) i)= _ ; simp only [neg_sub, PiLp.sub_apply]; rfl
-- divergence. invariance of frame: acts.
def rinse : TK→ₗ[ℝ] VK where
    toFun x p:= toLp 2 fun i=> ((grad n)ᵀ*ᵥ parts G _ (cloak H x) i) (p.val,Exterior.vac)
    map_add' u v:=by ext i j; simp only [Pi.add_apply,PiLp.add_apply]; rw [show parts G 1 _ _= _ from (flightPart H j).map_add u v, Matrix.mulVec_add];rfl -- notation
    map_smul' c u:=by ext i j; simp only [Pi.smul_apply,PiLp.smul_apply]; change ((grad n)ᵀ*ᵥ flightPart H j (c • u)) _= _;rw [map_smul,mulVec_smul];rfl
lemma deployed (x:TK)(i:G.ColorIndex): bedLoad H (rinse H x) i= (grad n)ᵀ*ᵥ parts G _ (cloak H x) i:=by
    let v:= parts G 1 (cloak H x) i; have he(k:Kv): stem k v=v:=(StemClip _).mpr (EllK H i x) k
    ext p; rcases p with ⟨x,j⟩
    obtain ⟨k,hx⟩:= (sitesK H).joint x; have ht:=adjG H k v; rw [he] at ht; let M:= crumb H x; change decks k M.val=x at hx; change ((grad n)ᵀ*ᵥ v) (M.val,Exterior.vac)=((grad n)ᵀ*ᵥ v) (x,j); rw [show j=Exterior.vac from vac_only j]; rw [← hx]; exact congr_fun ht _ -- issue M
lemma entered (u v:VK)(i:G.ColorIndex): bedLoad H u i ⬝ᵥ bedLoad H v i= 4*(∑ p:Node H, u p i*v p i):=by
      let f(x:Site n):= u (crumb H x) i * v (crumb H x) i
      calc
            _ = ∑ j:Site n,f j:=by unfold bedLoad dotProduct; rw [Fintype.sum_prod_type]; apply Finset.sum_congr rfl;intro i _; rw [Finset.sum_eq_single (Exterior.vac)]
                                   · intro b _ hb;exact (hb (vac_only b)).elim
                                   simp
            _=4 • ∑ j:Node H,f j.val:=by convert! (sitesK H).sumRep f (fun j k=> by unfold f; rw [show crumb H _=_ from (sitesK H).king_go k j]) using 1; congr!
            _=_:=by simp_rw [f,show ∀ p:Node H,crumb H p.val=p from fun p=> (sitesK H).king_here _]; simp
lemma galaxyDot (u:TK)(v:VK)(i:G.ColorIndex) : parts G _ (cloak H ((Pond H).galaxy G v)) i ⬝ᵥ parts G _ (cloak H u) i= -(4*(∑ p:Node H,v p i* rinse H u p i)):=by
      rw [galaxyTilt H,neg_dotProduct,← dotProduct_comm (parts G _ (cloak H u) i),← dotProduct_transpose_mulVec,← deployed,entered]
-- expose sum orth
lemma cover_in (S T:TK)(i:G.ColorIndex): parts G _ (cloak H S) i ⬝ᵥ parts G _ (cloak H T) i=4*(∑ j:Limb H,S j i* T j i):=by
     -- sums signed
     let x:= flightPart H i S; let y:= flightPart H i T; let f(p:edgeV n):ℝ:= loadV x p*loadV y p
     change x ⬝ᵥ y = _
     have hz(k:Kv)(p:edgeV n): f p=f (ferry k p):=by unfold f; rw [show loadV x p=_ from EllK H i S k p, show loadV y p=_ from EllK H i T k p]; split; simp; rfl;rfl
     have he:(∑ p,f p)=4 • ∑ p:Limb H,f p.val:=by convert! (edgesK H).sumRep f (fun j k=>(hz k j).symm) using 1; congr!
     rw [show x ⬝ᵥ y=∑ p,f p from (Equiv.sum_comp addressR _).symm,he]; simp_rw [show ∀ p:Limb H,f p.val=S p i*T p i from fun p=> by
            have ht(X:TK):loadV (parts G _ (cloak H X) i) p.val=X p i:=by unfold loadV Exterior.parts;dsimp only;rw [cloak_at,Prod.mk.eta,hover_reap]
            exact congr_arg₂ (·*·) (ht S) (ht T)]; simp
lemma toneG (u v:G.Color): inner ℝ u v=∑ i:G.ColorIndex,u i*v i:=by rw [PiLp.inner_apply]; apply Finset.sum_congr rfl; intro i _;rw [real_inner_comm]; rfl
lemma rainbook (S T:TK) : ∑ i:G.ColorIndex, ((grad n)ᵀ*ᵥ parts G _ (cloak H S) i) ⬝ᵥ ((grad n)ᵀ*ᵥ parts G _ (cloak H T) i)=4*(∑ p:Node H,inner ℝ (rinse H S p) (rinse H T p)):=by
      simp_rw [← deployed, entered, ← Finset.mul_sum]; congr 1; rw [Finset.sum_comm]; exact Finset.sum_congr rfl (fun i _=>by exact (toneG ..).symm)
lemma tideDown (S:TK)(v:VK): (∑ i:Limb H,inner ℝ ((Pond H).galaxy G v i) (S i))= -(∑ i:Node H,inner ℝ (v i) (rinse H S i)):=by
     have hp(i): (∑ j:Limb H, (Pond H).galaxy G v j i * S j i) = -(∑ j:Node H,v j i*rinse H S j i) :=by have he:= galaxyDot H S v i; rw [cover_in] at he; linarith only [he]
     simp_rw [toneG]; rw [Finset.sum_comm]; simp_rw [hp]; rw [Finset.sum_neg_distrib]; congr 1; exact Finset.sum_comm
end YM.OPE.Cascade.Glass
