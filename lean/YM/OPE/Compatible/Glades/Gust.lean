import YM.OPE.Compatible.Glades.Huddle
/-! Preserve births exactly reaping, not identifying the projection or
pruning physical fields. -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.ManyCopies
open Function Filter Lattice RG Wilson MergeProof Source Accent Spec Ribbons
open Push Marker Local Extra.Histories Extra.Trajectories MeasureTheory Extra.Multi Finset
open Ribbon Mirror MeasureTheory
open scoped Topology Classical
variable {X V I J W:Type}[Fintype V][DecidableEq V][Fintype I][DecidableEq I][Fintype J][DecidableEq J] [Fintype W][DecidableEq W]
   {G:Gauge} {A:History G}{N n p m:ℕ}
-- if blanks none old contents allowed choose Fibers with surj
variable (F : Fibers (I⊕W) J) (S:Fibers I J)(hF:∀ i,F.bunch (Sum.inl i)= S.bunch i)
include hF
lemma same_group (x:(Names V J).Mode): assembly F x=(partialGroup V S).plena x:=by
   apply Subtype.ext; ext j; rw [assembly,low_read,Fibers.reaped,Fibers.reaped]; change (_,F.bunch (.inl j.snd))∈ x.val ↔ (_,S.bunch j.snd)∈x.val; rw [hF]; rfl
private lemma wingy {n:Side}{M:Rep G n}{y:V×I→ Config G n→ℂ}:
   reunion F ∘ birth (Names V I) M y=birth (Names V J) M (fun j U => ∏ i ∈ S.contents j.2, y (j.1,i) U):=by
   funext U; ext s; change ((birth (Names V I) M y) U).part (assembly F s)=((birth (Names V J) M _) U).part s; rw [same_group F S hF]; unfold birth Mach; simp only [Poly.part_smul, pass_fire]; congr 1; rw [Fibers.prod_plena]; refine Finset.prod_congr rfl fun j _=>?_ ; rcases j with ⟨j,i⟩; rw [contentP, Finset.prod_image]; exact fun _ _ _ _ h=>Prod.mk.inj h|>.2
lemma reuni_gust {y:V×I→ Config G (A.S.side N p)→ℂ}
    (h:Integrable (birth (Names V I) (A.rep N p N) y) (prior G _)) (hm:m ≤ N):
    Integrable (birth (Names V J) (A.rep N p N) (fun j U=> ∏ i∈ S.contents j.2, y (j.1,i) U)) (prior G _)∧
    reunion F ∘ gust A N p N (birth (Names V I) (A.rep N p N) y) m hm= gust A N p N (birth (Names V J) (A.rep N p N) (fun j U=> ∏ i∈ S.contents j.2, y (j.1,i) U)) m hm:=by
    constructor; · rw [← wingy F S hF]; exact out_live F h
    induction hm using Nat.decreasingInduction with
    | self=> rw [gust_base, gust_base, wingy F S hF]
    | of_succ i hi ih=> rw [gust_step _ _ _ _ _ hi, gust_step _ _ _ _ _ hi, consumes F _ (A.levels.transition_mass ..) (gust_live A _ _ _ _ h _), ih]
omit hF
lemma drifting (X:Config G (A.S.side N p) → Marker.Poly (Bud V))(hn:n ≤ N)(hk:m ≤ n):
    gust A N p n (gust A N p N X n hn) m hk=gust A N p N X m (hk.trans hn):=by
    induction hk using Nat.decreasingInduction with
    | self=> rw [gust_base]
    | of_succ i hi ih=> rw [gust_step _ _ _ _ _ hi, gust_step _ _ _ N X (lt_of_lt_of_le hi hn), ih]
lemma all_prod (y:I→ℂ) : ∏ i,y i = ∏ v,∏ i∈ S.contents v,y i :=by
    let b:(Bud J).Mode:= ⟨univ, mem_univ _⟩; rw [show ∏ v,∏ i∈ S.contents v,y i= ∏ v∈b.val,∏ i∈ S.contents v,y i from rfl,← S.prod_plena]; exact prod_congr (eq_univ_of_forall (fun i=>(S.reaped ..).2 (mem_univ _))).symm (fun _ _=>rfl)
end YM.MergeProof.Ribbons.ManyCopies
