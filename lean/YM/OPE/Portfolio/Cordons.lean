import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Trails
import YM.OPE.Portfolio.Horizon
/-!
# Clock: deterministic branch overheads (initial joint law)

Keep integrability on WHOLE literal polynomial all the way. Can project pressure
monomials repeatedly as needed; no assertions on forbidden monomials in those projections.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.ManyCopies.Cadet
open Function Filter Finset Lattice RG Wilson Pressure MeasureTheory
open Push Marker Accent Menu Extra.Multi Extra.Trajectories Ribbon Source Local
open Extra.Histories PhysicalNext.Repeat Lotus GridApprox.Nil OPE.Backup Motion
open Muster MergeProof.Float
open scoped Topology BigOperators Classical
variable {V : Type}[Fintype V][DecidableEq V]{G:Gauge}{H:History G}{N p m i b:ℕ}
set_option quotPrecheck false
variable (L:Playout H p m N V){I J:Type}[Fintype I][DecidableEq I][Fintype J][DecidableEq J]
namespace Playout
-- gather
local notation "K0"=> H.rep N p i
local notation "V0"=> (H.levels.budget i)
variable {r:ℕ→ℕ}{u:I→Site (H.S.side i p)}{s:Ward (Names V I)}{s':Ward (Names V J)}{W W':I→ℝ}{δ ψ φ:ℕ→ℝ}
    {A:∀ N p m:ℕ,m<N→GaugeDoor (H.rep N p (m+1)) (H.rep N p m)}
variable (h:H.Selected)(ht:Thor H δ r A ψ φ b) (X:Fibers I J) {q:Config G (H.S.side i p)→Poly (Names V I)}{f:I→ Cup (H.rep N p i)}{z:Finset J} {T l:ℕ}{C:I→ℂ}
local notation "τ"=> (partialGroup V X).twig
local notation "V1"=> L.primary
include h ht
lemma ArcMarket.integrate (hi:b ≤ i)(hl:m ≤ i)(hn:i<N)(hQ:ClusterPars H δ φ r i)(hV:Arsenal K0)(hh:L.ArcMarket s u f q W (δ i) (φ i) C)
    (hs:∀ i ∈ z,X.Solo i) (ht0:0<T)(hT:Fintype.card I ≤ T)(ho:L.occupied (r i) u)(hp:∀ j:I,coverNumber (H.levels.budget i).B ({u (X.twig (X.bunch j)),u j}:Support _) ≤ l) (hy:∀ j:(Names V J).Mode,s'.ready j→ s.ready ((partialGroup V X).plena j)) : ∃ F:J→ Cup (H.rep N p i),
       L.Market s' (u ∘ X.twig) F (fun U=> Fibers.reap (partialGroup V X) (q U)) (grouped H δ T l i W X) ((V0).supportExponent-2) ∧ (∀ j,j∉z→ Blade K0 (u (X.twig j)) (F j).home (F j).leaves 0 (4*(1/grouped H δ T l i W X j))) ∧ ∀ j∈ z,F j=f (X.twig j):=by
    obtain ⟨k,hk,hY⟩:= hh.tall; let o:=L.spectrum i u; let Q':= partialGroup V X
    have hm:=ht.suns i hi; have hg:Occupancy (o ∘ τ) (r i):=by
       intro y; let f:=univ.filter (fun i=>(o ∘ τ) i=y); have hs: f.image τ ⊆ univ.filter fun i=>o i=y:=by
          intro i hi; obtain ⟨j,hj,rfl⟩:= mem_image.mp hi; exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hj).2⟩
       exact (le_of_eq (Finset.card_image_of_injective f Q'.sectioned.injective).symm).trans ((Finset.card_le_card hs).trans (ho y))
    have h_: ∀ j:V×I,δ i*W j.2*‖L.skater C j‖ ≤ 1:=by
       intro j; unfold skater; rw [norm_scalar]; exact (mul_le_mul_of_nonneg_right (mul_le_of_le_one_left (hh.width j.snd|>.le) hm.hats.2) (norm_nonneg _)).trans (hh.pepper _)
    have hp':∀ j:V×I, coverNumber (V0).B ({ (L.spectrum i u ∘ τ) ((partialGroup V X).bunch j), L.spectrum i u j}:Support _) ≤ l:=by
      intro j; let x:=X.twig (X.bunch j.snd); let Q:= L.tint j.fst; let v:= L.positions i j.fst
      have ht: ({ (L.spectrum i u ∘ τ) ((partialGroup V X).bunch j),L.spectrum i u j}:Support _)= sky Q v ({u x,u j.snd}:Support _):=by rw [shading,Finset.image_insert,image_singleton]; rfl -- check namespace
      rw [ht]; exact le_trans (le_of_eq (by rw [shading]; exact ProjectorNext.Equivariance.moves_cost Q.1 v _ _)) (hp _)
    obtain ⟨F',K',hr,hH,hF,hX,hE⟩:= buccGather q h ht X z hs hi hn hY (hk ▸ (L.rebind f C hl hn.le)) (fun j _ k=> L.roster u hl hn.le j k) hQ hh.width hV ht0 hT ho hg h_ hp' hy
    let F(j):= Cup.book K0 (F' (V1,j)) (K' (V1,j)) (hF _); have ha: L.cupsReg i F=F':=by
       funext j; obtain ⟨j,b⟩:=j; by_cases hx:j=V1; · rw [hx,L.attended F hl hn.le]; rfl
       exact ((hH j hx).2 b).1.symm
    have hb: L.cupsRes i F=fun j=> profile (K0).activities (K' j):=by
       funext j; obtain ⟨j,b⟩:=j; by_cases hx:j=V1; · rw [hx,L.fleur F hl hn.le]; rfl
       exact ((hH j hx).2 b).2.1.symm
    refine ⟨F, ⟨grouped_pos T l X hm.hats.1 ht0 hh.width,?_⟩,fun j hj=>?_,fun j hj=>?_⟩
    · rw [ha,hb]; exact hr
    · have hz:= hX (V1,j) hj; rw [show L.spectrum i u (τ (V1,j)) = u _ from L.principal u hl hn.le _] at hz; exact hz -- .comp?
    apply Cup.same ?_ ?_
    · exact (hE (V1,j) hj).1.trans (L.attended f hl hn.le _)
    have hk': (F j).leaves = _ := congr_arg (profile (K0).activities) (hE (V1,j) hj).2; exact hk'.trans ((congr_fun hk.symm _).trans (L.fleur f hl hn.le _))
end Playout
end YM.MergeProof.Ribbons.ManyCopies.Cadet
