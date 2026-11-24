import YM.AlbaMS.Barr.Pedal
/-!
# Root comparisons between two Canonical Tune. apply normalized Ward

Atlas all horizons/logs, not altering measure/hyp. Care after selecting
Gauge (based group). No need kernel restrictions at contacts for this equation,
requires quantum closure of product U, includes necessary exact columns.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Barr.Salute
open Set Function Filter IsNilpotent Matrix
open scoped BigOperators Classical Topology Matrix InnerProductSpace ENNReal
open Nexus Bric Coil Loft Inlay Inlay.Net Tune Odom Cutis Cutis.Winter Lattice
variable {K D E B:Type*}[Fintype K][AddCommMonoid D]{ρ:Ladder K D}{Ω :Net E B}{G:Gauge}[DecidableEq E][DecidableEq B][Fintype E][Fintype B]
variable {T P:Tune  (Tags ρ ℝ)}(F:Odom.Book Ω G)(he:Idle P)
variable (A:Fritz (Flit G E) (Flit G B)  (Tags ρ ℝ)) (U:Heave G E B  (Tags ρ ℝ))
include he in
theorem baseInd (ha:A.Normal (planeBook P F)) (ht:Idle T)(h:Still P T)
    (X:Fritz (Flit G E) (Flit G B)  (Tags ρ ℝ))(H:X.Fund (planeBook T F))(hh:FinRank U)(hu:EvenT U)(H':quantum P.bracket Finset.univ (F.charter P) U=0):
    bouquet F A P U= bouquet F X T ((weft (lane P T)) U):=by
  obtain ⟨S,hs,hS,hq⟩:=Fritz.classifies (legal P F (he.feel P F) (he.nul P)) ha (isRoot P) (he.funded P F A.hop) hh hu (by rw [bridge];exact H');
  have hl : FinRank (weft (lane P T) U):=⟨_,hh.choose_spec.weft _⟩
  have hvS : FinRank (weft (lane P T) S):=⟨_,hs.choose_spec.weft _⟩; have hqS := hS.weft (lane P T)
  symm; apply Fritz.classify_leads (legal T F (ht.feel T F) (ht.nul T)) H (ht.funded T F X.hop) _ _ hl hvS hqS
  rw [bridge, ← h.guide, ← bridge, ← hq]; rw [map_sub,map_smul,one_on]; rfl -- sign
section orbit
variable {n:Side}{u:Precision.ChartRatio G}(hp:Precision.LocalRatio u) {Y:Heave G (Arm n) (Vtx n)  (Tags ρ ℝ)}
-- global full thin / path interpolation. inspection at Compact kernels.
noncomputable def wrapped (T:Tune  (Tags ρ ℝ))(Y : LightQ G n  (Tags ρ ℝ)):= Fritz.levy (Element T G n).hop (Area T hp n) Y
lemma measured (h:Even n.val)(hU:Cutis.Winter.Moves P Y)(he: Idle P)(hr: FinRank Y):
    wrapped hp P Y= Salute.standard P hp (Owner P Y):=by
  unfold wrapped Salute.standard bouquet Fritz.levy
  have ht : Fritz.play (Element P G n).hop (Area P hp n) Y = CovRay P hp (Owner P Y):= fireCover P hp h Y hU hr (he.nul P) (he.feel ..) -- h args
  have hw : Fritz.gig (Element P G n).hop (Area P hp n)=Fritz.gig (drive (G:=G) (n:=n) P).hop ((Root G u n true hp).stim P):=by
    have hu (p:Wire (Flit G (Arm n)) (Flit G (Vtx n)) (Env G n) (Sand G n)  (Tags ρ ℝ)): p.firm 1=1:= shot_put .. -- unused i
    apply Eq.trans (b:=CovRay P hp (Owner P 1)) (fireCover P hp h 1 (by unfold Winter.Moves; rw [hu,hu]) FinRank.one (he.nul P) (he.feel ..))
    rw [show (Owner P 1:Heave G _ _ _)=1 from shot_put ..]; rfl
  rw [hw,ht]; rfl
lemma identification (h:Even n.val)(hs: Idle T)(F:Fritz (Env G n) (Sand G n) (Tags ρ ℝ))(hf : F.Fund (locate T hp))(Y:Heave G (Foil n) (Nail n true) (Tags ρ ℝ))(hr:FinRank Y)(hv:EvenT Y)(hq:quantum T.bracket Finset.univ ((Root G u n true hp).charter T) Y=0):
    Salute.standard T hp Y=bouquet (Root G u n true hp) F T Y:=by
  let B:=Root G u n true hp; unfold Salute.standard bouquet;
  have hc: F.Fund (planeBook T B):=hf
  apply Eq.symm; apply Fritz.gauge_neutral (legal T B (hs.feel T B) (hs.nul T)) (isRoot T) hc (Rosetta hp h T) hv hr; rw [bridge];exact hq
end orbit
end YM.MSBar.Barr.Salute
