import YM.RG05Readout.Capture.Fronds
/-!
# Budget a complete-polynomial real coarse path on a fixed card

Real R-only. Permit perturbatively UNAFFORDABLE growth: e^O(Lambda_m^2) on close windows
is intended. All priced on leases on real R. Geometry funded right before taking one root
reading along exact m Life. Outputs must keep their pre-alignment Paint on the LAST step!
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Petra
open Function Filter Set Lattice Wilson RG Source Extra.Histories Push Local
open Planned.GuardedAtom Guard MergeProof Accent Menu Marker Address Native View Bid Pressure Copper
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage Next.Rank.Station
open Ribbons Ribbons.Fibers Ribbons.ManyCopies Many
open MeasureTheory
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G} {n m p N d b i c:ℕ}{V W:Type}[DecidableEq V][Fintype V]
    {D:Address.Rail C} {w:Worth}{r:ℕ→ℕ} {B:Census V}
set_option quotPrecheck false
local notation "S0"=> C.path.levels
local notation "K"=> C.path.levels.clock
local notation "Y"=> C.path.rep N p
local notation "X"=> C.path
local notation "Ζ"=> C.path.levels.budget
local notation "u"=> Legato.Bandage.renal C.path.levels
local notation "Δ!"=> C.path.levels.clock.op
local notation "P!"=> C.side
local notation "ℓ"=> Copper.ld C.path.levels
abbrev Series (C:Family G)(p m:ℕ)(B:Census V):=Config G (C.side m p)→Poly B
structure Cutting (C:Family G)(o:V→Site (C.side i p))(P:Series C p i B)(T:V→Three G (C.side i p))(N:ℕ)(J e:ℝ):Prop where
    price : 0 < J
    plate : MenuBoard (C.path.rep N p i) T P o (fun _=>J) e 1
    cap (j:V) : ∃ t:ℂ, ‖t‖≤ 1/(2*J) ∧ MergeProof.Float.Blade (C.path.rep N p i) (o j) (T j).2.1 (profile ((C.path.rep N p i).activities) (T j).2.2) t (1/(2*J)) -- + secret scalar.S.Named.E
variable (h:C.Makes) (L:OPE.Package C w r D) (he:Cater C D)
variable {J e:ℝ}{o:V→Site (C.side (i+1) p)}{P: Series C p (i+1) B}{T:V→ Three G (C.side (i+1) p)}
local notation "δ"=> (C.path.levels.clock.op i p)
local notation "η"=> (C.S.block i).val
local notation "B₁"=>1/(2*J)
local notation "D₁"=> (Y (i+1))
include L h
open MergeProof.Float
abbrev occupancy (o:V→Site (C.side (i+1) p))(d:ℕ):=Occupancy o d ∧ Occupancy ((Δ! i p).ratio.parent ∘ o) d
private lemma scanning (hc:C.ref 0 ≤ i)(hm:i<N){z:V} (hp:Cutting C o P T N J e) : let b':= (δ).ratio.parent (o z)
    ∃ (U:Three G (C.side i p))(v:ℂ), ‖v‖ ≤ B₁∧ Ride δ (o z) b' (D N p i hm) 1 (T z) U B₁ ∧ MergeProof.Float.Blade (Y i) b' U.2.1 (profile ((Y i).activities) U.2.2) v (6*η*B₁):=by -- notation binder precedence.
    intro b'; have h1:=h.wilson.represents N p (i+1) hm; have h2:= h.wilson.represents N p i hm.le
    obtain ⟨v,hv,hV⟩:=hp.cap z; let q:= T z; have hU:=hp.plate.fettled z
    let x:= Y i; have hd:= (S0).transition_mass i p ((Y (i+1)).beta)
    have hL:= L.productCuts.mother.choose_spec 0; obtain ⟨f,k,hB,hK,hC,hχ⟩:= MergeProof.Float.slosh hV h1.good hU.normK (hL.brings i hc N p hm|>.1) (by positivity) h2.good.labels (h.wilson.steps N p i hm|>.1|>.symm) hd
    let C' := coin x f k
    refine ⟨(C',f,k),v,hv,⟨hU, ⟨hK,rfl,spill_in hB h2.good hK⟩, ?_,?_⟩, hB⟩
    · obtain ⟨s,hs,hS⟩:=hC; exact ⟨s,hs,v,hv,hS.climb le_rfl le_rfl ((norm_nonneg _).trans hv)⟩
    change coin (Y i) f k = _; rw [one_smul,← hχ,hU.read]
local notation "Z!"=> apron (S0)
local notation "Ω"=> (δ).ratio.parent ∘ o
local notation "P'"=> (δ).push (Y (i+1)|>.beta) P
-- craft arbitrary.I
lemma pick (hc:C.ref 0 ≤ i)(hm:i<N)(hp:Cutting C o P T N J e):∃ (U: V → Three G (C.side i p)), ∀ j:V,∃ v:ℂ, ‖v‖ ≤ B₁∧ Ride δ (o j) (Ω j) (D N p i hm) 1 (T j) (U j) B₁∧ MergeProof.Float.Blade (Y i) (Ω j) (U j).2.1 (profile ((Y i).activities) (U j).2.2) v (6*(η:ℝ)* (1/(2*J))):=by
    choose Q v H using (fun z:V=> scanning h L (z:=z) hc hm hp); exact ⟨Q,fun i=>⟨v i,H i⟩⟩
-- schedule ∆:  ξ paid at each step.J replaced by shrink with floor L.
def wet (C:Family G)(i:ℕ):ℝ:= renal C.path.levels i/(6*(C.S.block i).val)
local notation "J1"=>wet C i*J
include he
lemma heave (hc:C.ref 0 ≤ i)(hm:i<N)(hp:Cutting C o P T N J e)(hx: (Ζ (i+1)).supportExponent-4≤ e) (hX:occupancy (C:=C) (p:=p) (i:=i) o (Z! i)) : ∃ (t:ℝ)(U:V→ Three G (C.side i p)), Furls (S0) i t∧ Alcove (Y i) U P' Ω (fun _=> u i*J) t (u i) (1/2) ∧ Cutting C Ω P' U N J1 ((Ζ i).supportExponent):=by
   obtain ⟨a,b,hL,hA,hB⟩:=he.tiers i N p hm; obtain ⟨U,hu⟩:= pick h L hc hm hp
   have hJ := hp.price; have h_u:= hL.poses.hats.1; have ht:0<(η:ℝ):= by exact_mod_cast (C.S.block i).property
   have h6:1 ≤ 6*(η:ℝ):=by
       have H:1 ≤ (η:ℝ):= by exact_mod_cast (C.S.block i).property
       linarith only [H]
   have hv:0< J1:=mul_pos (div_pos h_u (by positivity)) hJ
   have he : ∀ j:V, Ride δ (o j) (Ω j) (D N p i hm) 1 (T j) (U j) (1/(2*J)):= fun j=> (hu j).choose_spec.2.1
   have hW : (fun j:V=> (1:ℂ)⁻¹ • U j)=U:=by simp
   have hy: ∀ _:V, 2*J*(1/(2*J)) ≤ 1:=fun _=>le_of_eq (by field_simp)
   have h_F := hL.plates h.wilson hm hp.plate hx (fun _=>by simp) (fun _=>hJ) he hX.1 hX.2 hy
   rw [hW] at h_F; have hF:=hL.send h.wilson hm hp.plate hx (fun _=>by simp) (fun _=>hJ) he hX.1 hX.2 hy (fun _=>hv)
   have hg:Repegs Ω (Ζ i|>.B) (fun _=>u i*J) (fun _=>J1) (1/2) 1 B:=by
       intro k _ p _; rw [one_mul]; unfold Poly.toll; refine (Finset.prod_le_prod (fun i _=>hv.le) fun i' _=> mul_le_mul_of_nonneg_right (div_le_self h_u.le h6) hJ.le).trans (le_mul_of_one_le_right (Finset.prod_nonneg (fun _ _=>?pos)) (Real.one_le_exp (by positivity))); exact mul_nonneg h_u.le hJ.le
   have hb: 0≤b:=by
       obtain ⟨F,K',ψ,ν',_,⟨t,H,Y',H'⟩,_⟩:=h_F.chamber; exact (tsum_nonneg ((Y' 0).1)).trans (Y' 0).2.2
   refine ⟨b,U,⟨hb,h_u,hL.poses.hats.2,hL.poses.exp.1,hL.poses.stakes.1,hA,hB⟩,h_F, hv,hW ▸ hF hg,fun j=>?_⟩
   obtain ⟨v,ht',hq,hY⟩:=hu j
   have hz: (6*(η:ℝ))*(1/(2*J)) ≤ 1/(2*J1):=by
       rw [le_div_iff₀ (show 0 < 2*J1 by positivity)]; refine le_trans (b:=u i) (le_of_eq ?_) hL.poses.hats.2; unfold wet; field_simp
   exact ⟨_,ht'.trans ((le_mul_of_one_le_left (by positivity) h6).trans hz), hY.more hz⟩
end YM.RG05Readout.Petra
